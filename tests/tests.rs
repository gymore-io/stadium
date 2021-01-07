use std::cell::Cell;
use std::mem::ManuallyDrop;
use std::rc::Rc;

/// A simple structure that adds one to its inner counter when it gets dropped.
pub struct DropCounter(ManuallyDrop<Rc<Cell<usize>>>);
impl Drop for DropCounter {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 1);

        unsafe { ManuallyDrop::drop(&mut self.0) };
        // must not use the arc after this point
    }
}

#[test]
fn build_with_no_objects() {
    stadium::builder().build();
}

#[test]
fn build_with_one_object() {
    let mut b = stadium::builder();
    let handle = b.insert(996633u32);
    let s = b.build();
    assert_eq!(s.get(handle), &996633u32);
}

#[test]
fn build_with_300_objects() {
    let mut b = stadium::builder();
    let mut handles_u16 = Vec::with_capacity(100);
    let mut handles_u32 = Vec::with_capacity(100);
    let mut handles_u64 = Vec::with_capacity(100);

    for i in 0usize..300 {
        match i % 3 {
            0 => handles_u16.push(b.insert(i as u16)),
            1 => handles_u32.push(b.insert(i as u32)),
            2 => handles_u64.push(b.insert(i as u64)),
            _ => unreachable!(),
        }
    }

    let s = b.build();

    for (i, h) in handles_u16.into_iter().enumerate() {
        assert_eq!(*s.get(h), i as u16 * 3);
    }

    for (i, h) in handles_u32.into_iter().enumerate() {
        assert_eq!(*s.get(h), i as u32 * 3 + 1);
    }

    for (i, h) in handles_u64.into_iter().enumerate() {
        assert_eq!(*s.get(h), i as u64 * 3 + 2);
    }
}

#[test]
fn zero_sized_type_insert() {
    let mut b = stadium::builder();
    b.insert(());
}

#[test]
fn zero_sized_type_insert_raw() {
    let meta = stadium::ObjectMeta::of::<()>();
    let mut b = stadium::builder();
    b.insert_raw(meta);
}

#[test]
fn handle_is_associated_with_stadium() {
    let mut b_1 = stadium::builder();
    let mut b_2 = stadium::builder();
    let h_1 = b_1.insert(0u8);
    let h_2 = b_2.insert(0u8);
    let s_1 = b_1.build();
    let s_2 = b_2.build();

    assert_eq!(s_1.is_associated_with(h_1), true);
    assert_eq!(s_1.is_associated_with(h_2), false);
    assert_eq!(s_2.is_associated_with(h_1), false);
    assert_eq!(s_2.is_associated_with(h_2), true);
}

#[test]
fn replace_value_in_stadium() {
    let mut b = stadium::builder();
    let h = b.insert("Hello");
    let mut s = b.build();

    assert_eq!(s.replace(h, "World"), "Hello");
    assert_eq!(*s.get(h), "World");
}

#[test]
fn get_mut_values_from_stadium() {
    let mut b = stadium::builder();
    let h = b.insert(vec![0, 1, 2]);
    let mut s = b.build();

    assert_eq!(s.get(h), &[0, 1, 2][..]);
    s.get_mut(h).push(3);
    assert_eq!(s.get(h), &[0, 1, 2, 3][..]);
}

#[test]
#[should_panic(expected = "The given handle was not created for this stadium")]
fn get_panics_on_invalid_handle() {
    let mut b_1 = stadium::builder();
    let mut b_2 = stadium::builder();
    b_1.insert(0u8);
    let h_2 = b_2.insert(0u8);
    let s = b_1.build();
    s.get(h_2);
}

#[test]
#[should_panic(expected = "The given handle was not created for this stadium")]
fn get_mut_panics_on_invalid_handle() {
    let mut b_1 = stadium::builder();
    let mut b_2 = stadium::builder();
    b_1.insert(0u8);
    let h_2 = b_2.insert(0u8);
    let mut s = b_1.build();
    s.get_mut(h_2);
}

#[test]
#[should_panic(expected = "The given handle was not created for this stadium")]
fn replace_panics_on_invalid_handle() {
    let mut b_1 = stadium::builder();
    let mut b_2 = stadium::builder();
    b_1.insert(0u8);
    let h_2 = b_2.insert(0u8);
    let mut s = b_1.build();
    s.replace(h_2, 1);
}

#[test]
fn swap_with_same_handle_does_nothing() {
    let mut b = stadium::builder();
    let h = b.insert(0);
    let mut s = b.build();

    assert_eq!(s[h], 0);
    s.swap(h, h);
    assert_eq!(s[h], 0);
}

#[test]
#[should_panic(expected = "`b` is not associated with this `Stadium`")]
fn swap_with_invalid_handle_panics() {
    let mut b_1 = stadium::builder();
    let mut b_2 = stadium::builder();
    let h_1 = b_1.insert(0);
    let h_2 = b_2.insert(0);
    let mut s_1 = b_1.build();

    s_1.swap(h_1, h_2)
}

#[test]
fn swap_values() {
    let mut bu = stadium::builder();
    let a = bu.insert(1);
    let b = bu.insert(2);
    let mut s = bu.build();

    assert_eq!(s[a], 1);
    assert_eq!(s[b], 2);

    s.swap(a, b);

    assert_eq!(s[a], 2);
    assert_eq!(s[b], 1);
}

#[test]
fn the_builder_properly_drops_everything() {
    let drop_count = Rc::new(Cell::new(0));

    {
        let mut b = stadium::builder();

        for _ in 0..100 {
            b.insert(DropCounter(ManuallyDrop::new(Rc::clone(&drop_count))));
        }
    }

    assert_eq!(drop_count.get(), 100);
}

#[test]
fn the_stadium_properly_drops_everything() {
    let drop_count = Rc::new(Cell::new(0));

    {
        let mut b = stadium::builder();

        for _ in 0..100 {
            b.insert(DropCounter(ManuallyDrop::new(Rc::clone(&drop_count))));
        }

        let _ = b.build();
    }

    assert_eq!(drop_count.get(), 100);
}

#[test]
fn the_builder_does_not_deallocate_zst() {
    let mut b = stadium::builder();
    let _ = b.insert(());

    // this should corrupt the memory if it tries to deallocate
    // the `()`.
    //  ... in debug mode at least
}

#[test]
fn stadium_can_retrieve_zst() {
    let mut b = stadium::builder();
    let h = b.insert(());
    let s = b.build();
    assert_eq!(s[h], ());
}

#[test]
fn zst_operations() {
    let mut b = stadium::builder();
    let h_a = b.insert(());
    let h_b = b.insert(());

    let mut s = b.build();

    assert_eq!(s[h_a], ());
    assert_eq!(s[h_b], ());
    assert_eq!(s.replace(h_a, ()), ());
    assert_eq!(s.replace(h_b, ()), ());

    s.swap(h_a, h_b);

    assert_eq!(s[h_a], ());
    assert_eq!(s[h_b], ());
}
