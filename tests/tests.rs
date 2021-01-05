#[test]
#[should_panic(expected = "")]
fn panic_on_build_with_no_objects() {
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
#[should_panic(expected = "")]
fn panic_on_zero_sized_type_insert() {
    let mut b = stadium::builder();
    b.insert(());
}

#[test]
#[should_panic(expected = "")]
fn panic_on_zero_sized_type_insert_raw() {
    let meta = stadium::ObjectMeta::of::<()>();
    let mut b = stadium::builder();
    b.insert_raw(meta);
}

#[test]
fn stadium_is_valid_handle() {
    let mut b_1 = stadium::builder();
    let mut b_2 = stadium::builder();
    let h_1 = b_1.insert(0u8);
    let h_2 = b_2.insert(0u8);
    let s_1 = b_1.build();
    let s_2 = b_2.build();

    assert_eq!(s_1.is_valid_handle(h_1), true);
    assert_eq!(s_1.is_valid_handle(h_2), false);
    assert_eq!(s_2.is_valid_handle(h_1), false);
    assert_eq!(s_2.is_valid_handle(h_2), true);
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
