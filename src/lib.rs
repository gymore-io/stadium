use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::marker::PhantomData;
use std::mem::{transmute, MaybeUninit};
use std::ptr::{self, NonNull};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::{fmt, mem, ops};

static NEXT_BUILDER_ID: AtomicUsize = AtomicUsize::new(0);

/// Creates a new [`Builder`].
///
/// # Examples
///
/// ```rust
/// let builder = stadium::builder();
///
/// /* profit */
/// ```
///
/// [`Builder`]: `struct.Builder.html`
#[inline(always)]
pub fn builder<'a>() -> Builder<'a> {
    Builder::new()
}

/// A chunk of allocated memory that stores a bunch of values of different types.
///
/// # Examples
///
/// ```rust
/// let mut builder = stadium::builder();
///
/// let h_vec = builder.insert(vec![1, 2, 3, 4]);
/// let h_string = builder.insert(String::from("Hello"));
/// let h_str = builder.insert("World");
///
/// let mut stadium = builder.build();
///
/// stadium[h_vec][0] = 2;
/// assert_eq!(&stadium[h_vec][..], &[2, 2, 3, 4]);
///
/// assert_eq!(stadium[h_str], "World");
/// ```
///
/// Note that using a `String` or a `Vec` inside of a [`Stadium`] defies a bit of its
/// original purpose (which is storing those different types localy in memory).
///
/// [`Stadium`]: struct.Stadium.html
pub struct Stadium<'a> {
    /// The id of the stadium. This id is unique and prevent a user to use a handle
    /// from another stadium.
    id: usize,

    /// A pointer to the owned data.
    ///
    /// In the case of an empty allocation, this pointer is `NonNull::dangling()`.
    data: NonNull<u8>,

    /// The layout that was used to allocate the stadium.
    layout: Layout,

    /// Maps an `index` to the location of an object.
    ///
    /// SAFETY: All the `Location`s within this vector must reference objects
    /// owned by the stadium.
    ///
    /// When a handle is given by a `Builder`, the `index` and the `T` of that
    /// handle must always match the `Location` at the given index in this vector.
    locations: Box<[Location]>,

    /// The lifetime of the types used inside of the stadium.
    _lifetime: PhantomData<&'a ()>,
}

impl<'a> Stadium<'a> {
    /// Creates a new [`Builder`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use stadium::Stadium;
    ///
    /// let builder = Stadium::builder();
    /// ```
    ///
    /// [`Builder`] struct.Builder.html
    #[inline(always)]
    pub fn builder() -> Builder<'a> {
        Builder::new()
    }

    /// Checks if the given [`Handle`] can be safely used with this [`Stadium`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut builder_1 = stadium::builder();
    /// let handle_1 = builder_1.insert("I'm a string inserted in the first stadium");
    /// let stadium_1 = builder_1.build();
    ///
    /// let mut builder_2 = stadium::builder();
    /// let handle_2 = builder_2.insert("I'm a string inserted in the second stadium");
    /// let stadium_2 = builder_2.build();
    ///
    /// assert_eq!(stadium_1.is_associated_with(handle_2), false);
    /// assert_eq!(stadium_1.is_associated_with(handle_1), true);
    /// assert_eq!(stadium_2.is_associated_with(handle_2), true);
    /// assert_eq!(stadium_2.is_associated_with(handle_1), false);
    /// ```
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`Stadium`]: struct.Stadium.html
    #[inline(always)]
    pub fn is_associated_with<T: 'a>(&self, handle: Handle<T>) -> bool {
        handle.id == self.id
    }

    /// Replaces the object referenced by the given [`Handle`].
    ///
    /// # Safety
    ///
    /// The provided [`Handle`] must be associated with this [`Stadium`].
    ///
    /// To check if a [`Handle`] can be safely used with a given [`Stadium`], use the
    /// [`Stadium::is_associated_with`] function.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    /// let handle = builder.insert(4);
    /// let mut stadium = builder.build();
    ///
    /// // SAFETY: The handle was created for this stadium.
    /// unsafe {
    ///     assert_eq!(stadium.replace_unchecked(handle, 5), 4);
    ///     assert_eq!(stadium.get_unchecked(handle), &5);
    /// }
    /// ```
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`Stadium`]: struct.Stadium.html
    /// [`Stadium::is_associated_with`]: struct.Stadium.html#method.is_associated_with
    #[inline(always)]
    pub unsafe fn replace_unchecked<T: 'a>(&mut self, handle: Handle<T>, val: T) -> T {
        mem::replace(self.get_unchecked_mut(handle), val)
    }

    /// Replaces the object referenced by the given [`Handle`] with the given value.
    ///
    /// # Panics
    ///
    /// This function panics if `handle` is not associated with this [`Stadium`].
    ///
    /// To check if a [`Handle`] can be safely used with a given [`Stadium`], use the
    /// [`Stadium::is_associated_with`] function.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    /// let handle = builder.insert(5);
    /// let mut stadium = builder.build();
    ///
    /// assert_eq!(stadium.replace(handle, 6), 5);
    /// assert_eq!(stadium.get(handle), &6);
    /// ```
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`Stadium`]: struct.Stadium.html
    /// [`Stadium::is_associated_with`]: struct.Stadium.html#method.is_associated_with
    #[inline(always)]
    pub fn replace<T: 'a>(&mut self, handle: Handle<T>, val: T) -> T {
        mem::replace(self.get_mut(handle), val)
    }

    /// Gets a reference to a value that is part of the [`Stadium`].
    ///
    /// # Panics
    ///
    /// This function panics if `handle` is not associated with this `Stadium`.
    ///
    /// To check if a [`Handle`] can be safely used with a given [`Stadium`], use the
    /// [`Stadium::is_associated_with`] function.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    ///
    /// let h_num = builder.insert(2023);
    /// let h_str = builder.insert("Hello, world");
    ///
    /// let stadium = builder.build();
    ///
    /// assert_eq!(stadium.get(h_str), &"Hello, world");
    /// assert_eq!(stadium.get(h_num), &2023);
    /// ```
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`Stadium`]: struct.Stadium.html
    /// [`Stadium::is_associated_with`]: struct.Stadium.html#method.is_associated_with
    #[inline]
    pub fn get<T: 'a>(&self, handle: Handle<T>) -> &T {
        assert!(
            self.is_associated_with(handle),
            "The given handle was not created for this stadium"
        );

        // SAFETY: If a handle is valid, its index is always in the bounds of `locations`.
        unsafe {
            // SAFETY: The handle was created for this stadium.
            // The object has a location.
            self.get_unchecked(handle)
        }
    }

    /// Gets a reference to a value that is part of the [`Stadium`].
    ///
    /// # Panics
    ///
    /// This function panics if `handle` is not associated with this [`Stadium`].
    ///
    /// To check if a [`Handle`] can be safely used with a given [`Stadium`], use the
    /// [`Stadium::is_associated_with`] function.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    ///
    /// let h_num = builder.insert(250);
    /// let h_vec = builder.insert(vec![1, 2, 3]);
    ///
    /// let mut stadium = builder.build();
    ///
    /// *stadium.get_mut(h_num) = 5;
    /// stadium.get_mut(h_vec).push(4);
    ///
    /// assert_eq!(stadium.get(h_num), &5);
    /// assert_eq!(&stadium.get(h_vec)[..], &[1, 2, 3, 4])
    /// ```
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`Stadium`]: struct.Stadium.html
    /// [`Stadium::is_associated_with`]: struct.Stadium.html#method.is_associated_with
    #[inline]
    pub fn get_mut<T: 'a>(&mut self, handle: Handle<T>) -> &mut T {
        assert!(
            self.is_associated_with(handle),
            "The given handle was not created for this stadium"
        );

        // SAFETY: see `Stadium::get`
        unsafe { self.get_unchecked_mut(handle) }
    }

    /// Gets a reference to a value that is part of the [`Stadium`].
    ///
    /// # Safety
    ///
    /// The provided [`Handle`] must be associated with this [`Stadium`].
    ///
    /// To check if a [`Handle`] can be safely used with a given [`Stadium`], use the
    /// [`Stadium::is_associated_with`] function.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    /// let handle = builder.insert(5);
    /// let mut stadium = builder.build();
    ///
    /// // SAFETY: The handle was provided by the builder of this stadium.
    /// unsafe { assert_eq!(stadium.get_unchecked(handle), &5) };
    /// ```
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`Stadium`]: struct.Stadium.html
    /// [`Stadium::is_associated_with`]: struct.Stadium.html#method.is_associated_with
    #[inline(always)]
    pub unsafe fn get_unchecked<T: 'a>(&self, handle: Handle<T>) -> &T {
        // SAFETY: This function can only be called using a shared reference to `self`
        // This ensure that no one has a mutable reference to this `T`.
        //
        // The caller must ensure that `handle` is associated with this `Stadium`.
        &*self.get_ptr(handle)
    }

    /// Gets a reference to a value that is part of the [`Stadium`].
    ///
    /// # Safety
    ///
    /// The provided [`Handle`] must be associated with this [`Stadium`].
    ///
    /// To check if a [`Handle`] can be safely used with a given [`Stadium`], use the
    /// [`Stadium::is_associated_with`] function.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    /// let handle = builder.insert(5);
    /// let mut stadium = builder.build();
    ///
    /// // SAFETY: The handle was provided by the builder of this stadium.
    /// unsafe {
    ///     *stadium.get_unchecked_mut(handle) = 4;
    ///     assert_eq!(stadium.get_unchecked(handle), &4);
    /// }
    /// ```
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`Stadium`]: struct.Stadium.html
    /// [`Stadium::is_associated_with`]: struct.Stadium.html#method.is_associated_with
    #[inline(always)]
    pub unsafe fn get_unchecked_mut<T: 'a>(&mut self, handle: Handle<T>) -> &mut T {
        // SAFETY: This function was called using a mutable reference to `self`.
        // This ensure that no one else has a mutable reference to this `T`.
        //
        // The caller must ensure that `handle` is associated with this `Stadium`.
        &mut *self.get_ptr_mut(handle)
    }

    /// Gets a pointer to the element referenced by the given [`RawHandle`].
    ///
    /// # Safety
    ///
    /// This function is unsafe unless:
    ///  * The given [`Handle`] is associated with this [`Stadium`].
    ///  * The returned pointer is used *as if* it was a `*const T` where
    /// `T` is the type of the original [`Handle`] (it was `Handle<T>`).
    ///
    /// To check if a [`Handle`] can be safely used with a given [`Stadium`], use the
    /// [`Stadium::is_associated_with`] function.
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`Stadium`]: struct.Stadium.html
    /// [`Stadium::is_associated_with`]: struct.Stadium.html#method.is_associated_with
    /// [`RawHandle`]: struct.RawHandle.html
    #[inline(always)]
    pub unsafe fn get_ptr_raw(&self, handle: RawHandle) -> *const u8 {
        // SAFETY: The caller must ensure that the handle is actually valid.
        // A valid handle hold an index that is in bounds.
        self.locations.get_unchecked(handle.index).data
    }

    /// Gets a pointer to the element referenced by the given [`RawHandle`].
    ///
    /// # Safety
    ///
    /// This function is unsafe unless:
    ///  * The given [`Handle`] is associated with this [`Stadium`].
    ///  * The returned pointer is used *as if* it was a `*mut T` where
    /// `T` is the type of the original [`Handle`] (it was `Handle<T>`).
    ///
    /// To check if a [`Handle`] can be safely used with a given [`Stadium`], use the
    /// [`Stadium::is_associated_with`] function.
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`Stadium`]: struct.Stadium.html
    /// [`Stadium::is_associated_with`]: struct.Stadium.html#method.is_associated_with
    /// [`RawHandle`]: struct.RawHandle.html
    #[inline(always)]
    pub unsafe fn get_ptr_mut_raw(&mut self, handle: RawHandle) -> *mut u8 {
        // SAFETY: The caller must ensure that the handle is actually valid.
        // A valid handle hold an index that is in bounds.
        self.locations.get_unchecked_mut(handle.index).data
    }

    /// Gets a pointer to the element referenced by the given [`Handle`].
    ///
    /// # Safety
    ///
    /// The given [`Handle`] must be associated with this [`Stadium`].
    ///
    /// To check if a [`Handle`] can be safely used with a given [`Stadium`], use the
    /// [`Stadium::is_associated_with`] function.
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`Stadium`]: struct.Stadium.html
    /// [`Stadium::is_associated_with`]: struct.Stadium.html#method.is_associated_with
    #[inline(always)]
    pub unsafe fn get_ptr<T: 'a>(&self, handle: Handle<T>) -> *const T {
        // SAFETY: The caller must ensure that the handle was associated with this
        // `Stadium`.
        // The raw handle was created from a `Handle<T>`.
        self.get_ptr_raw(handle.raw()).cast()
    }

    /// Gets a pointer to the element referenced by the given [`Handle`].
    ///
    /// # Safety
    ///
    /// The given [`Handle`] must be associated with this [`Stadium`].
    ///
    /// To check if a [`Handle`] can be safely used with a given [`Stadium`], use the
    /// [`Stadium::is_associated_with`] function.
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`Stadium`]: struct.Stadium.html
    /// [`Stadium::is_associated_with`]: struct.Stadium.html#method.is_associated_with
    #[inline(always)]
    pub unsafe fn get_ptr_mut<T: 'a>(&mut self, handle: Handle<T>) -> *mut T {
        // SAFETY: The caller must ensure that the handle was associated with this
        // `Stadium`.
        // The raw handle was created from a `Handle<T>`.
        self.get_ptr_mut_raw(handle.raw()).cast()
    }

    /// Swaps the values referenced by `a` and `b` within this [`Stadium`].
    ///
    /// # Safety
    ///
    /// * This given handles `a` and `b` must both be associated with this [`Stadium`].
    /// * `a` must be different from `b`
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    /// let a = builder.insert("Foo");
    /// let b = builder.insert("Bar");
    /// let mut s = builder.build();
    ///
    /// assert_eq!(s[a], "Foo");
    /// assert_eq!(s[b], "Bar");
    ///
    /// // SAFETY: Those two handles are associated with `s`.
    /// unsafe { s.swap_unchecked(a, b); }
    ///
    /// assert_eq!(s[a], "Bar");
    /// assert_eq!(s[b], "Foo");
    /// ```
    ///
    /// [`Stadium`]: struct.Stadium.html
    pub unsafe fn swap_unchecked<T: 'a>(&mut self, a: Handle<T>, b: Handle<T>) {
        // SAFETY: This function was called using a mutable reference to `self`
        // which mean no one else has a reference to any of those two objects.
        //
        // The caller must ensure that the given handle is actually valid AND
        // distinct.
        let a = &mut *self.get_ptr_mut(a);
        let b = &mut *self.get_ptr_mut(b);
        mem::swap(a, b);
    }

    /// Swaps the values referenced by `a` and `b` within this [`Stadium`].
    ///
    /// # Panics
    ///
    /// This function panics if one of `a` or `b` is not associated with tihs [`Stadium`].
    ///
    /// To check if a [`Handle`] can be safely used with a given [`Stadium`], use the
    /// [`Stadium::is_associated_with`] function.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    /// let a = builder.insert("Foo");
    /// let b = builder.insert("Bar");
    /// let mut s = builder.build();
    ///
    /// assert_eq!(s[a], "Foo");
    /// assert_eq!(s[b], "Bar");
    ///
    /// s.swap(a, b);
    ///
    /// assert_eq!(s[a], "Bar");
    /// assert_eq!(s[b], "Foo");
    /// ```
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`Stadium`]: struct.Stadium.html
    /// [`Stadium::is_associated_with`]: struct.Stadium.html#method.is_associated_with
    pub fn swap<T: 'a>(&mut self, a: Handle<T>, b: Handle<T>) {
        if a != b {
            assert!(
                self.is_associated_with(a),
                "`a` is not associated with this `Stadium`"
            );
            assert!(
                self.is_associated_with(b),
                "`b` is not associated with this `Stadium`"
            );

            // SAFETY: a != b and those handles are both
            // associated with this `Stadium`.
            unsafe { self.swap_unchecked(a, b) };
        }
    }
}

impl Drop for Stadium<'_> {
    fn drop(&mut self) {
        for location in self.locations.iter() {
            if let Some(drop_fn) = location.meta.drop_fn {
                // SAFETY: The data in the stadium is always initialized.
                unsafe { drop_fn(location.data) };
            }
        }

        // Now that all objects are dropped
        // We can deallocate the chunk of memory

        // check for empty stadiums
        if self.data != NonNull::dangling() {
            // SAFETY: The chunk was allocated with the same allocator and layout.
            unsafe { dealloc(self.data.as_ptr(), self.layout) };
        }
    }
}

impl<'a, T: 'a> ops::Index<Handle<T>> for Stadium<'a> {
    type Output = T;

    #[inline(always)]
    fn index(&self, handle: Handle<T>) -> &Self::Output {
        self.get(handle)
    }
}

impl<'a, T: 'a> ops::IndexMut<Handle<T>> for Stadium<'a> {
    #[inline(always)]
    fn index_mut(&mut self, handle: Handle<T>) -> &mut Self::Output {
        self.get_mut(handle)
    }
}

/// Locates an object within a `Stadium`.
struct Location {
    /// A pointer to the actual object.
    data: *mut u8,
    /// Information about the object.
    meta: ObjectMeta,
}

/// A structure used to create a [`Stadium`]. This function can be created using
/// the [`stadium::builder`] function.
///
/// [`Stadium`]: struct.Stadium.html
/// [`stadium::builder`]: fn.builder.html
pub struct Builder<'a> {
    id: usize,
    reserved_objects: Vec<Reserved<'a>>,
}

impl<'a> Builder<'a> {
    /// Creates a new instance of [`Builder`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// let builder = stadium::Builder::new();
    /// // That it! Now you have your own builder.
    /// ```
    ///
    /// [`Builder`]: struct.Builder.html
    #[inline(always)]
    pub fn new() -> Self {
        Self {
            id: NEXT_BUILDER_ID.fetch_add(1, Ordering::Relaxed),
            reserved_objects: Vec::new(),
        }
    }

    /// Prepares the insertion of `init` into the [`Stadium`].
    ///
    /// # Panics
    ///
    /// This function panics if it fails to allocate a box for `init`.
    ///
    /// [`Stadium`]: struct.Stadium.html
    pub fn insert<T: 'a>(&mut self, init: T) -> Handle<T> {
        let index = self.reserved_objects.len();
        self.reserved_objects.push(Reserved::new(init));
        Handle {
            id: self.id,
            index,
            _marker: PhantomData,
        }
    }

    /// Prepares the insertion of a `MaybeUninit<T>` into the [`Stadium`] where
    /// `T` is the type described by the given [`ObjectMeta`] structure.
    ///
    /// [`ObjectMeta`]: struct.ObjectMeta.html
    /// [`Stadium`]: struct.Stadium.html
    pub fn insert_raw(&mut self, meta: ObjectMeta) -> RawHandle {
        let index = self.reserved_objects.len();
        self.reserved_objects.push(Reserved::uninit(meta));
        RawHandle { index }
    }

    /// Prepares the insertion of a `MaybeUninit<T>` into the [`Stadium`].
    ///
    /// [`Stadium`]: struct.Stadium.html
    pub fn insert_uninit<T>(&mut self) -> Handle<MaybeUninit<T>> {
        let meta = ObjectMeta::of::<T>();
        let handle = self.insert_raw(meta);
        unsafe { handle.trust_with_builder(&self) }
    }

    /// Prepares the insertion of a `T` into the [`Stadium`] where `T` is the type
    /// described by the given [`ObjectMeta`] structure.
    ///
    /// # Safety
    ///
    /// `T` must be safely created using `mem::zeroed()`.
    ///
    /// [`ObjectMeta`]: struct.ObjectMeta.html
    /// [`Stadium`]: struct.Stadium.html
    pub unsafe fn insert_zeroed_raw(&mut self, meta: ObjectMeta) -> RawHandle {
        let index = self.reserved_objects.len();
        self.reserved_objects.push(Reserved::zeroed(meta));
        RawHandle { index }
    }

    /// Prepares the insertion of a `T` into the [`Stadium`].
    ///
    /// # Safety
    ///
    /// `T` must be safely created using `mem::zeroed()`.
    ///
    /// [`Stadium`]: struct.Stadium.html
    pub unsafe fn insert_zeroed<T>(&mut self) -> Handle<T> {
        let meta = ObjectMeta::of::<T>();
        let handle = self.insert_zeroed_raw(meta);
        handle.trust_with_builder(self)
    }

    /// Prepares the insertion of a `T` into the [`Stadium`].
    /// The `T` will be automatically initialized to its default value.
    ///
    /// [`Stadium`]: struct.Stadium.html
    pub fn insert_default<T: Default>(&mut self) -> Handle<T> {
        unsafe fn write_default<T: Default>(ptr: *mut T) {
            ptr.write(T::default())
        }

        let index = self.reserved_objects.len();
        self.reserved_objects
            .push(unsafe { Reserved::func(write_default::<T>) });

        Handle {
            id: self.id,
            index,
            _marker: PhantomData,
        }
    }

    /// Builds a new [`Stadium`].
    ///
    /// # Panics
    ///
    /// This function can panics if one of the following events occure:
    ///  * The builder is empty
    ///  * The function fails to allocate for the stadium
    ///
    /// [`Stadium`]: struct.Stadium.html
    pub fn build(self) -> Stadium<'a> {
        let objects = self.reserved_objects;
        let id = self.id;

        let mut total_size = 0;
        let mut max_align = 1;

        for obj in &objects {
            total_size += obj.meta.layout.size();
            max_align = Ord::max(max_align, obj.meta.layout.align());
        }

        let layout = Layout::from_size_align(total_size, max_align)
            .expect("Failed to compute the layout of the stadium");

        let ptr = unsafe {
            if total_size == 0 {
                // The stadium will be either empty or only store zero-sized types.
                NonNull::dangling() // zero-sized allocation
            } else {
                NonNull::new(alloc(layout)).unwrap_or_else(|| handle_alloc_error(layout))
            }
        };

        let object_count = objects.len();

        let mut sorted_vector: Vec<(usize, Reserved)> = objects.into_iter().enumerate().collect();

        // Sort the vector so that objects are sorted by align (ascending).
        sorted_vector.sort_unstable_by_key(|(_, o)| o.meta.layout.align());

        // We need this structure to map the handles that the builder has given
        // to actual objects within the stadium.
        // TODO: use `Box::new_uninit_slice` when stable.
        let mut locations: Vec<Location> = Vec::with_capacity(object_count);

        let mut cursor = ptr.as_ptr();
        for (original_index, obj) in sorted_vector.into_iter().rev() {
            // Safety check that should always pass
            assert_eq!(cursor as usize % obj.meta.layout.align(), 0);

            // SAFETY: We just checked if cursor was well-aligned.
            // We know cursor cannot be null.
            // We own the memory and have exclusive access to it.
            let meta = unsafe { obj.consume(cursor) };

            // The cursor stays aligned because the size of an object is always
            // a multiple of its alignement. Because we are iterating in reversed
            // order (large align -> little align), the cursor is always aligned
            // to the current object.
            //
            // This works because the alignement is always a power of 2.

            // SAFETY: it is important that the index is the same as the index that
            // was given to the used through the `Handle`. This index will
            // be trusted by the `Stadium` for the type of the object and for its
            // location.
            //
            // The `locations` vector was created with a capacity of `object_count`
            // The values of `original_index` are all differents and
            // `0 <= original_index < object_count`.
            unsafe {
                locations
                    .as_mut_ptr()
                    .add(original_index)
                    .write(Location { meta, data: cursor });
            }

            // SAFETY: We own the data. A safety check will be done after the loop.
            cursor = unsafe { cursor.add(meta.layout.size()) };
        }

        // SAFETY: This vector was properly initialized inside the loop and has a
        // capacity of `object_count`.
        unsafe { locations.set_len(object_count) };

        // Safety check that should always pass
        assert_eq!(cursor as usize, ptr.as_ptr() as usize + total_size);

        // Now the stadium is properly initialized.

        Stadium {
            id,
            data: ptr,
            layout,
            locations: locations.into_boxed_slice(),
            _lifetime: PhantomData,
        }
    }
}

impl<'a> From<Builder<'a>> for Stadium<'a> {
    #[inline(always)]
    fn from(builder: Builder<'a>) -> Self {
        builder.build()
    }
}

// In the following documentation, the type `T` is refering to the type of the reserved
// object.

/// Stores information about a `T`.
#[derive(Clone, Copy)]
pub struct ObjectMeta {
    /// The layout of `T`.
    layout: Layout,
    /// A function that causes a `T` to be dropped.
    ///
    /// # Safety
    ///
    /// * The given pointer must reference an initialized `T`.
    drop_fn: Option<unsafe fn(*mut u8)>,
}

impl ObjectMeta {
    /// Computes the [`ObjectMeta`] of the type `T`.
    ///
    /// [`ObjectMeta`]: struct.ObjectMeta.html
    pub fn of<T>() -> Self {
        Self {
            layout: Layout::new::<T>(),
            drop_fn: if mem::needs_drop::<T>() {
                Some(|ptr: *mut u8| unsafe { ptr::drop_in_place(ptr as *mut T) })
            } else {
                None
            },
        }
    }
}

/// Describes how a reserved value should be initialized when a stadium is
/// created.
enum InitialValue {
    /// The value may be left uninitialized.
    Uninit,
    /// The value should be initialized using `mem::zeroed()`.
    Zeroed,
    /// The value should be initialized by a function.
    ///
    /// # Safety
    ///
    /// The `*mut u8` given to the inner function must be a valid location for
    /// a `T` to be written.
    Fn(unsafe fn(*mut u8)),
    /// The value should be initialized using the allocated value.
    Value(NonNull<u8>),
}

/// Stores information about a `T` as well as an initialized instance of `T`.
struct Reserved<'a> {
    /// Stores information about a `T`.
    meta: ObjectMeta,

    /// The actual reserved value.
    initial_value: InitialValue,

    // The lifetime of `T`.
    _lifetime: PhantomData<&'a ()>,
}

impl<'a> Reserved<'a> {
    /// Creates a new instance of `Reserved` from the given initial value.
    ///
    /// # Panics
    ///
    /// This function panics if it fails to allocate a box for the given `T`.
    fn new<T: 'a>(init: T) -> Self {
        let meta = ObjectMeta::of::<T>();

        let initial_value = unsafe {
            if meta.layout.size() == 0 {
                // ZSTs can be left uninitialized.
                InitialValue::Uninit
            } else {
                // SAFETY: `T` is not a zero-sized type.
                let ptr = NonNull::new(alloc(meta.layout))
                    .unwrap_or_else(|| handle_alloc_error(meta.layout));

                // Initialize the value.
                ptr.as_ptr().cast::<T>().write(init);

                InitialValue::Value(ptr)
            }
        };

        // The initial value is now properly initialized.

        Self {
            meta,
            initial_value,
            _lifetime: PhantomData,
        }
    }

    /// Creates a new instance of `Reserved` for a `MaybeUninit<T>`
    /// where `T` is the type of the object described by the given `ObjectMeta`.
    ///
    /// # Panics
    ///
    /// This function panics if it fails to allocate a box for `T`.
    fn uninit(meta: ObjectMeta) -> Self {
        // Being uninit is a valid state for a `MaybeUninit<T>`
        Self {
            initial_value: InitialValue::Uninit,
            meta,
            _lifetime: PhantomData,
        }
    }

    /// Creates a new instance of `Reserved` for a `T` where `T` is the object
    /// described by the given `ObjectMeta`.
    ///
    /// # Safety
    ///
    /// `T` must be safely created using `mem::zeroed()`.
    ///
    unsafe fn zeroed(meta: ObjectMeta) -> Self {
        let initial_value = if meta.layout.size() == 0 {
            InitialValue::Uninit
        } else {
            InitialValue::Zeroed
        };

        Self {
            meta,
            initial_value,
            _lifetime: PhantomData,
        }
    }

    /// Creates a new instance of `Reserved` for a `T` where `T` is the object
    /// described by the given `ObjectMeta`.
    ///
    /// # Safety
    ///
    /// The given function must properly initialize the given `T`.
    unsafe fn func<T>(f: unsafe fn(*mut T)) -> Self {
        let meta = ObjectMeta::of::<T>();

        let f = transmute(f);

        let initial_value = if meta.layout.size() == 0 {
            InitialValue::Uninit
        } else {
            InitialValue::Fn(f)
        };

        Self {
            meta,
            initial_value,
            _lifetime: PhantomData,
        }
    }

    /// Consumes `self` and turns it into its inner `T`. The value is written on the
    /// given pointer `target`.
    ///
    /// # Safety
    ///
    /// `target` must be a valid location for an object of type `T` to be written on.
    unsafe fn consume(self, target: *mut u8) -> ObjectMeta {
        // SAFETY: We're moving out the value.
        let initial_value = ptr::read(&self.initial_value);
        let meta = self.meta;

        // `self` mut not be dropped because this would cause the value at `initial_value`
        // to be dropped even though it was moved.
        mem::forget(self);

        match initial_value {
            InitialValue::Value(ptr) => {
                // SAFETY: We are moving the value referenced by `initial_value` to
                // `target`.
                ptr::copy_nonoverlapping(ptr.as_ptr(), target, meta.layout.size());

                // We have to dealloc the layout though.
                dealloc(ptr.as_ptr(), meta.layout);
            }
            InitialValue::Fn(f) => f(target),
            InitialValue::Zeroed => ptr::write_bytes(target, 0u8, meta.layout.size()),
            InitialValue::Uninit => (),
        }

        meta
    }
}

impl Drop for Reserved<'_> {
    fn drop(&mut self) {
        if let InitialValue::Value(ptr) = self.initial_value {
            // We have to drop the initial value that was not used.
            if let Some(drop_fn) = self.meta.drop_fn {
                // SAFETY: The value is known to be initialized.
                unsafe { drop_fn(ptr.as_ptr()) };
            }

            // SAFETY: The layout was used to allocate the `T` in `Self::new` and the value
            // that was here was properly dropped beforehand.
            unsafe { dealloc(ptr.as_ptr(), self.meta.layout) };
        }
    }
}

/// A safe handle to a specific object stored in a specific [`Stadium`]. This handle can
/// be optained from the [`Builder::insert`] function.
///
/// [`Stadium`]: struct.Stadium.html
/// [`Builder::insert`]: struct.Builder.html#method.insert
pub struct Handle<T> {
    /// The id of the stadium this handle exist for.
    id: usize,
    /// The index of the location of the object referenced by this handle.
    index: usize,

    // Invariant T owned by this handle.
    _marker: PhantomData<*mut T>,
}

impl<T> Clone for Handle<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            index: self.index,
            _marker: PhantomData,
        }
    }
}

impl<T> Copy for Handle<T> {}

impl<T> fmt::Debug for Handle<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("Handle").field(&self.index).finish()
    }
}

impl<T> PartialEq for Handle<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.index == other.index
    }
}

impl<T> Eq for Handle<T> {}

impl<T> Handle<T> {
    /// Converts this [`Handle`] into a [`RawHandle`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    /// let raw_handle = builder.insert("Hello").raw();
    /// ```
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`RawHandle`]: struct.RawHandle.html
    #[inline(always)]
    pub fn raw(self) -> RawHandle {
        RawHandle { index: self.index }
    }
}

/// A handle to a `T` that does not own a `T`. This handle dos not remember
/// what stadium created it.
#[derive(Clone, Copy)]
pub struct RawHandle {
    /// The index of the location of the object referenced by this handle.
    index: usize,
}

impl RawHandle {
    /// Recreate an [`Handle`] from this [`RawHandle`].
    ///
    /// # Safety
    ///
    ///  * The generic type parameter `T` must be the same as the original [`Handle`]
    /// that was used to produce this [`RawHandle`].
    ///  * The given [`Stadium`] must be the one associated with the original handle.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    /// let handle = builder.insert(5i32);
    /// let stadium = builder.build();
    ///
    /// let raw_handle = handle.raw();
    ///
    /// // SAFETY: The handle was given by the builder that created the stadium and was
    /// // created for a `i32`.
    /// let handle = unsafe { raw_handle.trust::<i32>(&stadium) };
    ///
    /// assert_eq!(stadium[handle], 5);
    /// ```
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`RawHandle`]: struct.RawHandle.html
    /// [`Stadium`]: struct.Stadium.html
    #[inline(always)]
    pub unsafe fn trust<T>(self, stadium: &Stadium) -> Handle<T> {
        Handle {
            index: self.index,
            id: stadium.id,
            _marker: PhantomData,
        }
    }

    /// Recreate an [`Handle`] from this [`RawHandle`].
    ///
    /// # Safety
    ///
    ///  * The generic type parameter `T` must be the same as the original [`Handle`]
    /// that was used to produce this `RawHandle`.
    ///  * The given [`Builder`] must be the one associated with the original handle.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    /// let raw_handle = builder.insert(5i32).raw();
    ///
    /// // SAFETY: The handle was given by this builder and was created for a `i32`.
    /// let handle = unsafe { raw_handle.trust_with_builder::<i32>(&builder) };
    ///
    /// let stadium = builder.build();
    /// assert_eq!(stadium[handle], 5);
    /// ```
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`RawHandle`]: struct.RawHandle.html
    /// [`Builder`]: struct.Builder.html
    #[inline(always)]
    pub unsafe fn trust_with_builder<T>(self, builder: &Builder) -> Handle<T> {
        Handle {
            index: self.index,
            id: builder.id,
            _marker: PhantomData,
        }
    }
}
