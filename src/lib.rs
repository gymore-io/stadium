use std::alloc::{alloc, dealloc, Layout};
use std::marker::PhantomData;
use std::ptr::{self, NonNull};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::{mem, ops};

use mem::MaybeUninit;

static NEXT_BUILDER_ID: AtomicUsize = AtomicUsize::new(0);

/// Creates a new `Builder`.
///
/// ## Example
///
/// ```rust
/// let builder = stadium::builder();
///
/// /* profit */
/// ```
#[inline(always)]
pub fn builder() -> Builder {
    Builder::new()
}

/// A chunk of allocated memory that stores a bunch of values of different types.
///
/// ## Example
///
/// ```rust
/// let mut builder = stadium::builder();
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
/// Note that using a `String` or a `Vec` inside of a `Stadium` defies a bit of its
/// original purpose (which is storing those different types localy in memory).
pub struct Stadium {
    /// The id of the stadium. This id is unique and prevent a user to use a handle
    /// from another stadium.
    id: usize,

    /// A pointer to the owned data.
    data: NonNull<u8>,

    /// The layout that was used to allocate the pool.
    layout: Layout,

    /// Maps an `index` to the location of an object.
    ///
    /// SAFETY: All the `ObjectLocation`s within this vector must reference objects
    /// owned by the stadium.
    ///
    /// When a handle is given by a `Builder`, the `index` and the `T` of that
    /// handle must always match the `ObjectLocation` at the given index in this vector.
    locations: Vec<ObjectLocation>,
}

impl Stadium {
    /// Creates a new `Builder`.
    ///
    /// ## Example
    ///
    /// ```rust
    /// use stadium::Stadium;
    ///
    /// let builder = Stadium::builder();
    /// ```
    #[inline(always)]
    pub fn builder() -> Builder {
        Builder::new()
    }

    /// Checks if the given `ObjectHandle` can be safely used with this `Stadium`.
    ///
    /// ## Example
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
    /// assert_eq!(stadium_1.is_valid_handle(handle_2), false);
    /// assert_eq!(stadium_1.is_valid_handle(handle_1), true);
    /// assert_eq!(stadium_2.is_valid_handle(handle_2), true);
    /// assert_eq!(stadium_2.is_valid_handle(handle_1), false);
    /// ```
    #[inline(always)]
    pub fn is_valid_handle<T>(&self, handle: ObjectHandle<T>) -> bool {
        handle.id == self.id
    }

    /// Replaces the object referenced by the given handle assuming that the handle
    /// was created for this specific `Stadium`.
    ///
    /// ## Safety
    ///
    /// The given handle must've been created for this specific `Stadium`.
    //
    /// ## Example
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
    #[inline(always)]
    pub unsafe fn replace_unchecked<T>(&mut self, handle: ObjectHandle<T>, val: T) -> T {
        mem::replace(self.get_unchecked_mut(handle), val)
    }

    /// Replaces the object referenced by the given handle with the given value.
    ///
    /// ## Panics
    ///
    /// This function panics if the given handle was invalid.
    ///
    /// ## Example
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    /// let handle = builder.insert(5);
    /// let mut stadium = builder.build();
    ///
    /// assert_eq!(stadium.replace(handle, 6), 5);
    /// assert_eq!(stadium.get(handle), &6);
    /// ```
    #[inline(always)]
    pub fn replace<T>(&mut self, handle: ObjectHandle<T>, val: T) -> T {
        mem::replace(self.get_mut(handle), val)
    }

    /// Gets a reference to a value that is part of the `Stadium`.
    ///
    /// ## Panics
    ///
    /// This function panics if the given `ObjectHandle` was not created for this
    /// `Stadium`.
    ///
    /// ## Example
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
    #[inline]
    pub fn get<T>(&self, handle: ObjectHandle<T>) -> &T {
        // SAFETY: If a handle is valid, its index is always in the bounds of `locations`.
        if self.is_valid_handle(handle) {
            unsafe {
                // SAFETY: The handle was created for this stadium.
                // The object has a location.
                self.get_unchecked(handle)
            }
        } else {
            panic!("The given handle was not created for this pool");
        }
    }

    /// Gets a reference to a value that is part of the `Stadium`.
    ///
    /// ## Panics
    ///
    /// This function panics if the given `ObjectHandle` was not created for this
    /// `Stadium`.
    ///
    /// ## Example
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
    #[inline]
    pub fn get_mut<T>(&mut self, handle: ObjectHandle<T>) -> &mut T {
        // SAFETY: see `Stadium::get`
        if self.is_valid_handle(handle) {
            unsafe { self.get_unchecked_mut(handle) }
        } else {
            panic!("The given handle was not created for this pool");
        }
    }

    /// Gets a reference to a value that is part of the `Stadium`.
    ///
    /// ## Safety
    ///
    /// Providing a handle that wasn't created for this specific `Stadium` is
    /// undefined behaviour.
    ///
    /// ## Example
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    /// let handle = builder.insert(5);
    /// let mut stadium = builder.build();
    ///
    /// // SAFETY: The handle was provided by the builder of this stadium.
    /// unsafe { assert_eq!(stadium.get_unchecked(handle), &5) };
    /// ```
    #[inline(always)]
    pub unsafe fn get_unchecked<T>(&self, handle: ObjectHandle<T>) -> &T {
        // SAFETY: The caller must ensure that the handle was created for this stadium.
        // The stored index is always in bounds.
        let location = self.locations.get_unchecked(handle.index);

        // SAFETY: This cast is valid because the object handle "remembers" the
        // type of the object at this location.
        //
        // The dereference is valid be cause it is an invariant of the pool
        // that every location of the `locations` vector is valid and part
        // of the stadium.
        &*location.data.cast()
    }

    /// Gets a reference to a value that is part of the `Stadium`.
    ///
    /// ## Safety
    ///
    /// Providing a handle that wasn't created for this specific `Stadium` is
    /// undefined behaviour.
    ///
    /// ## Example
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    /// let handle = builder.insert(5);
    /// let mut stadium = builder.build();
    ///
    /// // SAFETY: The handle was provided by the builder of this pool.
    /// unsafe {
    ///     *stadium.get_unchecked_mut(handle) = 4;
    ///     assert_eq!(stadium.get_unchecked(handle), &4);
    /// }
    /// ```
    #[inline(always)]
    pub unsafe fn get_unchecked_mut<T>(&mut self, handle: ObjectHandle<T>) -> &mut T {
        // SAFETY: see `Stadium::get_unchecked`
        &mut *self.locations.get_unchecked_mut(handle.index).data.cast()
    }
}

impl Drop for Stadium {
    fn drop(&mut self) {
        for location in &self.locations {
            if let Some(drop_fn) = location.meta.drop_fn {
                // SAFETY: The data in the pool is always initialized.
                unsafe { drop_fn(location.data) };
            }
        }

        // Now that all objects are dropped
        // We can deallocate the chunk of memory

        // SAFETY: The chunk was allocated with the same allocator and layout.
        unsafe { dealloc(self.data.as_ptr(), self.layout) };
    }
}

impl<T> ops::Index<ObjectHandle<T>> for Stadium {
    type Output = T;

    #[inline(always)]
    fn index(&self, handle: ObjectHandle<T>) -> &Self::Output {
        self.get(handle)
    }
}

impl<T> ops::IndexMut<ObjectHandle<T>> for Stadium {
    #[inline(always)]
    fn index_mut(&mut self, handle: ObjectHandle<T>) -> &mut Self::Output {
        self.get_mut(handle)
    }
}

/// Locates an object within a `Stadium`.
struct ObjectLocation {
    /// A pointer to the actual object.
    data: *mut u8,
    /// Information about the object.
    meta: ObjectMeta,
}

/// A structure used to create a `Stadium`. This function can be created using
/// the `Stadium::builder` function.
pub struct Builder {
    id: usize,
    reserved_objects: Vec<ReservedObject>,
}

impl Builder {
    /// Creates a new instance of `Builder`.
    ///
    /// ## Example
    ///
    /// ```rust
    /// let builder = stadium::Builder::new();
    /// // That it! Now you have your own builder.
    /// ```
    #[inline(always)]
    pub fn new() -> Self {
        Self {
            // TODO: Figure out what Ordering is the best for this case because we don't
            // really care about the order in which those operations are being computed
            id: NEXT_BUILDER_ID.fetch_add(1, Ordering::Relaxed),
            reserved_objects: Vec::new(),
        }
    }

    /// Prepares the insertion of `init` into the pool.
    ///
    /// ## Panics
    ///
    /// This function panics if `T` is a zero-sized type.
    pub fn insert<T>(&mut self, init: T) -> ObjectHandle<T> {
        let index = self.reserved_objects.len();
        self.reserved_objects.push(ReservedObject::new(init));
        ObjectHandle {
            id: self.id,
            index,
            _marker: PhantomData,
        }
    }

    /// Prepares the insertion of a `MayveUninit<T>` into the pool where
    /// `T` is the type described by the given `ObjectMeta` structure.
    ///
    /// ## Panics
    ///
    /// This function panics if the object described by `ObjectMeta` is a
    /// a zero-sized type.
    pub fn insert_raw(&mut self, meta: ObjectMeta) -> RawObjectHandle {
        let index = self.reserved_objects.len();
        self.reserved_objects.push(ReservedObject::uninit(meta));
        RawObjectHandle { index }
    }

    /// Builds a new `Stadium`.
    ///
    /// ## Panics
    ///
    /// This function can panics if one of the following events occure:
    ///  * The builder is empty
    ///  * The function fails to allocate for the pool
    pub fn build(self) -> Stadium {
        let objects = self.reserved_objects;
        let id = self.id;

        if objects.is_empty() {
            panic!("You cannot create a pool with no elements in it");
        }

        let mut total_size = 0;
        let mut max_align = 1;

        for obj in &objects {
            total_size += obj.meta.layout.size();
            max_align = Ord::max(max_align, obj.meta.layout.align());
        }

        let layout = Layout::from_size_align(total_size, max_align)
            .expect("Failed to compute the layout of the pool");

        // SAFETY: A `ReservedObject` cannot store a zero-sized type and we know the
        // `reserved_objects` vector is not empty. Therefor, `total_size` must be
        // non-null.
        let ptr =
            unsafe { NonNull::new(alloc(layout)).expect("Failed to allocate memory for the pool") };

        let object_count = objects.len();

        let mut sorted_vector: Vec<(usize, ReservedObject)> =
            objects.into_iter().enumerate().collect();

        // Sort the vector so that objects are sorted by align (ascending).
        sorted_vector.sort_unstable_by_key(|(_, o)| o.meta.layout.align());

        // We need this structure to map the handles that the builder has given
        // to actual objects within the pool.
        let mut locations: Vec<ObjectLocation> = Vec::with_capacity(object_count);

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
            // was given to the used through the `ObjectHandle`. This index will
            // be trusted by the `LocalPool` for the type of the object and for its
            // location.
            //
            // The `locations` vector was created with a capacity of `object_count`
            // The values of `original_index` are all differents and
            // `0 <= original_index < object_count`.
            unsafe {
                locations
                    .as_mut_ptr()
                    .add(original_index)
                    .write(ObjectLocation { meta, data: cursor });
            }

            // SAFETY: We own the data. A safety check will be done after the loop.
            cursor = unsafe { cursor.add(meta.layout.size()) };
        }

        // SAFETY: This vector was properly initialized inside the loop and has a
        // capacity of `object_count`.
        unsafe { locations.set_len(object_count) };

        // Safety check that should always pass
        assert_eq!(cursor as usize, ptr.as_ptr() as usize + total_size);

        // Now the pool is properly initialized.

        Stadium {
            id,
            data: ptr,
            layout,
            locations,
        }
    }
}

impl From<Builder> for Stadium {
    #[inline(always)]
    fn from(builder: Builder) -> Self {
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
    /// ## Safety
    ///
    /// * The given pointer must reference an initialized `T`.
    drop_fn: Option<unsafe fn(*mut u8)>,
}

impl ObjectMeta {
    /// Computes the `ObjectMeta` of the type `T`.
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

/// Stores information about a `T` as well as an initialized instance of `T`.
///
/// This structure never stores a zero-sized struct.
struct ReservedObject {
    /// Stores information about a `T`.
    meta: ObjectMeta,
    /// A pointer to an initialized value of type `T`.
    initial_value: NonNull<u8>,
}

impl ReservedObject {
    /// Creates a new instance of `ReservedObject` from the given initial value.
    ///
    /// ## Panics
    ///
    /// This function panics if `T` is a zero-sized type.

    // the static lifetime is there because we are going to drop the T without
    // owning any of the potential references it could have.
    fn new<T>(init: T) -> Self {
        let uninit = Self::uninit(ObjectMeta::of::<T>());

        // SAFETY: This pointer is not aliased anywhere and is properly aligned.
        // It is also know to not be initialized.
        unsafe {
            uninit
                .initial_value
                .as_ptr()
                .cast::<MaybeUninit<T>>()
                .write(MaybeUninit::new(init));
        };

        // The initial value is now properly initialized.
        // T is now `T` instead of `MaybeUninit<T>`.

        uninit // now init
    }

    /// Creates a new instance of `ReservedObject` for a `MaybeUninit<T>`
    /// where `T` is the type of the object described by the given `ObjectMeta`.
    ///
    /// ## Panics
    ///
    /// This function panics if `meta` describes a zero-sized type.
    fn uninit(meta: ObjectMeta) -> Self {
        if meta.layout.size() == 0 {
            panic!("You cannot put a zero-sized type into a `Stadium`");
        }

        let ptr = unsafe {
            // SAFETY: `T` is not a zero-sized type.
            NonNull::new(alloc(meta.layout)).expect("Failed to allocate memory for a `T`")
        };

        Self {
            initial_value: ptr.cast(),
            meta,
        }
    }

    /// Consumes `self` and turns it into its inner `T`. The value is written on the
    /// given pointer `target`.
    ///
    /// ## Safety
    ///
    /// `target` must be a valid location for an object of type `T` to be written on.
    unsafe fn consume(self, target: *mut u8) -> ObjectMeta {
        // SAFETY: We are moving the value referenced by `initial_value` to
        // `target`.
        ptr::copy_nonoverlapping(self.initial_value.as_ptr(), target, self.meta.layout.size());

        let meta = self.meta;

        // `self` mut not be dropped because this would cause the value at `initial_value`
        // to be dropped even though it was moved.
        mem::forget(self);

        meta
    }
}

impl Drop for ReservedObject {
    fn drop(&mut self) {
        // We have to drop the initial value that was not used.
        if let Some(drop_fn) = self.meta.drop_fn {
            // SAFETY: The value is known to be initialized.
            unsafe { drop_fn(self.initial_value.as_ptr()) };
        }

        // SAFETY: The layout was used to allocate the `T` in `Self::new` and the value
        // that was here was properly dropped beforehand.
        unsafe { dealloc(self.initial_value.as_ptr(), self.meta.layout) };
    }
}

/// A safe handle to a specific object stored in a specific `Stadium`. This handle can
/// be optained from the `Builder::insert` function.
#[derive(PartialEq, Eq, Hash, Debug)]
pub struct ObjectHandle<T> {
    /// The id of the pool this handle exist for.
    id: usize,
    /// The index of the location of the object referenced by this handle.
    index: usize,

    // Invariant T owned by this handle.
    _marker: PhantomData<*mut T>,
}

impl<T> Clone for ObjectHandle<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            index: self.index,
            _marker: PhantomData,
        }
    }
}

impl<T> Copy for ObjectHandle<T> {}

impl<T> ObjectHandle<T> {
    /// Converts this `ObjectHandle` into a `RawObjectHandle`.
    ///
    /// ## Example
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    /// let raw_handle = builder.insert("Hello").raw();
    /// ```
    #[inline(always)]
    pub fn raw(self) -> RawObjectHandle {
        RawObjectHandle { index: self.index }
    }
}

/// A handle to a `T` that does not own a `T`. This handle dos not remember
/// what stadium created it.
pub struct RawObjectHandle {
    /// The index of the location of the object referenced by this handle.
    index: usize,
}

impl RawObjectHandle {
    /// Recreate an `ObjectHandle` from this `RawObjectHandle`.
    ///
    /// ## Safety
    ///
    ///  * The generic type parameter `T` must be the same as the original `ObjectHandle`
    /// that was used to produce this `RawObjectHandle`.
    ///  * The given `Stadium` must be the one associated with the original handle.
    ///
    /// ## Example
    ///
    /// ```rust
    /// let mut builder = stadium::builder();
    /// let handle = builder.insert(5i32);
    /// let stadium = builder.build();
    ///
    /// let raw_handle = handle.raw();
    ///
    /// // SAFETY: The handle was given by the builder that created the pool and was
    /// // created for a `i32`.
    /// let handle = unsafe { raw_handle.trust::<i32>(&stadium) };
    ///
    /// assert_eq!(stadium[handle], 5);
    /// ```
    #[inline(always)]
    pub unsafe fn trust<T>(self, stadium: &Stadium) -> ObjectHandle<T> {
        ObjectHandle {
            index: self.index,
            id: stadium.id,
            _marker: PhantomData,
        }
    }

    /// Recreate an `ObjectHandle` from this `RawObjectHandle`.
    ///
    /// ## Safety
    ///
    ///  * The generic type parameter `T` must be the same as the original `ObjectHandle`
    /// that was used to produce this `RawObjectHandle`.
    ///  * The given `Builder` must be the one associated with the original handle.
    ///
    /// ## Example
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
    #[inline(always)]
    pub unsafe fn trust_with_builder<T>(self, builder: &Builder) -> ObjectHandle<T> {
        ObjectHandle {
            index: self.index,
            id: builder.id,
            _marker: PhantomData,
        }
    }
}
