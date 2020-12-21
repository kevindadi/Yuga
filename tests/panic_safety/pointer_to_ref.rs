/*!
```rudra-test
test_type = "normal"
expected_analyzers = ["PanicSafety"]
```
!*/

use std::fmt::Debug;

fn test_order_unsafe<I: Iterator<Item = impl Debug>>(mut iter: I) {
    unsafe {
        let _ = &*(1234 as *const i32);
    }
    println!("{:?}", iter.next());
}
