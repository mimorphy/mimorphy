structure bit_reference where
    byte_ptr_ : Option UInt8
    bit_pos_ : UInt64

/- 逻辑右移，当位移量 ≥ 8 时结果为 0 -/
def logical_shift_right (x : UInt8) (n : UInt64) : UInt8 :=
    if n ≥ 8 then 0 else x >>> n.toUInt8

/- 逻辑左移，当位移量 ≥ 8 时结果为 0，左移时高位丢弃 -/
def logical_shift_left (x : UInt8) (n : UInt64) : UInt8 :=
    if n ≥ 8 then 0 else x <<< n.toUInt8

def bit_reference.initial (byte_ptr : Option UInt8) (bit_pos : UInt64) : bit_reference := Id.run do
    return ⟨byte_ptr, bit_pos⟩

def bit_reference.to_bool (self : bit_reference) : UInt8 := Id.run do
    return (logical_shift_right self.byte_ptr_.get! self.bit_pos_) &&& 1

def bit_reference.equal (self : bit_reference) (value : UInt8) : bit_reference × Option UInt8 := Id.run do
    let mut _self := self
    if value ≠ 0 then
        _self := { _self with byte_ptr_ := some (self.byte_ptr_.get! ||| (logical_shift_left 1 _self.bit_pos_)) }
    else
        _self := { _self with byte_ptr_ := some (self.byte_ptr_.get! &&& ~~~(logical_shift_left 1 _self.bit_pos_)) }
    return (_self, _self.byte_ptr_)

def bit_reference.assign (self : bit_reference) (other : bit_reference) : bit_reference × Option UInt8 := Id.run do
    let mut _self := self
    _self := (_self.equal other.to_bool).1
    return (_self, _self.byte_ptr_)

def bit_reference.flip (self : bit_reference) : Option UInt8 := Id.run do
    let mut _self := self
    _self := { _self with byte_ptr_ := some (self.byte_ptr_.get! ^^^ (logical_shift_left 1 _self.bit_pos_)) }
    return _self.byte_ptr_
