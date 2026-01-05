/-- 数胞类型，简写为 NC_n
    n: 状态数
    val: 当前值，保证在 [0, n-1] 范围内
-/
structure NumericalCell (n : Nat) where
    hpos : n > 0
    val : Fin n
    deriving Repr, DecidableEq

/-- NC 的缩写 -/
abbrev NC (n : Nat) := NumericalCell n

/-- 有符号数胞类型，简写为 SNC_n
    n: 状态数
    val: 当前值，保证在 [0, n-1] 范围内
-/
structure SignedNumericalCell (n : Nat) where
    hpos : n > 0
    val : Fin n
    deriving Repr, DecidableEq

/-- SNC 的缩写 -/
abbrev SNC (n : Nat) := SignedNumericalCell n

/-- 创建 NC_n 实例，需要证明 n > 0 -/
def NC.mk (n : Nat) (h : n > 0) (value : Nat) : NC n :=
    let val := value % n
    have h_val : val < n := Nat.mod_lt value h
    ⟨h, ⟨val, h_val⟩⟩

/-- 创建 SNC_n 实例，需要证明 n > 0 -/
def SNC.mk (n : Nat) (h : n > 0) (value : Int) : SNC n :=
    let temp := (value % n).toNat
    let val := temp % n
    have h_val : val < n := Nat.mod_lt temp h
    ⟨h, ⟨val, h_val⟩⟩

/-- 构建一个新的数胞，其状态数由 x 指定，值为 b 的值限制在 [0, x-1] 内 -/
def NC.transfer {n : Nat} (x : Nat) (h : x > 0) (b : NC n) : NC x :=
    let val := b.val.val % x
    have h_val : val < x := by
        -- 需要证明 val < x
        exact Nat.mod_lt b.val.val h
    ⟨h, ⟨val, h_val⟩⟩

/-- 构建一个新的数胞，其新值由 x 指定，限制在 [0, n-1] 内 -/
def NC.assign {n : Nat} (nc : NC n) (x : Nat) : NC n :=
    let val := x % n
    have h_val : val < n := by
        -- 需要证明 x < n
        exact Nat.mod_lt x nc.hpos
    ⟨nc.hpos, ⟨val, h_val⟩⟩

/-- 获取当前值（Nat 形式） -/
def NC.toNat {n : Nat} (c : NC n) : Nat := c.val.val

/-- 将数胞值转换为整数
    规则：0 到 ⌊(n-1)/2⌋ 映射到 0 到 ⌊(n-1)/2⌋
          ⌊(n-1)/2⌋+1 到 n-1 映射到 -⌈(n-1)/2⌉ 到 -1
    当 n 为奇数时，正负对称
    当 n 为偶数时，正数部分多一个（包括0） -/
def NC.toInt {n : Nat} (c : NC n) : Int :=
    let v := c.val.val
    let half := (n - 1) / 2
    if v <= half then
        v
    else
        (v : Int) - (n : Int)

/-- 获取当前状态数（Nat 形式） -/
def NC.NumberOfStates {n : Nat} (_ : NC n) : Nat := n

/-- 模 n 加法 -/
protected def NC.add {n : Nat} (a b : NC n) : NC n :=
    let sum := a.val + b.val
    ⟨a.hpos, sum⟩

/-- 模 n 减法 -/
protected def NC.sub {n : Nat} (a b : NC n) : NC n :=
    let dif := a.val - b.val
    ⟨a.hpos, dif⟩

/-- 模 n 乘法 -/
protected def NC.mul {n : Nat} (a b : NC n) : NC n :=
    let pro := a.val * b.val
    ⟨a.hpos, pro⟩

/-- 数胞的模除法（返回商，结果仍在同一模数下）-/
def NC.div {n : Nat} (a b : NC n) : NC n :=
    -- 在整数中计算 a.val.val / b.val.val，再取模n
    -- 但需要确保b.val.val ≠ 0
    if h : b.val.val = 0 then
        ⟨a.hpos, ⟨0, a.hpos⟩⟩
    else
        let quotient : Nat := a.val.val / b.val.val
        let quotient_mod_n : Fin n := ⟨quotient % n, by
            have : n > 0 := a.hpos
            exact Nat.mod_lt quotient this⟩
        ⟨a.hpos, quotient_mod_n⟩

/-- 数胞的模取模（返回余数，结果仍在同一模数下）-/
def NC.mod {n : Nat} (a b : NC n) : NC n :=
    if h : b.val.val = 0 then
        a
    else
        let remainder : Nat := a.val.val % b.val.val
        let remainder_mod_n : Fin n := ⟨remainder % n, by
            have : n > 0 := a.hpos
            exact Nat.mod_lt remainder this⟩
        ⟨a.hpos, remainder_mod_n⟩

instance {n : Nat} : Add (NC n) := ⟨NC.add⟩
instance {n : Nat} : Sub (NC n) := ⟨NC.sub⟩
instance {n : Nat} : Mul (NC n) := ⟨NC.mul⟩
instance {n : Nat} : Div (NC n) := ⟨NC.div⟩
instance {n : Nat} : Mod (NC n) := ⟨NC.mod⟩

/-- 转换为有符号数胞 -/
def NC.toSNC {n : Nat} (c : NC n) : SNC n :=
    SNC.mk n c.hpos c.toNat

/-- 转换为字符串 -/
def NC.toString {n : Nat} (c : NC n) : String :=
    s!"NC_{n}({c.val.val})"

instance {n : Nat} : ToString (NC n) := ⟨NC.toString⟩




/-- 构建一个新的有符号数胞，其新值由 x 指定 -/
def SNC.assign {n : Nat} (nc : NC n) (x : Int) : SNC n :=
    let t := (x % n).toNat
    let val := t % n
    have h_val : val < n := by
        -- 需要证明 x < n
        exact Nat.mod_lt t nc.hpos
    ⟨nc.hpos, ⟨val, h_val⟩⟩

/-- 构建一个新的有符号数胞，其状态数由 x 指定 -/
def SNC.transfer {n : Nat} (x : Nat) (h : x > 0) (b : SNC n) : SNC x :=
    let val := b.val.val % x
    have h_val : val < x := by
        -- 需要证明 val < x
        exact Nat.mod_lt b.val.val h
    ⟨h, ⟨val, h_val⟩⟩

/-- 获取当前值（Nat 形式） -/
def SNC.toNat {n : Nat} (c : SNC n) : Nat := c.val.val

/-- 将数胞值转换为整数
    规则：0 到 ⌊(n-1)/2⌋ 映射到 0 到 ⌊(n-1)/2⌋
          ⌊(n-1)/2⌋+1 到 n-1 映射到 -⌈(n-1)/2⌉ 到 -1
    当 n 为奇数时，正负对称
    当 n 为偶数时，正数部分多一个（包括0） -/
def SNC.toInt {n : Nat} (c : SNC n) : Int :=
    let v := c.val.val
    let half := (n - 1) / 2
    if v <= half then
        v
    else
        (v : Int) - (n : Int)

/-- 获取当前状态数（Nat 形式） -/
def SNC.NumberOfStates {n : Nat} (_ : NC n) : Nat := n

/-- 模 n 加法 -/
protected def SNC.add {n : Nat} (a b : SNC n) : SNC n :=
    let sum := a.val + b.val
    ⟨a.hpos, sum⟩

/-- 模 n 减法 -/
protected def SNC.sub {n : Nat} (a b : SNC n) : SNC n :=
    let dif := a.val - b.val
    ⟨a.hpos, dif⟩

/-- 模 n 乘法 -/
protected def SNC.mul {n : Nat} (a b : SNC n) : SNC n :=
    let pro := a.val * b.val
    ⟨a.hpos, pro⟩

/-- 有符号数胞的模除法（返回商，结果仍在同一模数下）-/
def SNC.div {n : Nat} (a b : SNC n) : SNC n :=
    -- 在整数中计算 a.val.val / b.val.val，再取模n
    -- 但需要确保b.val.val ≠ 0
    if h : b.val.val = 0 then
        ⟨a.hpos, ⟨0, a.hpos⟩⟩
    else
        let a_val : Int := a.toInt
        let b_val : Int := b.toInt
        let quotient : Int := a_val / b_val
        let limited : Nat := (quotient % n).toNat
        let quotient_mod_n : Fin n := ⟨limited % n, by
            have : n > 0 := a.hpos
            exact Nat.mod_lt limited this⟩
        ⟨a.hpos, quotient_mod_n⟩

/-- 有符号数胞的模取模（返回余数，结果仍在同一模数下）-/
def SNC.mod {n : Nat} (a b : SNC n) : SNC n :=
    if h : b.val.val = 0 then
        a
    else
        let a_val : Int := a.toInt
        let b_val : Int := b.toInt
        let remainder : Int := a_val % b_val
        let limited : Nat := (remainder % n).toNat
        let remainder_mod_n : Fin n := ⟨limited % n, by
            have : n > 0 := a.hpos
            exact Nat.mod_lt limited this⟩
        ⟨a.hpos, remainder_mod_n⟩

instance {n : Nat} : Add (SNC n) := ⟨SNC.add⟩
instance {n : Nat} : Sub (SNC n) := ⟨SNC.sub⟩
instance {n : Nat} : Mul (SNC n) := ⟨SNC.mul⟩
instance {n : Nat} : Div (SNC n) := ⟨SNC.div⟩
instance {n : Nat} : Mod (SNC n) := ⟨SNC.mod⟩

/-- 转换为无符号数胞 -/
def SNC.toNC {n : Nat} (c : SNC n) : NC n :=
    NC.mk n c.hpos c.toNat

/-- 转换为字符串 -/
def SNC.toString {n : Nat} (c : SNC n) : String :=
    let temp : Int := c.val.val
    let half := (n - 1) / 2
    let val : Int := if temp <= half then temp else temp - n
    s!"SNC_{n}({val})"

instance {n : Nat} : ToString (SNC n) := ⟨SNC.toString⟩
