import Mathlib.Tactic
import core.bit_span

/- 输入值 n, 位索引 pos (从0开始). 输出 n 以 2 为进制的第 pos 位值 -/
def bit (n : Nat) (pos : Nat) : UInt8 :=
    ((n / 2 ^ pos) % 2).toUInt8
