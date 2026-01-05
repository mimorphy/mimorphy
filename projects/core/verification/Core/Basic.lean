import Core.NumericalCell

abbrev SNC8 := SNC 0x100
abbrev SNC16 := SNC 0x10000
abbrev SNC32 := SNC 0x100000000
abbrev SNC64 := SNC 0x10000000000000000
abbrev SNCMin := SNC 0x100
abbrev SNCMax := SNC 0x10000000000000000
abbrev NC8 := NC 0x100
abbrev NC16 := NC 0x10000
abbrev NC32 := NC 0x100000000
abbrev NC64 := NC 0x10000000000000000
abbrev NCMin := NC8
abbrev NCMax := NC64
abbrev SizeValue := NCMax
abbrev Float64 := Float
abbrev Address := SizeValue
abbrev Byte := NCMin

def Int8Max : SNCMax := SNC.mk 0x10000000000000000 (by decide) 0x7FFFFFFFFFFFFFFF
def Int16Max : SNCMax := SNC.mk 0x10000000000000000 (by decide) 0x7FFF
def Int32Max : SNCMax := SNC.mk 0x10000000000000000 (by decide) 0x7FFFFFFF
def Int64Max : SNCMax := SNC.mk 0x10000000000000000 (by decide) 0x7FFFFFFFFFFFFFFF
def IntMinMax : SNCMax := SNC.mk 0x10000000000000000 (by decide) 0x7F
def IntMaxMax : SNCMax := SNC.mk 0x10000000000000000 (by decide) 0x7FFFFFFFFFFFFFFF
def Nat8Max : NCMax := NC.mk 0x10000000000000000 (by decide) 0xFF
def Nat16Max : NCMax := NC.mk 0x10000000000000000 (by decide) 0xFFFF
def Nat32Max : NCMax := NC.mk 0x10000000000000000 (by decide) 0xFFFFFFFF
def Nat64Max : NCMax := NC.mk 0x10000000000000000 (by decide) 0xFFFFFFFFFFFFFFFF
def NatMinMax : NCMax := NC.mk 0x10000000000000000 (by decide) 0xFF
def NatMaxMax : NCMax := NC.mk 0x10000000000000000 (by decide) 0xFFFFFFFFFFFFFFFF
def SizeValueMax : SizeValue := NC.mk 0x10000000000000000 (by decide) 0xFFFFFFFFFFFFFFFF
def AddressMax : Address := NatMaxMax
def CharacterMax := 0xFFFFFFFF

def Int8Min : SNCMax := SNC.mk 0x10000000000000000 (by decide) (-128)
def Int16Min : SNCMax := SNC.mk 0x10000000000000000 (by decide) (-32768)
def Int32Min : SNCMax := SNC.mk 0x10000000000000000 (by decide) (-2147483648)
def Int64Min : SNCMax := SNC.mk 0x10000000000000000 (by decide) (-9223372036854775808)
def IntMinMin : SNCMax := Int8Min
def IntMaxMin : SNCMax := Int64Min

def BASE := 2
def BYTE_LENGTH := 8
def WORD_SIZE := 8
