module

public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf

@[expose] public section

namespace AlgebraicGeometry.Scheme

/-- Positive integers with the divisibility order, the canonical torsion-filtration index. -/
abbrev PositiveNat := PNat.DvdOrder

/-- Positivity of the torsion-filtration index. -/
theorem PositiveNat.pos (n : PositiveNat) : 0 < n.val := PNat.DvdOrder.val_pos n

end AlgebraicGeometry.Scheme
