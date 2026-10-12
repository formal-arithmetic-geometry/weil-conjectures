module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Picard.Group
import Sheaf.AlgebraicGeometry.Curve.PicardDecomposition
import Sheaf.AlgebraicGeometry.Curve.ProperProjective
import Sheaf.AlgebraicGeometry.SmoothProjectiveCurve
import Sheaf.AlgebraicGeometry.Variety
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.Regular
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry
/-- The prime-to-characteristic Picard torsion for a proper smooth curve.
Source: blueprint `lem-sc-pic-proper-ntorsion`, the Jacobian calculation.
(blueprint: lem-sc-pic-proper-ntorsion-torsion)

Proof in words: The connected curve has dimension one, so properness gives projectivity by
`isProjective_of_isProper_of_dim_le_one`. Smoothness gives regular local rings, hence
domains. Finite type over a field gives Noetherianity; distinct irreducible components
are disjoint because the local rings are domains, and there are finitely many components.
They are therefore open as well as closed, so connectedness gives integrality.
Smoothness and nonemptiness over the algebraically closed field give a rational point;
the integral smooth curve with that point is geometrically integral. The curve is thus
a smooth projective geometrically integral curve to which Jacobian representability
applies. Its degree-zero Picard subgroup is isomorphic, as a group, to the rational points
of its Jacobian. Serre duality identifies the arithmetic genus used for the Jacobian's
dimension with `f.genus`.
The hypothesis `(n : k) ≠ 0` implies n > 0 and that the characteristic does not divide n.
Clause (c) of the abelian-variety estimate identifies the nth-torsion of the Jacobian's
points with `(ZMod n)^(2 * f.genus)`. Under the Picard decomposition
`Pic(C) ≃ ℤ × Pic⁰(C)`, an nth-torsion element has integer coordinate d with n*d = 0.
Since n > 0, d = 0. Thus projection onto Pic⁰(C) identifies Pic(C)[n] with Pic⁰(C)[n],
and the Jacobian group equivalence identifies the latter with the computed torsion group.
Write the final additive group multiplicatively to obtain exactly the displayed kernel
isomorphism. For n = 1 both torsion groups are trivial; for genus zero the finite function
group is trivial as well. -/
theorem Scheme.Hom.pic_proper_ntorsion_torsion
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (_hn : (n : k) ≠ 0) :
    Nonempty ((powMonoidHom n : C.Pic →* C.Pic).ker ≃*
      Multiplicative (Fin (2 * f.genus) → ZMod n)) := by sorry
end AlgebraicGeometry
