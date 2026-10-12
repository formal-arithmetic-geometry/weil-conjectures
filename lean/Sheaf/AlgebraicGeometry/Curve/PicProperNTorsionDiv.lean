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
/-- Degree-zero Picard divisibility for a proper smooth curve.
Source: blueprint `lem-sc-pic-proper-ntorsion`, the Jacobian calculation.
(blueprint: lem-sc-pic-proper-ntorsion-div)

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
The hypothesis `(n : k) ≠ 0` excludes n = 0, hence n is positive. Clause (d) of the
abelian-variety estimate says the nth-power map on the Jacobian's rational points is
surjective. For a degree-zero class L, take an nth root of its image in the Jacobian and
transport that root back along the group equivalence. It is a degree-zero class M;
the homomorphism property and injectivity of the equivalence give M ^ n = L.
For n = 1 one can take M = L. -/
theorem Scheme.Hom.pic_proper_ntorsion_div
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (_hn : (n : k) ≠ 0) :
    ∀ L : C.Pic, L ∈ f.picZero → ∃ M : C.Pic, M ∈ f.picZero ∧ M ^ n = L := by sorry
end AlgebraicGeometry
