module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension
import Sheaf.AlgebraicGeometry.Curve.EtaleSheafHLargeFilteredColimit
import Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import Sheaf.Paper.ZeroDimensionalEtaleCohomologyRest

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))

/-- Degree-two vanishing for the constant sheaf with arbitrary coefficients `Λ/pΛ`.
Source: blueprint `sec-proper-base-change/sk-thm-p1/lem-sc-c3`, via
`sec-curve-estimates/sk-prop-cd/lem-sc-artin-schreier-dimension` and the filtered-colimit
extension of constant coefficients (Stacks Project, Tags 0A3N, 03Q5 and 0739).
(blueprint: lem-sc-c3-degree-two)

Proof: The curve is quasi-compact and quasi-separated, since it is separated and of
finite type over a field. First suppose its dimension is zero. Smoothness makes its
finite coordinate algebras reduced, so a connected zero-dimensional such scheme over
an algebraically closed field is `Spec k`. Choose its geometric point over k and apply
`zero_dimensional_etale_cohomology_rest` in degree two to the underlying abelian sheaf.
The comparison `nonempty_sheafH_extDerivedIso` transfers this to Ext cohomology.

In dimension one the hypotheses give `IsConnectedCurve f`. Apply
`isZero_etaleCohomology_constantZMod_of_one_lt_of_charP` with q = 2. Its proof uses
Artin--Schreier: H² is the cokernel of F - 1 on H¹(O). For an affine curve H¹(O) = 0;
for a proper curve this is finite-dimensional and Lang--Steinberg makes F - 1
surjective. The Ext/derived comparison `nonempty_sheafH_extDerivedIso` therefore
identifies H² of the underlying constant ZMod p sheaf with a zero group.

Now put M = Λ/pΛ. It is an F_p-vector space, even when Λ has characteristic different
from p; if M is zero there is nothing to prove. Express M as the filtered union of
its finite-dimensional F_p-subspaces, indexed in Type (u + 1). A basis identifies each
such subspace, additively, with a finite direct sum of ZMod p. Constant sheafification
preserves these colimits, and forgetting the coefficient module structure preserves
them (its sheaf functor is a left adjoint). Thus the underlying sheaf in the conclusion
is the filtered colimit of finite direct sums of the constant ZMod p sheaf. Additivity
of Sheaf.functorH makes H² of each finite sum zero. Finally
`sheafH_isColimit_large_filtered` applies to this qcqs curve and this index universe:
H² of the filtered colimit is a colimit of zero groups and hence zero. This also
covers the zero ring and arbitrarily large coefficient rings. -/
theorem subsingleton_sheafH_constantModSheaf_of_charP_two [IsCurve f] [Smooth f]
    [ConnectedSpace C] (p : ℕ) [Fact p.Prime] [CharP k p] :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C p)) 2) := by
  sorry

end AlgebraicGeometry.IsCurve
