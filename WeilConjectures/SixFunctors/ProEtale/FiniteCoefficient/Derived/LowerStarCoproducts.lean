/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimensionAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Localization

/-!
# Pro-étale direct images commute with coproducts of complexes of étale origin

Let `Λ` be a finite ring and `p : Z ⟶ Y` a morphism between finite-type `k`-schemes. On the
pro-étale derived categories, the direct image `Rp_*` does not commute with coproducts in general
(`not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety`).
It does on complexes with cohomology sheaves of étale origin, when `p` is proper:

* `Rp_*` has finite amplitude on such complexes
  (`AlgebraicGeometry.ProEtale.exists_isLE_rightDerivedLowerStar_of_etaleOriginHomology`): on a
  bounded one, which is `ν^* G` for a bounded étale complex `G`, it is `ν^* Rp_*^{ét} G`, and
  `Rp_*^{ét}` has finite cohomological dimension; an arbitrary one is the homotopy limit of its
  truncations `τ_{≥ -n}`, the pro-étale derived category being left complete
  (`DerivedCategory.isHomotopyLimit_truncGECone`);
* on uniformly bounded families it commutes with coproducts, since `Rp_*^{ét}` does for proper
  `p` (`AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerivedLowerStar_of_isProper`) and
  `ν^*` preserves coproducts;
* hence it commutes with all coproducts of complexes with cohomology of étale origin
  (`AlgebraicGeometry.ProEtale.isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology`,
  by `DerivedCategory.isIso_sigmaComparison_of_bounded`).

This is the finite-coefficient direct-sum statement of blueprint `sk-prop-ctf-finite-proper`
(`det-ctf-finite-proper-localizing`), in the form used by `det-sf-comp-coherence-single`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme _root_.DerivedCategory.TStructure

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

end AlgebraicGeometry.ProEtale
