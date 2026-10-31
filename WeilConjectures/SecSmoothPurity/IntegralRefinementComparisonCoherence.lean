/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactificationRefinementLocalizing
public import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
public import WeilConjectures.AlgebraicGeometry.CondensedFlatCoefficientCalculus
import all WeilConjectures.AlgebraicGeometry.CondensedFlatCoefficientCalculus

/-!
# Coherence of integral refinement comparisons

Source: Def. 6.7.6 / Lemma 6.7.7 of Bhatt--Scholze, with the
Hom-uniqueness route through the open-extension adjunction.
(blueprint: lem-pur-integral-refinement-comparison-coherence)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

attribute [local instance 3000] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory
attribute [local instance 2000] CategoryTheory.scalarTensor4 CategoryTheory.scalarTensor12
  CategoryTheory.scalarTensor23 CategoryTheory.scalarTensorColimits
  CategoryTheory.scalarFlipTensorColimits

namespace AlgebraicGeometry.ProEtale.CondensedRing

/--
For integral coefficients, the canonical refinement maps are coherent under composition and
normalized on identity refinements.  The compositor is the canonical derived direct-image
compositor, expressed here in the orientation from the composite direct image to the iterated
one; its inverse is the `c` used in the statement of the node.

Source: Bhatt--Scholze, arXiv 1309.1198, Def. 6.7.6 / Lemma 6.7.7 (Hom-uniqueness by the
`j_! ⊣ j^*` adjunction); blueprint sk-thm-purity-transport, proof Step 3,
compactification-independence sentence (expert re-plan #1267)
(blueprint: lem-pur-integral-refinement-comparison-coherence).

The maps are the canonical adjoint maps `localizingRefinementMap`, so their restriction to the
open is the identity.  Equality is the Hom-bijection uniqueness statement and does not use
coefficient reduction.

Proof, following the node:
1. Write `J = j_!`, `J' = j'_!`, `J'' = j''_!` and `u_j : j^* J ≅ 1` for the inverse open
   units.  The canonical open restrictions give `ρ_h : j^* Rh_* ≅ j'^*`,
   `ρ_k : j'^* Rk_* ≅ j''^*` and `ρ_{hk} : j^* R(hk)_* ≅ j''^*`, since the restricted maps
   are `1_X` (`h⁻¹(X) = k⁻¹(X) = X`) and `R(1_X)_*` is the identity.  The composite `hk` is
   proper with `(hk) j'' = j` and `(hk)⁻¹(X) = X`, so `α_{hk}` is defined.  The defining
   Hom bijection gives `u_{j'} ρ_h j^*(α_h) = u_j`, `u_{j''} ρ_k j'^*(α_k) = u_{j'}` and
   `u_{j''} ρ_{hk} j^*(α_{hk}) = u_j`.
2. With `c : Rh_* Rk_* ≅ R(hk)_*` the inverse of the canonical compositor, the mixed
   open-restriction/composition compatibility gives `ρ_{hk} j^*(c) = ρ_k ρ_{h, Rk_*}`; the
   restricted compositor of `1_X, 1_X` is the identity by the unital clause.
3. Put `b = c ∘ Rh_*(α_k) ∘ α_h`.  Naturality of `ρ_h` at `α_k`, Step 2 and the equations
   of Step 1 give `u_{j''} ρ_{hk} j^*(b) = u_j`.  So `b` and `α_{hk}` have the same image
   `1_K` under the defining Hom bijection, and its injectivity gives `b = α_{hk}`, for every
   unbounded `K`, without invertibility of either comparison.
4. For the identity refinement the identity direct-image identification carries the target to
   `j_! K`, and the normalized identity restriction is the identity, so `1_{j_! K}` goes to
   `1_K`.  Injectivity of the Hom bijection gives `α_id = 1`.
-/
theorem integralRefinementComparisonCoherence
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d e : Compactification.BoundaryCompactification f}
    (r : d ⟶ c) (s : e ⟶ d)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) :
    localizingRefinementMap (Profinite.padicIntegersRingObj ℓ E.1) (s ≫ r) K =
        (localizingRefinementMap (Profinite.padicIntegersRingObj ℓ E.1) r K ≫
          (lowerStar (Profinite.padicIntegersRingObj ℓ E.1) r.hom.hom.hom).rightDerivedFunctor.map
            (localizingRefinementMap (Profinite.padicIntegersRingObj ℓ E.1) s K)) ≫
          (refinementDerivedLowerStarComp (Profinite.padicIntegersRingObj ℓ E.1)
            s.hom.hom.hom r.hom.hom.hom).inv.app
            ((openImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E.1)
              e.obj.obj.i).mapDerivedCategory.obj K) ∧
      localizingRefinementMap (Profinite.padicIntegersRingObj ℓ E.1) (𝟙 c) K ≫
          (refinementDerivedLowerStarId (Profinite.padicIntegersRingObj ℓ E.1)
            c.obj.obj.Z).hom.app
            ((openImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E.1)
              c.obj.obj.i).mapDerivedCategory.obj K) = 𝟙 _ := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
