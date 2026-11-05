/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback

/-!
# Invertibility of the exceptional base change map at the unit is Zariski local (A1', step 1)

Let `f : X ⟶ Y` over `k₁`, `f' : X' ⟶ Y'` over `k₂`, `bc : Rf_! ⋙ πY^* ≅ πX^* ⋙ Rf'_!` and
`e : πY^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` as in `ProEtale.CondensedRing.smoothUnitBaseChange`. Let `jᵢ : Uᵢ ⟶ X`
be open immersions, `jᵢ' : Uᵢ' ⟶ X'` open immersions covering `X'` (in practice the base changes
of the `jᵢ`, which cover `X'` as soon as the `jᵢ` cover `X`), with compact-support base change
isomorphisms `bcjᵢ : Rjᵢ_! ⋙ πX^* ≅ πUᵢ^* ⋙ Rjᵢ'_!` whose mates `πUᵢ^* Rjᵢ^! ⟶ Rjᵢ'^! πX^*` are
invertible (the open-immersion case of step 2). Then `smoothUnitBaseChange` of `f` is invertible
as soon as the ones of the restrictions `jᵢ ≫ f` (with the pasted base change isomorphisms) are
(`isIso_smoothUnitBaseChange_of_openCover`).

Proof: by the pasting of step 3 (`isIso_smoothUnitBaseChange_comp_iff`), the exceptional base
change map of `jᵢ ≫ f` is, up to isomorphisms, `Rjᵢ'^!` of the one of `f`; `Rjᵢ'^! ≅ jᵢ'^*` for
an open immersion (`boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl`), and the pullbacks
to the members of a (pro-étale, here Zariski) cover jointly reflect isomorphisms
(`isIso_of_forall_isIso_leftDerivedUpperStar_map`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Local

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y')
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}
  (bc : boundedConstructibleLowerShriek l f ⋙ boundedConstructibleUpperStarOfMap l πY ≅
    boundedConstructibleUpperStarOfMap l πX ⋙ boundedConstructibleLowerShriek l f')
  (e : (boundedConstructibleUpperStarOfMap l πY).obj (𝟙_ _) ⟶ 𝟙_ _)
  {ι : Type u} {U : ι → Over (Spec (.of k₁))}
  [∀ i, LocallyOfFiniteType (U i).hom] [∀ i, QuasiCompact (U i).hom]
  [∀ i, IsSeparated (U i).hom]
  {U' : ι → Over (Spec (.of k₂))}
  [∀ i, LocallyOfFiniteType (U' i).hom] [∀ i, QuasiCompact (U' i).hom]
  [∀ i, IsSeparated (U' i).hom]
  (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i).left]
  (j' : ∀ i, U' i ⟶ X') [∀ i, IsOpenImmersion (j' i).left]
  {πU : ∀ i, (U' i).left ⟶ (U i).left}
  (bcj : ∀ i, boundedConstructibleLowerShriek l (j i) ⋙ boundedConstructibleUpperStarOfMap l πX ≅
    boundedConstructibleUpperStarOfMap l (πU i) ⋙ boundedConstructibleLowerShriek l (j' i))

end Local

end AlgebraicGeometry.ProEtale.CondensedRing
