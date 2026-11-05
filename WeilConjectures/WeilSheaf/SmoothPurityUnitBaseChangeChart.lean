/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeLocal
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeProper

/-!
# The exceptional base change map at the unit on a chart of the étale normal form (A1')

Formal consequences of the pasting law (`smoothUnitBaseChange_comp`) used in the local proof of
`IsIso smoothUnitBaseChange` for a smooth non-proper `f`:

* `isIso_smoothUnitBaseChange_iff_isIso_mate_app`: for `e` invertible, the exceptional base
  change map at the unit is invertible iff the mate of `bc` is invertible at the unit;
* `isIso_smoothUnitBaseChange_comp_openImmersion_right_iff` (**locality on the base**): for an
  open immersion `jV : V ⟶ Y` whose exceptional base change map at the unit is invertible, the
  one of `fV ≫ jV` is invertible iff the one of `fV : XV ⟶ V` is;
* `isIso_smoothUnitBaseChange_chart`: on a chart `U --g--> A --jA--> P --p--> V --jV--> Y`
  (`g` étale, `jA` an open immersion, `p` the projection of a projective space, `jV` an open
  immersion), the exceptional base change map at the unit of the composite is invertible as soon
  as the mates of `bcg` and `bcjA` are invertible (step 2), the one of `jV` is invertible (open
  unit case of step 2) and the one of `p` is (the proper piece,
  `isIso_smoothUnitBaseChange_of_projectiveSpace_of_weaklyEtale`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Unit

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

end Unit

section Base

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {XV V Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType XV.hom] [QuasiCompact XV.hom] [IsSeparated XV.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {XV' V' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType XV'.hom] [QuasiCompact XV'.hom] [IsSeparated XV'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (fV : XV ⟶ V) (jV : V ⟶ Y) [IsOpenImmersion jV.left] (fV' : XV' ⟶ V') (jV' : V' ⟶ Y')
  [IsOpenImmersion jV'.left]
  {πXV : XV'.left ⟶ XV.left} {πV : V'.left ⟶ V.left} {πY : Y'.left ⟶ Y.left}
  (bcf : boundedConstructibleLowerShriek l fV ⋙ boundedConstructibleUpperStarOfMap l πV ≅
    boundedConstructibleUpperStarOfMap l πXV ⋙ boundedConstructibleLowerShriek l fV')
  (bcj : boundedConstructibleLowerShriek l jV ⋙ boundedConstructibleUpperStarOfMap l πY ≅
    boundedConstructibleUpperStarOfMap l πV ⋙ boundedConstructibleLowerShriek l jV')
  (eY : (boundedConstructibleUpperStarOfMap l πY).obj (𝟙_ _) ⟶ 𝟙_ _)
  (eV : (boundedConstructibleUpperStarOfMap l πV).obj (𝟙_ _) ⟶ 𝟙_ _)

end Base

section Chart

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {U A P V Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {U' A' P' V' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
  [LocallyOfFiniteType A'.hom] [QuasiCompact A'.hom] [IsSeparated A'.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (g : U ⟶ A) (jA : A ⟶ P) (p : P ⟶ V) (jV : V ⟶ Y)
  (g' : U' ⟶ A') (jA' : A' ⟶ P') (p' : P' ⟶ V') (jV' : V' ⟶ Y')
  {πU : U'.left ⟶ U.left} {πA : A'.left ⟶ A.left} {πP : P'.left ⟶ P.left}
  {πV : V'.left ⟶ V.left} {πY : Y'.left ⟶ Y.left}
  (bcg : boundedConstructibleLowerShriek l g ⋙ boundedConstructibleUpperStarOfMap l πA ≅
    boundedConstructibleUpperStarOfMap l πU ⋙ boundedConstructibleLowerShriek l g')
  (bcjA : boundedConstructibleLowerShriek l jA ⋙ boundedConstructibleUpperStarOfMap l πP ≅
    boundedConstructibleUpperStarOfMap l πA ⋙ boundedConstructibleLowerShriek l jA')
  (bcp : boundedConstructibleLowerShriek l p ⋙ boundedConstructibleUpperStarOfMap l πV ≅
    boundedConstructibleUpperStarOfMap l πP ⋙ boundedConstructibleLowerShriek l p')
  (bcjV : boundedConstructibleLowerShriek l jV ⋙ boundedConstructibleUpperStarOfMap l πY ≅
    boundedConstructibleUpperStarOfMap l πV ⋙ boundedConstructibleLowerShriek l jV')
  (eY : (boundedConstructibleUpperStarOfMap l πY).obj (𝟙_ _) ⟶ 𝟙_ _)

variable [IsProper p.left] [IsProper p'.left] (sqp : IsPullback πP p'.left p.left πV)
  [IsOpenImmersion jV.left] [IsOpenImmersion jV'.left]
  (eV : (boundedConstructibleUpperStarOfMap l πV).obj (𝟙_ _) ⟶ 𝟙_ _)

end Chart

section Congr

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) {f₁' f₂' : X' ⟶ Y'} (h' : f₁' = f₂')
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}
  (bc : boundedConstructibleLowerShriek l f₁ ⋙ boundedConstructibleUpperStarOfMap l πY ≅
    boundedConstructibleUpperStarOfMap l πX ⋙ boundedConstructibleLowerShriek l f₁')
  (e : (boundedConstructibleUpperStarOfMap l πY).obj (𝟙_ _) ⟶ 𝟙_ _)

end Congr

end AlgebraicGeometry.ProEtale.CondensedRing
