# Picard canonical base-change support declarations

## Reason

The target needs specified comparison maps compatible with evaluation, rather than
an arbitrary isomorphism furnished by an existence statement. Add explicit maps and
prove their invertibility and the generic transpose-square assembly. Isolate the
remaining cup-pairing naturality calculation. No existing declaration signature,
visibility, definition, or public import is changed.

## Old

The support modules and declarations listed below were absent. The existing target
signature is unchanged; its old proof was `:= by sorry`.

## New

The following are the complete new support modules. Their only unproved declaration
is the pairing-naturality theorem. All data are constructed, and the existing target
combines their declarations without altering its statement.

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.PicardCupProductMap
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction

/-! # Canonical comparisons for degree-zero Picard base change

Source: Stacks Project, Tags 0095, 0096, 08HY and 0BDP.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Tensor pullback composition, transported from ordinary pullback.
Source: Stacks Project, Tags 0095 and 0096; uniqueness of left adjoints.
(blueprint: lem-sc-picard-canonical-base-change-comparisons) -/
noncomputable def picardTensorCompIso {A B C : Scheme.{u}}
    (k : A ⟶ B) (l : B ⟶ C) (M : C.Modules) :
    (tensorPullback k).obj ((tensorPullback l).obj M) ≅
      (tensorPullback (k ≫ l)).obj M :=
  (tensorPullback k).mapIso ((picardTensorComparison l).app M) ≪≫
    (picardTensorComparison k).app ((pullback l).obj M) ≪≫
      (pullbackComp k l).app M ≪≫ (picardTensorComparison (k ≫ l)).symm.app M

/-- The map between the non-iterated fibre products induced by a base morphism.
Source: Stacks Project, Tag 0BDP, change-of-base paragraph.
(blueprint: lem-sc-picard-canonical-base-change-comparisons) -/
noncomputable def picardBaseChangeTop {X S W T : Scheme.{u}}
    (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) :
    CategoryTheory.Limits.pullback f (h ≫ j) ⟶ CategoryTheory.Limits.pullback f j :=
  CategoryTheory.Limits.pullback.lift (CategoryTheory.Limits.pullback.fst f (h ≫ j))
    (CategoryTheory.Limits.pullback.snd f (h ≫ j) ≫ h)
    (by rw [Category.assoc]; exact CategoryTheory.Limits.pullback.condition)

/-- The canonical direct-image base-change map, with the top pullbacks composed.
Source: Stacks Project, Tags 08HY and 0BDP, change-of-base paragraph.
(blueprint: lem-sc-picard-canonical-base-change-comparisons) -/
noncomputable def picardDirectImageBaseChangeMap {X S W T : Scheme.{u}}
    (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) (M : X.Modules) :
    (tensorPullback h).obj
      ((pushforward (CategoryTheory.Limits.pullback.snd f j)).obj
        ((tensorPullback (CategoryTheory.Limits.pullback.fst f j)).obj M)) ⟶
    (pushforward (CategoryTheory.Limits.pullback.snd f (h ≫ j))).obj
      ((tensorPullback (CategoryTheory.Limits.pullback.fst f (h ≫ j))).obj M) :=
  let v := picardBaseChangeTop f j h
  moduleBaseChangeMap (CategoryTheory.Limits.pullback.snd f j)
    (CategoryTheory.Limits.pullback.snd f (h ≫ j)) h v
    (by dsimp [v, picardBaseChangeTop]; rw [CategoryTheory.Limits.pullback.lift_snd])
    ((tensorPullback (CategoryTheory.Limits.pullback.fst f j)).obj M) ≫
    (pushforward (CategoryTheory.Limits.pullback.snd f (h ≫ j))).map
      ((picardTensorCompIso v (CategoryTheory.Limits.pullback.fst f j) M).hom ≫
        (eqToIso (congrArg (fun k ↦ (tensorPullback k).obj M)
          (by dsimp [v, picardBaseChangeTop];
              rw [CategoryTheory.Limits.pullback.lift_fst]))).hom)

/-- Pull evaluation back and transpose it; this fixes the dual comparison map.
Source: Stacks Project, Tag 0FNV, the coordinate dual basis computation.
(blueprint: lem-sc-picard-canonical-base-change-comparisons) -/
noncomputable def picardTensorDualComparison {W T : Scheme.{u}} (h : T ⟶ W)
    (M : W.Modules) : (tensorPullback h).obj (dual M) ⟶ dual ((tensorPullback h).obj M) :=
  MonoidalClosed.curry ((picardTensorObjIso h M (dual M)).inv ≫
    (tensorPullback h).map ((ihom.ev M).app (SheafOfModules.unit W.ringCatSheaf)) ≫
      (picardTensorUnitIso h).hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem picardTensorObjIso_inv_naturality {W T : Scheme.{u}} (h : T ⟶ W)
    {A B C D : W.Modules} (f : A ⟶ B) (g : C ⟶ D) :
    ((tensorPullback h).map f ⊗ₘ (tensorPullback h).map g) ≫
        (picardTensorObjIso h B D).inv =
      (picardTensorObjIso h A C).inv ≫ (tensorPullback h).map (f ⊗ₘ g) := by
  simp only [picardTensorObjIso, Iso.trans_inv, Iso.symm_inv, tensorIso_inv]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  erw [(picardTensorComparison h).hom.naturality f,
    (picardTensorComparison h).hom.naturality g]
  rw [← tensorHom_comp_tensorHom_assoc, Functor.Monoidal.μIso_hom,
    Functor.LaxMonoidal.μ_natural_assoc]
  erw [(picardTensorComparison h).inv.naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pulling a transpose back and applying the explicit dual comparison is currying
of the pulled pairing. This is naturality of the tensor comparison, followed by
injectivity of uncurrying. Source: Stacks Project, Tag 0095, tensor formula.
(blueprint: lem-sc-picard-canonical-base-change-comparisons) -/
private theorem picardTensorDualComparison_uncurry {W T : Scheme.{u}} (h : T ⟶ W)
    (M N : W.Modules) (g : N ⟶ dual M) :
    MonoidalClosed.uncurry ((tensorPullback h).map g ≫ picardTensorDualComparison h M) =
      (picardTensorObjIso h M N).inv ≫
        (tensorPullback h).map (MonoidalClosed.uncurry g) ≫ (picardTensorUnitIso h).hom := by
  rw [MonoidalClosed.uncurry_natural_left, picardTensorDualComparison,
    MonoidalClosed.uncurry_curry]
  rw [← id_tensorHom, ← (tensorPullback h).map_id,
    picardTensorObjIso_inv_naturality_assoc]
  rw [← Functor.map_comp_assoc, id_tensorHom, ← MonoidalClosed.uncurry_eq]

/-- A commuting square of pairings gives a commuting square of their transposes.
Source: Stacks Project, Tag 0BDP, transpose of the degree-zero cup pairing.
(blueprint: lem-sc-picard-canonical-base-change-comparisons) -/
private theorem picardTranspose_square {T : Scheme.{u}} {A A' B B' : T.Modules}
    (c : A ⟶ A') (a : B ⟶ B') (φ : B ⟶ dual A) (ψ : B' ⟶ dual A')
    (hpair : (c ⊗ₘ a) ≫ MonoidalClosed.uncurry ψ = MonoidalClosed.uncurry φ) :
    φ = (a ≫ ψ) ≫ dualMap c := by
  apply MonoidalClosed.uncurry_injective
  have hpre : dualMap c = (MonoidalClosed.pre c).app (SheafOfModules.unit T.ringCatSheaf) :=
    (pre_app c (SheafOfModules.unit T.ringCatSheaf)).symm
  rw [hpre, MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_natural_left]
  rw [← tensorHom_def_assoc]
  exact hpair.symm

/-- Invertible comparison maps and compatibility of pairings give a base-change
square for transposes. All isomorphisms are constructed from the specified maps.
Source: Stacks Project, Tag 0BDP, dualizing the degree-zero cup pairing.
(blueprint: lem-sc-picard-canonical-base-change-comparisons) -/
theorem picardBaseChangeSquare_of_pairings {W T : Scheme.{u}} (h : T ⟶ W)
    (N D : W.Modules) (NT DT : T.Modules)
    (φ : D ⟶ dual N) (ψ : DT ⟶ dual NT)
    (c : (tensorPullback h).obj N ⟶ NT) (a : (tensorPullback h).obj D ⟶ DT)
    [IsIso c] [IsIso a] [IsIso (picardTensorDualComparison h N)]
    (hpair : (c ⊗ₘ a) ≫ MonoidalClosed.uncurry ψ =
      (picardTensorObjIso h N D).inv ≫ (tensorPullback h).map (MonoidalClosed.uncurry φ) ≫
        (picardTensorUnitIso h).hom) :
    ∃ (aI : (tensorPullback h).obj D ≅ DT)
      (bI : (tensorPullback h).obj (dual N) ≅ dual NT),
      (tensorPullback h).map φ ≫ bI.hom = aI.hom ≫ ψ := by
  let d := asIso (picardTensorDualComparison h N)
  let cD := (dualFunctor T).mapIso (asIso c).symm.op
  have hpull := picardTensorDualComparison_uncurry h N D φ
  have key : (tensorPullback h).map φ ≫ d.hom = (a ≫ ψ) ≫ cD.inv :=
    picardTranspose_square c a _ _ (hpair.trans hpull.symm)
  refine ⟨asIso a, d ≪≫ cD, ?_⟩
  change (tensorPullback h).map φ ≫ (d.hom ≫ cD.hom) = _
  rw [← Category.assoc, key]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end AlgebraicGeometry.Scheme.Modules


/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.PicardCanonicalBaseChange
import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapPasting
import Sheaf.AlgebraicGeometry.ModuleBaseChangeOpenSquareIso

/-! # Invertibility of the non-iterated direct-image base-change map
Source: Stacks Project, Tags 08HY and 0BDP.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme

private theorem baseChange_isIso_of_iso_top {A B A' A'' T : Scheme.{u}}
    (p : A ⟶ B) (p' : A' ⟶ T) (p'' : A'' ⟶ T) (h : T ⟶ B) (v : A' ⟶ A)
    (e : A'' ≅ A') (w : v ≫ p = p' ≫ h) (we : e.hom ≫ p' = p'') (F : A.Modules)
    (hbc : IsIso (Modules.moduleBaseChangeMap p p' h v w F)) :
    IsIso (Modules.moduleBaseChangeMap p p'' h (e.hom ≫ v)
      (by rw [Category.assoc, w, ← Category.assoc, we]) F) := by
  have w' : e.hom ≫ p' = p'' ≫ 𝟙 T := by simpa only [Category.comp_id] using we
  have hrange : Set.range e.hom = p' ⁻¹' Set.range (𝟙 T) := by
    have hs : Function.Surjective e.hom := by
      intro x
      refine ⟨e.inv x, ?_⟩
      exact congrArg (fun k : A' ⟶ A' ↦ k x) e.inv_hom_id
    rw [Set.range_eq_univ.mpr hs]
    change Set.univ = p' ⁻¹' Set.range (id : T → T)
    rw [Set.range_id, Set.preimage_univ]
  have hi : IsIso (Modules.moduleBaseChangeMap p' p'' (𝟙 T) e.hom w'
      ((Modules.tensorPullback v).obj F)) :=
    Modules.moduleBaseChangeMap_open_square_isIso p' p'' (𝟙 T) e.hom w' hrange _
  have hout : IsIso (Modules.moduleBaseChangeMap p p'' (𝟙 T ≫ h) (e.hom ≫ v)
      ((Category.assoc e.hom v p).trans
        ((congrArg (fun k ↦ e.hom ≫ k) w).trans
          ((Category.assoc e.hom p' h).symm.trans
            ((congrArg (fun k ↦ k ≫ h) w').trans (Category.assoc p'' (𝟙 T) h))))) F) := by
    rw [Modules.moduleBaseChangeMap_pasting p p' p'' h v (𝟙 T) e.hom w w' F]
    infer_instance
  have heq : 𝟙 T ≫ h = h := Category.id_comp h
  cases heq
  exact hout

/-- Invertibility of the iterated cartesian base-change map implies invertibility
of the canonical map to the non-iterated fibre product.

Source: Stacks Project, Tag 08HY (canonical base change) and Tag 0BDP
(compatibility with arbitrary change of base).
(blueprint: lem-sc-picard-direct-image-base-change-iso)

Proof: Paste the pullback squares for f and j with the square for p_W and h.
The resulting pullback cone is canonically isomorphic to X_T. The top projection
under this isomorphism is picardBaseChangeTop f j h. Pushforward along this
scheme isomorphism is an equivalence, with inverse pushforward along its inverse.
Use uniqueness of left adjoints to compare the two tensor pullbacks. Taking
adjoints of the two base-change maps identifies their defining pushforwards of
the pullback units, by naturality of the unit and the sectionwise composition
identifications of pushforward. Hence the non-iterated map is the iterated map
followed by the pushforward and tensor-composition isomorphisms. Every factor is
invertible, so the displayed map is invertible. This applies to arbitrary M,
without finite local freeness or flatness; empty fibre products cause no change. -/
theorem picardDirectImageBaseChangeMap_isIso
    {X S W T : Scheme.{u}} (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) (M : X.Modules)
    (hbc : IsIso (Modules.moduleBaseChangeMap (pullback.snd f j)
      (pullback.snd (pullback.snd f j) h) h (pullback.fst (pullback.snd f j) h)
      pullback.condition ((Modules.tensorPullback (pullback.fst f j)).obj M))) :
    IsIso (Modules.picardDirectImageBaseChangeMap f j h M)  := by
  let p := pullback.snd f j
  let pi := pullback.snd p h
  let vi := pullback.fst p h
  let pt := pullback.snd f (h ≫ j)
  let v := Modules.picardBaseChangeTop f j h
  let sq := (IsPullback.of_hasPullback p h).paste_horiz (IsPullback.of_hasPullback f j)
  let e := sq.isoPullback.symm
  have he : e.hom ≫ pi = pt := sq.isoPullback_inv_snd
  have hv : e.hom ≫ vi = v := by
    apply pullback.hom_ext
    · dsimp [v, Modules.picardBaseChangeTop]
      rw [pullback.lift_fst]
      exact sq.isoPullback_inv_fst
    · rw [Category.assoc, pullback.condition, ← Category.assoc, he]
      dsimp [v, Modules.picardBaseChangeTop]
      rw [pullback.lift_snd]
  have hi : IsIso (Modules.moduleBaseChangeMap p pt h v
      (by dsimp [v, Modules.picardBaseChangeTop]; rw [pullback.lift_snd])
      ((Modules.tensorPullback (pullback.fst f j)).obj M)) := by
    have hh := baseChange_isIso_of_iso_top p pi pt h vi e pullback.condition he
      ((Modules.tensorPullback (pullback.fst f j)).obj M) hbc
    have hall : ∀ w' : (e.hom ≫ vi) ≫ p = pt ≫ h,
        IsIso (Modules.moduleBaseChangeMap p pt h (e.hom ≫ vi) w'
          ((Modules.tensorPullback (pullback.fst f j)).obj M)) := fun _ ↦ hh
    have htransport := congrArg (fun v' ↦ ∀ w' : v' ≫ p = pt ≫ h,
      IsIso (Modules.moduleBaseChangeMap p pt h v' w'
        ((Modules.tensorPullback (pullback.fst f j)).obj M))) hv
    exact (htransport.mp hall) _
  dsimp only [Modules.picardDirectImageBaseChangeMap]
  infer_instance

end AlgebraicGeometry.Scheme


/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.PicardCanonicalBaseChange

import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.LocallyFree
import Sheaf.AlgebraicGeometry.DualTensorHomComparison
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! # Invertibility of the canonical tensor-pullback dual comparison
Source: Stacks Project, Tags 0FNV and 01C8.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme

/-- The comparison defined by transposing pulled evaluation is invertible for a
finite locally free module.

Source: Stacks Project, Tag 0FNV, finite free dual bases; Tag 01C8,
base change of locally free sheaves.
(blueprint: lem-sc-picard-tensor-dual-comparison-iso)

Proof: The finite-locally-free dual-tensor-Hom isomorphism agrees with the
closed-category comparison. Thus the comparison at M is invertible, and
MonoidalClosed.exactPairingOfIsIso gives the canonical exact pairing of dual M
with M, whose evaluation is the internal-Hom evaluation. Transport the monoidal
structure of ordinary pullback along picardTensorComparison, and apply
ExactPairing.map. The resulting evaluation is the tensor comparison followed by
the pulled internal-Hom evaluation and the transported monoidal unit comparison.
Its transpose is an isomorphism by MonoidalClosed.curry_evaluation. The explicit
picardTensorUnitIso might use a different unit comparison; compose with the
unit automorphism obtained as the inverse transported unit map followed by this
explicit map. Its image under internal Hom is invertible. Naturality of currying
in the target identifies the resulting composite with the defined canonical
comparison. Hence that comparison is invertible as well. This argument covers
rank zero, empty schemes and arbitrary base morphisms without flatness. -/
theorem picardTensorDualComparison_isIso {W T : Scheme.{u}} (h : T ⟶ W)
    (M : W.Modules) [M.IsFiniteLocallyFree] :
    IsIso (Modules.picardTensorDualComparison h M) := by
  have : IsIso (MonoidalClosed.ihomUnitTensorToIhom M M) := by
    rw [← Modules.dualTensorHom_eq_ihomUnitTensorToIhom]
    infer_instance
  let : ExactPairing (Modules.dual M) M := MonoidalClosed.exactPairingOfIsIso M
  let : (Modules.tensorPullback h).Monoidal :=
    Functor.Monoidal.transport (Modules.picardTensorComparison h).symm
  let : ExactPairing ((Modules.tensorPullback h).obj (Modules.dual M))
      ((Modules.tensorPullback h).obj M) :=
    ExactPairing.map (Modules.tensorPullback h) (Modules.dual M) M
  let k := inv (Functor.OplaxMonoidal.η (Modules.tensorPullback h)) ≫
    (Modules.picardTensorUnitIso h).hom
  have : IsIso k := by dsimp [k]; infer_instance
  have hi : IsIso (MonoidalClosed.curry
      (ε_ ((Modules.tensorPullback h).obj (Modules.dual M))
        ((Modules.tensorPullback h).obj M)) ≫
      (ihom ((Modules.tensorPullback h).obj M)).map k) := by
    infer_instance
  rw [← MonoidalClosed.curry_natural_right] at hi
  convert hi using 1
  · rfl
  · unfold Modules.picardTensorDualComparison
    congr 1
    change _ =
      (Functor.LaxMonoidal.μ (Modules.tensorPullback h) M (Modules.dual M) ≫
        (Modules.tensorPullback h).map ((ihom.ev M).app (SheafOfModules.unit W.ringCatSheaf)) ≫
        Functor.OplaxMonoidal.η (Modules.tensorPullback h)) ≫
      (inv (Functor.OplaxMonoidal.η (Modules.tensorPullback h)) ≫
        (Modules.picardTensorUnitIso h).hom)
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [Functor.Monoidal.transport_μ]
    simp only [Modules.picardTensorObjIso, Iso.trans_inv, tensorIso_inv, Iso.symm_inv,
      Iso.app_hom, Iso.symm_hom, Functor.Monoidal.μIso_hom, Category.assoc]
    rfl

end AlgebraicGeometry.Scheme


/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.PicardCanonicalBaseChange

/-! # Compatibility of the cup pairing with arbitrary base change
Source: Stacks Project, Tag 0BDP, final two paragraphs.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme

/-- The degree-zero cup pairing commutes with the canonical direct-image maps.
This statement does not assume the direct-image maps are invertible and does not
assert any dual-pullback comparison is invertible.

Source: Stacks Project, Tag 0BDP, compatibility with arbitrary change of base
and the evaluation formula for the cup product in the final two paragraphs.
(blueprint: lem-sc-picard-cup-pairing-base-change)

Proof: Expand picardCupProductMap and uncurry its defining transpose, obtaining
the pushed-forward evaluation pairing. Apply the tensor comparison for h. Take
the adjoint along p_T of the two proposed pairings. Expand each canonical
base-change map as the mate of the top pullback unit. Naturality of the units
and counits, together with the two triangle identities, replaces the two
base-change maps followed by the p_T counits with the pullbacks of the p_W
counits. Tensor-composition comparisons transport their evaluations to X_T.
Both adjoints are then the pullback of E tensor dual E to X_T, followed by the
pulled evaluation and the inverse structure-sheaf unit. The structure units
commute with base change because their section formula is m mapped to 1 tensor m.
The tensor comparisons commute by naturality and tensor associativity. Thus the
adjoints agree; injectivity of the adjunction Hom equivalence proves the formula.
This calculation uses neither local freeness nor any flatness of h. Zero pairings
and empty bases satisfy the same identities. -/
theorem picardCupPairing_baseChange
    {X S W T : Scheme.{u}} (f : X ⟶ S) (E : X.Modules)
    (j : W ⟶ S) (h : T ⟶ W)
    (hO : IsIso ((Classical.choose
      (Modules.exists_tensorPullbackAdjunction (pullback.snd f j))).unit.app
        (SheafOfModules.unit W.ringCatSheaf)))
    (hOT : IsIso ((Classical.choose
      (Modules.exists_tensorPullbackAdjunction (pullback.snd f (h ≫ j)))).unit.app
        (SheafOfModules.unit T.ringCatSheaf))) :
    ((Modules.picardDirectImageBaseChangeMap f j h E) ⊗ₘ
        (Modules.picardDirectImageBaseChangeMap f j h (Modules.dual E))) ≫
      MonoidalClosed.uncurry (picardCupProductMap f E (h ≫ j) hOT) =
    (Modules.picardTensorObjIso h
      ((Modules.pushforward (pullback.snd f j)).obj
        ((Modules.tensorPullback (pullback.fst f j)).obj E))
      ((Modules.pushforward (pullback.snd f j)).obj
        ((Modules.tensorPullback (pullback.fst f j)).obj (Modules.dual E)))).inv ≫
      (Modules.tensorPullback h).map (MonoidalClosed.uncurry (picardCupProductMap f E j hO)) ≫
        (Modules.picardTensorUnitIso h).hom := by sorry

end AlgebraicGeometry.Scheme

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | J1 | Proof imports and proof changed; signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.PicardCanonicalBaseChange | new in J1 delivery | Constructs the comparison maps and proves generic transpose assembly. |
| Sheaf.AlgebraicGeometry.PicardDirectImageBaseChangeIso | new in J1 delivery | Uses canonical maps, existing pasting and open-square results. |
| Sheaf.AlgebraicGeometry.PicardTensorDualComparisonIso | new in J1 delivery | Uses canonical maps and existing finite duality. |
| Sheaf.AlgebraicGeometry.PicardCupPairingBaseChange | new in J1 delivery | States the pairing compatibility needed by the target. |

Existing callers of the assigned theorem see exactly the same statement and visibility.
There are no forced adaptations and no changed target definitions.

## Status

landed 20261013T054220-L-443854 2026-10-13 (merge of deliver/J1/Sheaf.AlgebraicGeometry.PicardCupProductBaseChange)
