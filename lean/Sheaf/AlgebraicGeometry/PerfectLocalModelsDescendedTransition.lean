/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.OpenSectionsCohomologyModel
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonDiagram
import Sheaf.AlgebraicGeometry.TwoOpenComparisonRealization

/-! # Descent of the prescribed overlap transition

Source: Stacks Project, Tags 09RE and 09RF, the transition before object gluing.
(blueprint: lem-pc-perfect-local-models-descended-transition).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits schemeOpenOverlapRestriction_additive
  schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits

-- Preserve the existing names of unused dependent Pi binders in the statement.
set_option linter.unusedVariables false in
set_option synthInstance.maxHeartbeats 400000 in
-- Elaborating the transported overlap restrictions needs this instance-search budget.
set_option maxHeartbeats 800000 in
-- The dependent stage objects and overlap functors need this elaboration budget.
/-- Descend the prescribed overlap identification, retaining its action on every
realization of the descended gluing datum. This does not construct a stage object.
Source: Stacks Project, Tags 09RE and 09RF, two-open induction before Tag 08DG.
(blueprint: lem-pc-perfect-local-models-descended-transition).

Proof: Use the directed tail above j. The stage scheme Yj is quasi-separated,
since its structural map is quasi-separated and its base is affine. The compact
opens U and V therefore have compact intersection W. Its inclusion is a
quasi-compact open immersion, so W maps to Spec Rj by a finite presentation map.
Restrict A and B to W. Derived pullback preserves their perfectness. Restrict
φU and φV and compose the first with the inverse of the second. Under the
canonical composition and open-restriction comparisons this is an isomorphism
between the limit pullbacks of the two perfect overlap objects. Apply perfect
morphism descent to this isomorphism on the tail, including its inverse; the
isomorphism clause (or stabilization of both inverse equations) supplies k and
an invertible transition e on the inverse-image overlap. The cartesian open
identifications transport e to the displayed exact overlap restrictions of the
pulled objects A' and B'. Its pullback is the prescribed transition.
For an arbitrary F and local identifications iU,iV realizing e, pull those
identifications to the limit and compose with the transported φU,φV. The
realization equation and the prescribed pullback equation imply equality of
the resulting maps on the overlap in the open-subscheme derived categories.
Pass to fully faithful preimages through the derived functors of overEquiv.
Their composition comparisons identify the preimages with isomorphisms pU,pV
on the localized sites. The canonical Hom restriction transport identity
identifies their overlap equality with the displayed derivedOpenHomRestriction
equality. This argument uses only the realization equation; it neither assumes
nor proves that such an F exists. Empty overlaps, empty opens and equal opens
use the same equations. The tail remains directed for a non-strict preorder. -/
theorem perfect_local_models_descended_transition
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    :
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
    ∃ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))
      let f := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U' := f ⁻¹ᵁ U
      let V' := f ⁻¹ᵁ V
      let instY : Category (schemeDerivedCategory Yk) := inferInstance
      let instU : Category (schemeDerivedCategory U'.toScheme) := inferInstance
      let instV : Category (schemeDerivedCategory V'.toScheme) := inferInstance
      let instW : Category (schemeDerivedCategory (U' ⊓ V').toScheme) := inferInstance
      let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
      let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
      let SU : schemeDerivedCategory U'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
      let SV : schemeDerivedCategory V'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
      let TU : schemeDerivedCategory Yk ⥤ schemeDerivedCategory U'.toScheme :=
        (schemeOpenRestriction Yk U').mapDerivedCategory
      let TV : schemeDerivedCategory Yk ⥤ schemeDerivedCategory V'.toScheme :=
        (schemeOpenRestriction Yk V').mapDerivedCategory
      let TW : schemeDerivedCategory Yk ⥤ schemeDerivedCategory (U' ⊓ V').toScheme :=
        (schemeOpenRestriction Yk (U' ⊓ V')).mapDerivedCategory
      let αU : TU ⋙ SU ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))
      let αV : TV ⋙ SV ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))
      ∃ e : SU.obj A' ≅ SV.obj B',
        ∀ (F : schemeDerivedCategory Yk)
          (iU : TU.obj F ≅ A')
          (iV : TV.obj F ≅ B'),
        αU.inv.app F ≫ SU.map iU.hom ≫ e.hom =
          αV.inv.app F ≫ SV.map iV.hom →
        let P := gj ⁻¹ᵁ U
        let Q := gj ⁻¹ᵁ V
        let L : schemeDerivedCategory X := (derivedPullback g).obj F
        let instLP : Category (DerivedCategory
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over P))) := inferInstance
        let instLQ : Category (DerivedCategory
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Q))) := inferInstance
        let instLW : Category (DerivedCategory
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (P ⊓ Q)))) := inferInstance
        let RU : schemeDerivedCategory X ⥤
            DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over P)) :=
          (SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) P).mapDerivedCategory
        let RV : schemeDerivedCategory X ⥤
            DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Q)) :=
          (SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) Q).mapDerivedCategory
        let RW : schemeDerivedCategory X ⥤ DerivedCategory
            (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (P ⊓ Q))) :=
          (SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
        let rU : (RU.obj L ⟶ RU.obj E) → (RW.obj L ⟶ RW.obj E) :=
          derivedOpenHomRestriction X.toRingedSpace
            (homOfLE (show P ⊓ Q ≤ P from inf_le_left)) (E := L) (F := E)
        let rV : (RV.obj L ⟶ RV.obj E) → (RW.obj L ⟶ RW.obj E) :=
          derivedOpenHomRestriction X.toRingedSpace
            (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)) (E := L) (F := E)
        ∃ (pU : RU.obj L ≅ RU.obj E) (pV : RV.obj L ≅ RV.obj E),
          rU pU.hom = rV pV.hom := by
  intro Yj X gj U V hcover hU hV A B hA hB E instP instQ instX PU PV φU φV
  obtain ⟨k, hjk, d, e, θU, θV, hθ⟩ :=
    perfect_overlap_transition_comparison R c hc i Z t j hij
      U V hcover hU hV A B hA hB E φU φV
  refine ⟨k, hjk, e, ?_⟩
  intro F iU iV hi
  exact d.toDiagram.realization e θU θV hθ F iU iV hi

end AlgebraicGeometry
