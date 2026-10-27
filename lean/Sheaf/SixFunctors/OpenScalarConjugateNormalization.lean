/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.Paper.OpenInternalKFlatMateNormalization
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormulaAdjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

/-! # Restriction of the specified open scalar conjugate

Source: blueprint main-20261015, det-prop-scalar-six-pullback.proof.md (2), alternative
open-adjunction argument; def-sfb-derived-open-immersion-shriek-iso; Stacks Tag 0B65
(blueprint: lem-sfb-open-scalar-conjugate-normalization).

The displayed isomorphisms have their forward maps fixed to the scalar-adjunction mate
and the actual open adjunction units. Thus their inverses cannot be independently
renormalized. All categories and scalar extensions are ordinary and unbounded.
The inline projection of the left functor from its specified adjunction is definitionally
L(extendScalars); it avoids repeatedly synthesizing the K-flat tensor instances.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Full faithfulness passes through the coefficient isomorphism and the linear lift.
private theorem openUnitIsIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit := by
  let ff := (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulFunctor.comp
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).fullyFaithfulMapModLeft
  have : (openImmersionLowerShriek Λ j).Full := ff.full
  have : (openImmersionLowerShriek Λ j).Faithful := ff.faithful
  exact Adjunction.unit_isIso_of_L_fully_faithful _

-- Iterating inverse mates identifies the inverse of the published conjugate.
private theorem scalarOpenInverseMate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) :
    ((mateEquiv a b).symm
      ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv))).natTrans =
      ((conjugateIsoEquiv (u.comp b) (a.comp x)).symm q).inv := by
  exact congrArg TwoSquare.natTrans
    (iterated_mateEquiv_conjugateEquiv_symm a b u x (TwoSquare.mk _ _ _ _ q.inv))

-- Apply the unit mate equation, then take inverses of the resulting isomorphisms.
private theorem scalarOpenRestriction
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) (θ : JA ⋙ SU ≅ SX ⋙ JB)
    (hθ : θ.hom = SheafOfModules.ScalarPullback.mate x u q.inv)
    (uA : 𝟭 C ≅ LA ⋙ JA) (huA : uA.hom = a.unit)
    (uB : 𝟭 E ≅ LB ⋙ JB) (huB : uB.hom = b.unit) (M : C) :
    JB.map (((conjugateIsoEquiv (u.comp b) (a.comp x)).symm q).hom.app M) ≫
        uB.inv.app (SU.obj M) = θ.inv.app (LA.obj M) ≫ SU.map (uA.inv.app M) := by
  let α := (mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)
  have hh := unit_mateEquiv_symm a b α M
  have hi := scalarOpenInverseMate a b x u q
  change SU.map (a.unit.app M) ≫ α.natTrans.app _ =
    b.unit.app _ ≫ JB.map (((mateEquiv a b).symm α).natTrans.app M) at hh
  rw [hi] at hh
  change SU.map (a.unit.app M) ≫
    (SheafOfModules.ScalarPullback.mate x u q.inv).app _ = _ at hh
  rw [← hθ, ← huA, ← huB] at hh
  let l := uB.app (SU.obj M) ≪≫
    JB.mapIso (((conjugateIsoEquiv (u.comp b) (a.comp x)).symm q).symm.app M)
  let r := SU.mapIso (uA.app M) ≪≫ θ.app (LA.obj M)
  have hhom : l.hom = r.hom := hh.symm
  have hinv := congrArg Iso.inv (Iso.ext hhom)
  simpa only [l, r, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
    Iso.symm_inv] using hinv

-- Keep localization construction data folded while using the normalized mate.
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

/-- The specified scalar/open conjugate restricts to inverse theta under the actual units.

Source: blueprint main-20261015, det-prop-scalar-six-pullback.proof.md (2), alternative
open-adjunction argument; Stacks Tag 0B65
(blueprint: lem-sfb-open-scalar-conjugate-normalization).

Proof:
1. Write J_A, J_B for open extension, R_A, R_B for restriction, and r for scalar
restriction. The published beta is the conjugate of c : R_B ⋙ r_U ≅ r_X ⋙ R_A
under the two composite adjunctions (def-weil-pbc-composite-adjunction).
2. Since alpha is invertible (lem-sfb-alpha-iso), extension along alpha collapses by
x tensor n ↦ alpha inverse(x)n, with inverse n ↦ 1 tensor n. The coefficient-change
square identifies both restricted actions, using sk-def-sfb-change-of-scalars,
sk-def-sfb-transport and sk-def-sfb-module-pushforward-pullback.
3. Unfold comapUpperStarIso and extendScalarsComapIsoOfIsIso: c and its inverse
become identity maps on the same inverse-image module. Localize degreewise.
4. Transpose beta under T_X J_A ⊣ R_A r_X. The composite-unit formula identifies
its transpose with c followed by the transpose of the identity under J_B T_U ⊣ r_U R_B.
5. Transport to sectionwise modules via lem-sfb-internal-module-operations-transport
and lem-sfb-internal-section-scalar-adjunction. Apply
lem-sfb-kflat-scalar-comparison-normalization: the mate of c inverse is the balanced
K-flat comparison theta on every unbounded object, and is invertible without flatness.
6. Transpose R_B(beta_M) theta_(J_A M) T_U(u_A,M) under T_U ⊣ r_U.
Naturality of the scalar unit, the mate equation, naturality of c inverse and step 4
identify this transpose with the transpose of u_B,T_U M. The Hom bijection is injective.
7. The actual open units are invertible. Cancel these units and theta in step 6.
Functoriality gives the displayed equality, naturally for all M. -/
theorem open_scalar_conjugate_normalization
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ∃ (θ : D((j)^*⟦Λ⟧) ⋙ ((fun {F : _} {G : _} (_ : F ⊣ G) ↦ F)
            (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))) ≅
          ((fun {F : _} {G : _} (_ : F ⊣ G) ↦ F)
            (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))) ⋙ D((j)^*⟦Λ'⟧))
      (uA : 𝟭 (DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))) ≅
        D((j)_!open⟦Λ⟧) ⋙ D((j)^*⟦Λ⟧))
      (uB : 𝟭 (DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ' U))) ≅
        D((j)_!open⟦Λ'⟧) ⋙ D((j)^*⟦Λ'⟧)),
      θ.hom = SheafOfModules.ScalarPullback.mate
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))
        (derivedComapUpperStarIso a j).inv ∧
      uA.hom = (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit ∧
      uB.hom = (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j).unit ∧
      ∀ M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)),
        D((j)^*⟦Λ'⟧).map ((derivedOpenImmersionShriekIso a j).hom.app M) ≫
            uB.inv.app (((fun {F : _} {G : _} (_ : F ⊣ G) ↦ F)
              (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))).obj M) =
          θ.inv.app (D((j)_!open⟦Λ⟧).obj M) ≫
            ((fun {F : _} {G : _} (_ : F ⊣ G) ↦ F)
              (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))).map
                (uA.inv.app M) := by
  let x := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)
  let u := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U)
  let aa := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j
  let bb := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j
  let c := derivedComapUpperStarIso a j
  have : IsGrothendieckAbelian.{u + 1}
      (SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ U)) :=
    IsGrothendieckAbelian.of_equivalence (InternalModuleOperations.equivalence Λ U)
  let : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ U)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  have : IsGrothendieckAbelian.{u + 1}
      (SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ X)) :=
    IsGrothendieckAbelian.of_equivalence (InternalModuleOperations.equivalence Λ X)
  let : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ X)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  have : IsGrothendieckAbelian.{u + 1}
      (SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ' U)) :=
    IsGrothendieckAbelian.of_equivalence (InternalModuleOperations.equivalence Λ' U)
  let : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ' U)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  have : IsGrothendieckAbelian.{u + 1}
      (SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ' X)) :=
    IsGrothendieckAbelian.of_equivalence (InternalModuleOperations.equivalence Λ' X)
  let : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ' X)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  have hn := (OpenInternalScalar.normalization a j).exists
  let t := hn.choose
  have ht := hn.choose_spec.2.2.1
  have hm := hn.choose_spec.2.2.2.1
  have hsq : mateEquiv x u (TwoSquare.mk _ _ _ _ t) =
      TwoSquare.mk _ _ _ _ c.inv := by
    apply TwoSquare.ext
    intro V
    exact congrArg (fun z ↦ z.app V) hm
  have heq : t = SheafOfModules.ScalarPullback.mate x u c.inv :=
    congrArg TwoSquare.natTrans ((mateEquiv x u).eq_symm_apply.mpr hsq)
  have : IsIso t := ht
  let θ := asIso t
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit := openUnitIsIso Λ j
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ' j).unit := openUnitIsIso Λ' j
  have : IsIso aa.unit := Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have : IsIso bb.unit := Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  let uA := asIso aa.unit
  let uB := asIso bb.unit
  refine ⟨θ, uA, uB, heq, rfl, rfl, ?_⟩
  intro M
  exact scalarOpenRestriction aa bb x u c θ heq uA rfl uB rfl M

end AlgebraicGeometry.ProEtale.CondensedRing
