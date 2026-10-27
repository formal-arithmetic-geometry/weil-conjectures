/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed

import all Sheaf.Paper.CoefficientHeartLisseExtensionConstructible
import all Sheaf.SixFunctors.IntegralModelsGenerators
import all Sheaf.Paper.CondensedFiniteCoefficientLocalization
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Integral branch models and finite open-closed reconstruction

Source: Stacks Project, Tag 09AH, with Tags 09YD, 09YG, 03EL, 03ER and 0E8I;
the finite-tree argument in lem-sfb-qcqs-lattice-tree-reconstruction
(blueprint: lem-sfb-qcqs-lattice-tree-reconstruction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.all false
set_option cleanup.letToHave false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.TwoSquare
open scoped CategoryTheory.Obj

section MateIdentity


variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  {T : A ⥤ B} {S : B ⥤ A} {T' : A' ⥤ B'} {S' : B' ⥤ A'}
  {l : A' ⥤ A} {r : A ⥤ A'} {l' : B' ⥤ B} {r' : B ⥤ B'}

private theorem push_eq_mate_pull_inv (a : T ⊣ S) (b : T' ⊣ S')
    (c : l ⊣ r) (d : l' ⊣ r') (e : r' ⋙ S' ≅ S ⋙ r) :
    Adjunction.pushHomOfComapIso a b e =
      (mateEquiv c d (TwoSquare.mk _ _ _ _
        (Adjunction.pullIsoOfComapIso a b c d e).inv)).natTrans := by
  have h := iterated_mateEquiv_conjugateEquiv_symm c d b a
    (TwoSquare.mk _ _ _ _ e.inv)
  apply (TwoSquare.equivNatTrans _ _ _ _).symm.injective
  apply (mateEquiv c d).symm.injective
  change (mateEquiv c d).symm ((mateEquiv a b).symm (.mk _ _ _ _ e.inv)) =
    (mateEquiv c d).symm
      (mateEquiv c d (.mk _ _ _ _ (Adjunction.pullIsoOfComapIso a b c d e).inv))
  rw [Equiv.symm_apply_apply]
  exact h

end MateIdentity

namespace AlgebraicGeometry.ProEtale.LatticeTree

attribute [-instance] WeilConjectures.SixFunctors.integralModel_coefficientMonObj

/-- The existing module-object category over pulled-back condensed coefficients.
Source: coefficient convention of the item
(blueprint: lem-sfb-qcqs-lattice-tree-reconstruction). -/
abbrev Modules (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R]
    (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)

/-- A module in degree zero in the ordinary, uncompleted unbounded derived category.
Source: derived-category convention of the item
(blueprint: lem-sfb-qcqs-lattice-tree-reconstruction). -/
abbrev single (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R]
    (X : Scheme.{u}) (M : Modules R X) :=
  (DerivedCategory.singleFunctor (Modules R X) 0).obj M

/-- The actual scalar comparison along a branch, directed from extension after the
branch functor to the branch functor after extension. Its inverse is the comparison
in the displayed statement. The open edge uses the canonical adjunction conjugate;
the closed edge uses the canonical scalar/direct-image mate. Composition fixes the
map on every branch, including the identity on a path of length zero.
Source: Stacks 0E8I and 09AH; proof step 3
(blueprint: lem-sfb-qcqs-lattice-tree-reconstruction). -/
def scalarComparison
    {A R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj R] [IsCommMonObj R]
    (a : A ⟶ R) [IsMonHom a] {X W : Scheme.{u}} {t : QcqsOpenClosedTree X}
    (p : t.Path W) :
    p.extension A ⋙ Mod.extendScalars (coefficientMap a X) ⟶
      Mod.extendScalars (coefficientMap a W) ⋙ p.extension R :=
  match X, t, W, p with
  | _, _, _, .root _ => 𝟙 _
  | _, _, _, @QcqsOpenClosedTree.Path.openBranch _ _ _ _ _ _ j _ _ _ _ _ _ _ _ q =>
      Functor.whiskerLeft (q.extension A) (CondensedRing.openImmersionShriekIso a j).hom ≫
        Functor.whiskerRight (scalarComparison a q) (CondensedRing.openImmersionLowerShriek R j)
  | _, _, _, @QcqsOpenClosedTree.Path.closedBranch _ _ _ _ _ _ _ i _ _ _ _ _ _ _ q =>
      Functor.whiskerLeft (q.extension A) (CondensedRing.pushHom a i) ≫
        Functor.whiskerRight (scalarComparison a q) (CondensedRing.lowerStar R i)

/-- Preservation of the recorded finite scalar-model constructibility and tensor
flatness. Flatness is exactness of tensor, expressed by the existing flat-object
predicate on this module-object category.
Source: Stacks 09YD, 09YG and 03ER; proof steps 1--2
(blueprint: lem-sfb-qcqs-lattice-tree-reconstruction). -/
def PreservesModelsAndFlat
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X W : Scheme.{u}} {t : QcqsOpenClosedTree X} (p : t.Path W) : Prop :=
  ∀ B : Modules R W,
    (IsConstantModelConstructible R W B →
      IsConstantModelConstructible R X ((p.extension R).obj B)) ∧
    (ObjectProperty.flat B → ObjectProperty.flat ((p.extension R).obj B))

/-- Leaf paths, including paths to empty leaves. This is a subtype of the actual
vertices of the finite tree, not a family of independently chosen immersions.
Source: finite-tree argument in Tag 09AH
(blueprint: lem-sfb-qcqs-lattice-tree-reconstruction). -/
abbrev Leaf {X : Scheme.{u}} (t : QcqsOpenClosedTree X) :=
  Σ W : Scheme.{u}, {p : t.Path W // p.IsLeaf}

/-- The supplied, possibly zero integral lattices on the leaves, with their actual
scalar-extension identifications. The field index may vary from leaf to leaf.
Source: the leaf hypotheses of the item
(blueprint: lem-sfb-qcqs-lattice-tree-reconstruction). -/
structure LeafModels
    (ℓ : ℕ) [Fact ℓ.Prime] (I : Type) (F : I → PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (a : ∀ k : I, Profinite.padicIntegersRingObj.{u} ℓ (F k).1 ⟶ R)
    [∀ k : I, IsMonHom (a k)] {X : Scheme.{u}} (t : QcqsOpenClosedTree X)
    (M : Modules R X) where
  fieldIndex : Leaf t → I
  model (w : Leaf t) : Modules (Profinite.padicIntegersRingObj ℓ (F (fieldIndex w)).1) w.1
  lisse (w : Leaf t) : IsLisseCoefficientModule
    (Profinite.padicIntegersRingObj ℓ (F (fieldIndex w)).1) (model w)
  scalarIso (w : Leaf t) :
    (Mod.extendScalars (coefficientMap (a (fieldIndex w)) w.1)).obj (model w) ≅
      (CondensedRing.upperStar R w.2.1.toRoot).obj M

/-- The integral branch module J_W, using the given integral field on that leaf.
Source: definition of J_W in the item
(blueprint: lem-sfb-qcqs-lattice-tree-reconstruction). -/
def branchModel
    {ℓ : ℕ} [Fact ℓ.Prime] {I : Type} {F : I → PadicAlgCl.FiniteIntermediateField ℓ}
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {a : ∀ k : I, Profinite.padicIntegersRingObj.{u} ℓ (F k).1 ⟶ R}
    [∀ k : I, IsMonHom (a k)] {X : Scheme.{u}} {t : QcqsOpenClosedTree X}
    {M : Modules R X} (d : LeafModels ℓ I F R a t M) (w : Leaf t) :=
  (w.2.1.extension (Profinite.padicIntegersRingObj ℓ (F (d.fieldIndex w)).1)).obj (d.model w)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- All clauses of the branch-model and reconstruction assertion for a specified
coefficient family and its canonical integral inclusions. Flatness of the coefficient
extension is imposed at every vertex for each field in that family. The final finite
extension product uses arbitrary morphisms in D(R_X), and does not descend these maps
to any common finite field.
Source: Stacks 09AH and the finite-tree argument, clauses 1--3 of the item
(blueprint: lem-sfb-qcqs-lattice-tree-reconstruction). -/
def Reconstruction
    (ℓ : ℕ) [Fact ℓ.Prime] (I : Type) (F : I → PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (a : ∀ k : I, Profinite.padicIntegersRingObj.{u} ℓ (F k).1 ⟶ R)
    [∀ k : I, IsMonHom (a k)] : Prop :=
  let derivedScalar {Y : Scheme.{u}}
      {A B : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}}
      [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
      (φ : A ⟶ B) [IsMonHom φ] :
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) A) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) B) :=
    (Mod.extendScalars φ).leftDerivedFunctor
  ∀ (X : Scheme.{u}) (t : QcqsOpenClosedTree X),
    (∀ (W : Scheme.{u}) (_p : t.Path W) (k : I),
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap (a k) W))) →
    (∀ (W : Scheme.{u}) (p : t.Path W),
      PreservesModelsAndFlat R p ∧
      ∀ k : I, PreservesModelsAndFlat (Profinite.padicIntegersRingObj ℓ (F k).1) p ∧
        PreservesModelsAndFlat (Profinite.continuousMapRingObj (F k).1) p ∧
        ∀ B : Modules (Profinite.padicIntegersRingObj ℓ (F k).1) W,
          IsIso ((scalarComparison (a k) p).app B)) ∧
    ∀ (M : Modules R X) (d : LeafModels ℓ I F R a t M),
      (∀ w : Leaf t,
        constantModelBoundedConstructible
          (Profinite.padicIntegersRingObj ℓ (F (d.fieldIndex w)).1) X
          (single _ X (branchModel d w)) ∧
        DerivedCategory.finiteTorAmplitude _ (single _ X (branchModel d w)) ∧
        DerivedCategory.torAmplitudeIn _ 0 0 (single _ X (branchModel d w)) ∧
        Nonempty
          ((derivedScalar (coefficientMap (a (d.fieldIndex w)) X)).obj
              (single _ X (branchModel d w)) ≅
            single R X ((w.2.1.extension R).obj
              ((CondensedRing.upperStar R w.2.1.toRoot).obj M)))) ∧
      ∃ n : ℕ, ObjectProperty.extensionProductIter
        (fun K : DerivedCategory (Modules R X) ↦ ∃ w : Leaf t,
          Nonempty (K ≅ single R X ((w.2.1.extension R).obj
            ((CondensedRing.upperStar R w.2.1.toRoot).obj M)))) n (single R X M)

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  CondensedRing.upperStar CondensedRing.lowerStar CondensedRing.openImmersionLowerShriek
  Mod.extendScalars Functor.mapDerivedCategory Functor.mapDerivedCategoryPlus
  CondensedRing.pullIso CondensedRing.pushHom CondensedRing.openImmersionShriekIso
  Functor.mapDerivedCategorySingleFunctor Functor.mapDerivedCategoryPlusSingleFunctor
  exactOuterSingleIso HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

set_option backward.isDefEq.respectTransparency true

private theorem tree_qcqs {X : Scheme.{u}} (t : QcqsOpenClosedTree X) :
    CompactSpace X ∧ QuasiSeparatedSpace X := by
  cases t <;> exact ⟨inferInstance, inferInstance⟩

private theorem path_preserves
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X W : Scheme.{u}} {t : QcqsOpenClosedTree X} (p : t.Path W) :
    PreservesModelsAndFlat R p := by
  induction p with
  | root => exact fun B ↦ ⟨id, id⟩
  | @openBranch X U Z W _ _ j i _ _ _ _ h a b p ih =>
    intro B
    obtain ⟨hcU, hqU⟩ := tree_qcqs a
    let := hcU
    let := hqU
    constructor
    · intro hB
      have hs := (ih B).1 hB
      rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at hs ⊢
      exact stratified_openExtension R j _ hs
    · exact fun hB ↦ (WeilConjectures.SixFunctors.integralModel_open_closed_flat
        R i j h).2 _ ((ih B).2 hB)
  | @closedBranch X U Z W _ _ j i _ _ _ _ h a b p ih =>
    intro B
    obtain ⟨hcZ, hqZ⟩ := tree_qcqs b
    let := hcZ
    let := hqZ
    constructor
    · intro hB
      have hs := (ih B).1 hB
      rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at hs ⊢
      have hji : Set.range i = (Set.range j)ᶜ := by rw [h, compl_compl]
      obtain ⟨S, hS⟩ := hs
      have hi := CondensedRing.moduleCounitOfAbelian R i
        (ProEtale.abelian_closed_support i j h).1
      apply stratified_of_restrictions R j i hji
      · exact finiteConstantStratified_of_isZero R _ _
          (CondensedRing.openRestrictionPushforwardZero R i j h _)
      · exact ⟨S, fun c ↦ finiteModel_iso R _
          ((CondensedRing.upperStar R (S.immersion c)).mapIso
            (asIso ((CondensedRing.upperStarLowerStarAdjunction R i).counit.app _)).symm)
          (hS c)⟩
    · exact fun hB ↦ (WeilConjectures.SixFunctors.integralModel_open_closed_flat
        R i j h).1 _ ((ih B).2 hB)

private theorem closed_scalar_iso
    {A R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj R] [IsCommMonObj R]
    (a : A ⟶ R) [IsMonHom a] {X U Z : Scheme.{u}}
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] (h : Set.range j = (Set.range i)ᶜ) (B : Modules A Z) :
    IsIso ((CondensedRing.pushHom a i).app B) := by
  have hiA := CondensedRing.moduleCounitOfAbelian A i
    (ProEtale.abelian_closed_support i j h).1
  have hiR := CondensedRing.moduleCounitOfAbelian R i
    (ProEtale.abelian_closed_support i j h).1
  let δ := (CondensedRing.pushHom a i).app B
  apply (CondensedRing.jointlyReflectIsomorphisms_upperStar_of_isCompl R i j
    (by rw [h]; exact isCompl_compl)).isIso_of_pairFunctor δ
  · have hzA := CondensedRing.openRestrictionPushforwardZero A i j h B
    have hzR := CondensedRing.openRestrictionPushforwardZero R i j h
      ((Mod.extendScalars (coefficientMap a Z)).obj B)
    have hz := ((Mod.extendScalars (coefficientMap a U)).map_isZero hzA).of_iso
      ((CondensedRing.pullIso a j).app ((CondensedRing.lowerStar A i).obj B)).symm
    exact hz.isIso hzR _
  · have hd : CondensedRing.pushHom a i =
        (mateEquiv (CondensedRing.upperStarLowerStarAdjunction A i)
          (CondensedRing.upperStarLowerStarAdjunction R i)
          (TwoSquare.mk _ _ _ _ (CondensedRing.pullIso a i).inv)).natTrans := by
      simpa only [CondensedRing.pushHom, CondensedRing.pullIso] using
        (push_eq_mate_pull_inv
        (Mod.extendRestrictAdjunction (coefficientMap a Z))
        (Mod.extendRestrictAdjunction (coefficientMap a X))
        (CondensedRing.upperStarLowerStarAdjunction A i)
        (CondensedRing.upperStarLowerStarAdjunction R i) (CondensedRing.comapLowerStarIso a i))
    have he : (CondensedRing.upperStar R i).map δ ≫
        (CondensedRing.upperStarLowerStarAdjunction R i).counit.app
          ((Mod.extendScalars (coefficientMap a Z)).obj B) =
        (CondensedRing.pullIso a i).inv.app ((CondensedRing.lowerStar A i).obj B) ≫
          (Mod.extendScalars (coefficientMap a Z)).map
            ((CondensedRing.upperStarLowerStarAdjunction A i).counit.app B) := by
      change (CondensedRing.upperStar R i).map ((CondensedRing.pushHom a i).app B) ≫ _ = _
      rw [hd]
      exact mateEquiv_counit (CondensedRing.upperStarLowerStarAdjunction A i)
        (CondensedRing.upperStarLowerStarAdjunction R i)
        (TwoSquare.mk _ _ _ _ (CondensedRing.pullIso a i).inv) B
    have : IsIso ((CondensedRing.upperStar R i).map δ ≫
        (CondensedRing.upperStarLowerStarAdjunction R i).counit.app
          ((Mod.extendScalars (coefficientMap a Z)).obj B)) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right ((CondensedRing.upperStar R i).map δ)
      ((CondensedRing.upperStarLowerStarAdjunction R i).counit.app _)

private theorem path_scalar_iso
    {A R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj R] [IsCommMonObj R]
    (a : A ⟶ R) [IsMonHom a] {X W : Scheme.{u}} {t : QcqsOpenClosedTree X}
    (p : t.Path W) (B : Modules A W) : IsIso ((scalarComparison a p).app B) := by
  induction p with
  | root => change IsIso (𝟙 _); infer_instance
  | @openBranch X U Z W _ _ j i _ _ _ _ h ta tb p ih =>
    change IsIso ((CondensedRing.openImmersionShriekIso a j).hom.app _ ≫
      (CondensedRing.openImmersionLowerShriek R j).map ((scalarComparison a p).app B))
    have := ih
    infer_instance
  | @closedBranch X U Z W _ _ j i _ _ _ _ h ta tb p ih =>
    change IsIso ((CondensedRing.pushHom a i).app _ ≫
      (CondensedRing.lowerStar R i).map ((scalarComparison a p).app B))
    have := ih
    have := closed_scalar_iso a j i h ((p.extension A).obj B)
    infer_instance

private theorem leaf_lisse_flat
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X : Scheme.{u}} (B : Modules R X) (hB : IsLisseCoefficientModule R B) :
    ObjectProperty.flat B := by
  apply WeilConjectures.SixFunctors.integralModel_locallyFree_flat
  obtain ⟨C, hC⟩ := hB
  exact ⟨C, fun k ↦ (CondensedRing.freeAt_iff_standard R (C.f k) B).mpr (hC k)⟩

private theorem single_localization_of_distinguished
    {C U Z : Type*} [Category C] [Category U] [Category Z]
    [Abelian C] [Abelian U] [Abelian Z]
    [HasDerivedCategory C] [HasDerivedCategory U] [HasDerivedCategory Z]
    (jL : U ⥤ C) (jR : C ⥤ U) (iL : C ⥤ Z) (iR : Z ⥤ C)
    [jL.Additive] [jR.Additive] [iL.Additive] [iR.Additive]
    [PreservesFiniteLimits jL] [PreservesFiniteColimits jL]
    [PreservesFiniteLimits jR] [PreservesFiniteColimits jR]
    [PreservesFiniteLimits iL] [PreservesFiniteColimits iL]
    [PreservesFiniteLimits iR] [PreservesFiniteColimits iR]
    (aj : jL.mapDerivedCategoryPlus ⊣ jR.mapDerivedCategoryPlus)
    (ai : iL.mapDerivedCategoryPlus ⊣ iR.mapDerivedCategoryPlus)
    (δ : iL.mapDerivedCategoryPlus ⋙ iR.mapDerivedCategoryPlus ⟶
      jR.mapDerivedCategoryPlus ⋙ jL.mapDerivedCategoryPlus ⋙ shiftFunctor _ (1 : ℤ))
    (htri : ∀ K, Pretriangulated.Triangle.mk
      (aj.counit.app K) (ai.unit.app K) (δ.app K) ∈ distTriang _) (N : C) :
    ∃ T : Triangle (_root_.DerivedCategory C), T ∈ distTriang _ ∧
      Nonempty ((_root_.DerivedCategory.singleFunctor C 0).obj (jL.obj (jR.obj N)) ≅
        T.obj₁) ∧
      Nonempty ((_root_.DerivedCategory.singleFunctor C 0).obj (iR.obj (iL.obj N)) ≅
        T.obj₃) ∧
      Nonempty (T.obj₂ ≅ (_root_.DerivedCategory.singleFunctor C 0).obj N) := by
  let K := (_root_.DerivedCategory.Plus.singleFunctor C 0).obj N
  let Tp := Pretriangulated.Triangle.mk (aj.counit.app K) (ai.unit.app K) (δ.app K)
  let T := _root_.DerivedCategory.Plus.ι.mapTriangle.obj Tp
  refine ⟨T, _root_.DerivedCategory.Plus.ι.map_distinguished Tp (htri K), ?_, ?_, ?_⟩
  · exact ⟨exactOuterSingleIso jR jL N⟩
  · exact ⟨exactOuterSingleIso iL iR N⟩
  · exact ⟨(_root_.DerivedCategory.Plus.singleFunctorιIso C 0).app N⟩

set_option backward.isDefEq.respectTransparency true in
private theorem localization_single_triangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (k : Z ⟶ X) [IsClosedImmersion k]
    (hjk : Set.range j = (Set.range k)ᶜ)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ∃ D : Triangle (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      D ∈ distTriang _ ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.openImmersionLowerShriek Λ j).obj
          ((CondensedRing.upperStar Λ j).obj N)) ≅ D.obj₁) ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar Λ k).obj ((CondensedRing.upperStar Λ k).obj N)) ≅ D.obj₃) ∧
      Nonempty (D.obj₂ ≅ (DerivedCategory.singleFunctor _ 0).obj N) := by
  have hrec := CondensedRing.condensed_open_closed_recollement Λ k j hjk
  rcases hrec with ⟨hc, hrec⟩
  rcases hrec with ⟨hjl, hjc, hkl, hkc, hsl, hsc, hcl, _, _, _, _, _, r⟩
  let _ := hc
  let _ := hjl
  let _ := hjc
  let _ := hkl
  let _ := hkc
  let _ := hsl
  let _ := hsc
  let _ := hcl
  obtain ⟨ish, ha, hl, r⟩ := r
  let _ := ha
  let _ := hl
  obtain ⟨ash, aj, bj, ai, bi, hjshift, hishift, r⟩ := r
  let _ := hjshift
  let _ := hishift
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, δ, ε, _, _, htri, _⟩ := r
  exact single_localization_of_distinguished
    (CondensedRing.openImmersionLowerShriek Λ j) (CondensedRing.upperStar Λ j)
    (CondensedRing.upperStar Λ k) (CondensedRing.lowerStar Λ k) aj ai δ htri N


attribute [local irreducible] ObjectProperty.extensionProductIter

private theorem extension_iter_triangle
    {C : Type*} [Category C] [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (T : Triangle C) (hT : T ∈ distTriang C) (n m : ℕ)
    (h₁ : P.extensionProductIter n T.obj₁) (h₃ : P.extensionProductIter m T.obj₃) :
    P.extensionProductIter (n + 1 + m) T.obj₂ := by
  rw [ObjectProperty.extensionProductIter_add P rfl]
  exact ⟨T.obj₁, T.obj₃, T.mor₁, T.mor₂, T.mor₃, hT, h₁, h₃⟩

private theorem extension_iter_closed
    {C : Type*} [Category C] [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (n : ℕ) :
    (P.extensionProductIter n).IsClosedUnderIsomorphisms := by
  cases n with
  | zero => rw [ObjectProperty.extensionProductIter_zero]; infer_instance
  | succ n => rw [ObjectProperty.extensionProductIter_succ]; infer_instance

private theorem extension_iter_iso_triangle
    {C : Type*} [Category C] [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    {A B N : C} (T : Triangle C) (hT : T ∈ distTriang C)
    (e₁ : T.obj₁ ≅ A) (e₂ : T.obj₂ ≅ N) (e₃ : T.obj₃ ≅ B) (n m : ℕ)
    (hn : P.extensionProductIter n A) (hm : P.extensionProductIter m B) :
    P.extensionProductIter (n + 1 + m) N := by
  have := extension_iter_closed P n
  have := extension_iter_closed P m
  have := extension_iter_closed P (n + 1 + m)
  exact (P.extensionProductIter _).prop_of_iso e₂
    (extension_iter_triangle P T hT n m
      ((P.extensionProductIter n).prop_of_iso e₁.symm hn)
      ((P.extensionProductIter m).prop_of_iso e₃.symm hm))

private theorem extensions_mapped_triangle
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    {A B N : D} (T : Triangle C) (hT : T ∈ distTriang C)
    (e₁ : F.obj T.obj₁ ≅ A) (e₂ : F.obj T.obj₂ ≅ N) (e₃ : F.obj T.obj₃ ≅ B)
    (n m : ℕ) (hn : P.extensionProductIter n A) (hm : P.extensionProductIter m B) :
    P.extensionProductIter (n + 1 + m) N := by
  exact extension_iter_iso_triangle P (F.mapTriangle.obj T)
    (F.map_distinguished T hT) e₁ e₂ e₃ n m hn hm

set_option backward.isDefEq.respectTransparency true in
private theorem extensions_of_single_triangle
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : ObjectProperty (_root_.DerivedCategory D)) [P.IsClosedUnderIsomorphisms]
    (A N B : C) (T : Triangle (_root_.DerivedCategory C)) (hT : T ∈ distTriang _)
    (e₁ : (_root_.DerivedCategory.singleFunctor C 0).obj A ≅ T.obj₁)
    (e₂ : T.obj₂ ≅ (_root_.DerivedCategory.singleFunctor C 0).obj N)
    (e₃ : (_root_.DerivedCategory.singleFunctor C 0).obj B ≅ T.obj₃)
    (n m : ℕ)
    (hn : P.extensionProductIter n ((_root_.DerivedCategory.singleFunctor D 0).obj (F.obj A)))
    (hm : P.extensionProductIter m ((_root_.DerivedCategory.singleFunctor D 0).obj (F.obj B))) :
    P.extensionProductIter (n + 1 + m)
      ((_root_.DerivedCategory.singleFunctor D 0).obj (F.obj N)) := by
  let G := F.mapDerivedCategory
  let d₁ := G.mapIso e₁.symm ≪≫ (F.mapDerivedCategorySingleFunctor 0).app A
  let d₂ := G.mapIso e₂ ≪≫ (F.mapDerivedCategorySingleFunctor 0).app N
  let d₃ := G.mapIso e₃.symm ≪≫ (F.mapDerivedCategorySingleFunctor 0).app B
  exact extensions_mapped_triangle G P T hT d₁ d₂ d₃ n m hn hm

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStar

attribute [local irreducible] CondensedRing.upperStarComp CondensedRing.upperStarId
  CondensedRing.upperStarLowerStarAdjunction

section
variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]
private theorem root_toRoot {X : Scheme.{u}} (t : QcqsOpenClosedTree X) :
    (QcqsOpenClosedTree.Path.root t).toRoot = 𝟙 X := rfl
private theorem root_extension {X : Scheme.{u}} (t : QcqsOpenClosedTree X) :
    (QcqsOpenClosedTree.Path.root t).extension R = 𝟭 _ := rfl
variable {X U Z W : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
  [QuasiCompact j] [QuasiCompact i] (h : Set.range j = (Set.range i)ᶜ)
  (a : QcqsOpenClosedTree U) (b : QcqsOpenClosedTree Z)
private theorem open_toRoot (p : a.Path W) :
    (QcqsOpenClosedTree.Path.openBranch j i h a b p).toRoot = p.toRoot ≫ j := rfl
private theorem closed_toRoot (p : b.Path W) :
    (QcqsOpenClosedTree.Path.closedBranch j i h a b p).toRoot = p.toRoot ≫ i := rfl
private theorem open_extension (p : a.Path W) :
    (QcqsOpenClosedTree.Path.openBranch j i h a b p).extension R =
      p.extension R ⋙ CondensedRing.openImmersionLowerShriek R j := rfl
private theorem closed_extension (p : b.Path W) :
    (QcqsOpenClosedTree.Path.closedBranch j i h a b p).extension R =
      p.extension R ⋙ CondensedRing.lowerStar R i := rfl

end

attribute [local irreducible] QcqsOpenClosedTree.Path.toRoot
  QcqsOpenClosedTree.Path.extension

@[irreducible] private def pull_comp
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X U W : Scheme.{u}} (f : W ⟶ U) (j : U ⟶ X) (N : Modules R X) :
    (CondensedRing.upperStar R (f ≫ j)).obj N ≅
      (CondensedRing.upperStar R f).obj ((CondensedRing.upperStar R j).obj N) :=
  (CondensedRing.upperStarComp R f j).app N

@[irreducible] private def leafObject
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X W : Scheme.{u}} {t : QcqsOpenClosedTree X} (p : t.Path W) (N : Modules R X) :
    Modules R X := (p.extension R).obj ((CondensedRing.upperStar R p.toRoot).obj N)

@[irreducible] private def root_leaf_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X : Scheme.{u}} (t : QcqsOpenClosedTree X) (N : Modules R X) :
    leafObject R (QcqsOpenClosedTree.Path.root t) N ≅ N := by
  unfold leafObject
  rw [root_extension, root_toRoot]
  exact (CondensedRing.upperStarId R X).app N

private theorem property_map_iso
    {C D : Type*} [Category C] [Category D]
    (Q : ObjectProperty D) [Q.IsClosedUnderIsomorphisms] (F : C ⥤ D)
    {A B : C} (e : A ≅ B) (hA : Q (F.obj A)) : Q (F.obj B) :=
  Q.prop_of_iso (F.mapIso e) hA

private def mapIso_twice {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) {A B : C} (e : A ≅ B) :
    G.obj (F.obj A) ≅ G.obj (F.obj B) := G.mapIso (F.mapIso e)

private theorem branch_leaf_iso_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X U Z W : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] [QuasiCompact i] (h : Set.range j = (Set.range i)ᶜ)
    (ta : QcqsOpenClosedTree U) (tb : QcqsOpenClosedTree Z)
    (p : ta.Path W) (N : Modules R X) :
    leafObject R (QcqsOpenClosedTree.Path.openBranch j i h ta tb p) N =
      (CondensedRing.openImmersionLowerShriek R j).obj ((p.extension R).obj
        ((CondensedRing.upperStar R (p.toRoot ≫ j)).obj N)) := by
  unfold leafObject
  rw [open_extension, open_toRoot]
  rfl

@[irreducible] private def branch_leaf_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X U Z W : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] [QuasiCompact i] (h : Set.range j = (Set.range i)ᶜ)
    (ta : QcqsOpenClosedTree U) (tb : QcqsOpenClosedTree Z)
    (p : ta.Path W) (N : Modules R X) :
    leafObject R (QcqsOpenClosedTree.Path.openBranch j i h ta tb p) N ≅
      (CondensedRing.openImmersionLowerShriek R j).obj
        (leafObject R p ((CondensedRing.upperStar R j).obj N)) := by
  refine (eqToIso (branch_leaf_iso_eq R j i h ta tb p N)) ≪≫ ?_
  unfold leafObject
  change (CondensedRing.openImmersionLowerShriek R j).obj ((p.extension R).obj _) ≅
    (CondensedRing.openImmersionLowerShriek R j).obj ((p.extension R).obj _)
  exact mapIso_twice (p.extension R) (CondensedRing.openImmersionLowerShriek R j)
    (pull_comp R p.toRoot j N)

private theorem closed_branch_leaf_iso_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X U Z W : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] [QuasiCompact i] (h : Set.range j = (Set.range i)ᶜ)
    (ta : QcqsOpenClosedTree U) (tb : QcqsOpenClosedTree Z)
    (p : tb.Path W) (N : Modules R X) :
    leafObject R (QcqsOpenClosedTree.Path.closedBranch j i h ta tb p) N =
      (CondensedRing.lowerStar R i).obj ((p.extension R).obj
        ((CondensedRing.upperStar R (p.toRoot ≫ i)).obj N)) := by
  unfold leafObject
  rw [closed_extension, closed_toRoot]
  rfl

@[irreducible] private def closed_branch_leaf_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X U Z W : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] [QuasiCompact i] (h : Set.range j = (Set.range i)ᶜ)
    (ta : QcqsOpenClosedTree U) (tb : QcqsOpenClosedTree Z)
    (p : tb.Path W) (N : Modules R X) :
    leafObject R (QcqsOpenClosedTree.Path.closedBranch j i h ta tb p) N ≅
      (CondensedRing.lowerStar R i).obj (leafObject R p ((CondensedRing.upperStar R i).obj N)) := by
  refine (eqToIso (closed_branch_leaf_iso_eq R j i h ta tb p N)) ≪≫ ?_
  unfold leafObject
  change (CondensedRing.lowerStar R i).obj ((p.extension R).obj _) ≅
    (CondensedRing.lowerStar R i).obj ((p.extension R).obj _)
  exact mapIso_twice (p.extension R) (CondensedRing.lowerStar R i) (pull_comp R p.toRoot i N)



set_option backward.isDefEq.respectTransparency true in
private theorem closed_exact
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i] [QuasiCompact j]
    (h : Set.range j = (Set.range i)ᶜ) :
    PreservesFiniteColimits (CondensedRing.lowerStar R i) := by
  have := CondensedRing.moduleCounitOfAbelian R i
    (ProEtale.abelian_closed_support i j h).1
  exact CondensedRing.exactClosedOfDetection
    (CondensedRing.upperStar R i) (CondensedRing.lowerStar R i)
    (CondensedRing.upperStar R j) (CondensedRing.upperStarLowerStarAdjunction R i)
    (CondensedRing.openRestrictionPushforwardZero R i j h)
    (fun M hi hj ↦ CondensedRing.isZero_of_isZero_upperStar_of_isCompl R i j
      (by rw [h]; exact isCompl_compl) M hi hj)

@[irreducible] private def TreeInductionGoal
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {D : Type*} [Category D] [Abelian D] (Q : ObjectProperty D)
    {X : Scheme.{u}} (t : QcqsOpenClosedTree X) : Prop :=
    ∀ (F : Modules R X ⥤ D) [F.Additive]
      [PreservesFiniteLimits F] [PreservesFiniteColimits F]
      (N : Modules R X),
      (∀ w : Leaf t, Q (F.obj (leafObject R w.2.1 N))) → Q (F.obj N)

@[irreducible] private def TreeInductionStep
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {D : Type*} [Category D] [Abelian D] (Q : ObjectProperty D) : Prop :=
  ∀ {Y U Z : Scheme.{u}} (j : U ⟶ Y) (i : Z ⟶ Y)
      [IsOpenImmersion j] [IsClosedImmersion i] [QuasiCompact j]
      (h : Set.range j = (Set.range i)ᶜ)
      (F : Modules R Y ⥤ D) [F.Additive]
      [PreservesFiniteLimits F] [PreservesFiniteColimits F] (N : Modules R Y),
      Q (F.obj ((CondensedRing.openImmersionLowerShriek R j).obj
        ((CondensedRing.upperStar R j).obj N))) →
      Q (F.obj ((CondensedRing.lowerStar R i).obj
        ((CondensedRing.upperStar R i).obj N))) → Q (F.obj N)

private theorem tree_induction
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {D : Type*} [Category D] [Abelian D]
    (Q : ObjectProperty D) [Q.IsClosedUnderIsomorphisms]
    (hstep : TreeInductionStep R Q)
    {X : Scheme.{u}} (t : QcqsOpenClosedTree X) : TreeInductionGoal R Q t := by
  induction t with
  | leaf X =>
    unfold TreeInductionGoal
    intro F _ _ _ N hleaf
    exact property_map_iso Q F (root_leaf_iso R (.leaf X) N)
      (hleaf ⟨X, .root _, trivial⟩)
  | @split X U Z _ _ j i _ _ _ _ h ta tb iha ihb =>
    unfold TreeInductionGoal at iha ihb ⊢
    intro F _ _ _ N hleaf
    have : PreservesFiniteColimits (CondensedRing.lowerStar R i) :=
      closed_exact R j i h
    have hu : ∀ w : Leaf ta,
        Q (((CondensedRing.openImmersionLowerShriek R j) ⋙ F).obj
          (leafObject R w.2.1 ((CondensedRing.upperStar R j).obj N))) := by
      intro w
      have hv := hleaf ⟨w.1, .openBranch j i h ta tb w.2.1, w.2.2⟩
      exact property_map_iso Q F (branch_leaf_iso R j i h ta tb w.2.1 N) hv
    have hz : ∀ w : Leaf tb,
        Q (((CondensedRing.lowerStar R i) ⋙ F).obj
          (leafObject R w.2.1 ((CondensedRing.upperStar R i).obj N))) := by
      intro w
      have hv := hleaf ⟨w.1, .closedBranch j i h ta tb w.2.1, w.2.2⟩
      exact property_map_iso Q F (closed_branch_leaf_iso R j i h ta tb w.2.1 N) hv
    have hs := hstep
    unfold TreeInductionStep at hs
    exact hs j i h F N
      (iha (CondensedRing.openImmersionLowerShriek R j ⋙ F)
        ((CondensedRing.upperStar R j).obj N) hu)
      (ihb (CondensedRing.lowerStar R i ⋙ F)
        ((CondensedRing.upperStar R i).obj N) hz)


@[irreducible] private def finiteExtensionsInHeart
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (P : ObjectProperty (_root_.DerivedCategory D)) : ObjectProperty D :=
  fun M ↦ ∃ n, P.extensionProductIter n
    ((_root_.DerivedCategory.singleFunctor D 0).obj M)

private theorem finiteExtensionsInHeart_closed
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (P : ObjectProperty (_root_.DerivedCategory D)) [P.IsClosedUnderIsomorphisms] :
    (finiteExtensionsInHeart P).IsClosedUnderIsomorphisms := by
  constructor
  intro A B e hA
  rw [finiteExtensionsInHeart] at hA ⊢
  obtain ⟨n, hn⟩ := hA
  let := extension_iter_closed P n
  exact ⟨n, (P.extensionProductIter n).prop_of_iso
    ((_root_.DerivedCategory.singleFunctor D 0).mapIso e) hn⟩

set_option backward.isDefEq.respectTransparency true in
private theorem tree_reconstruct
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    {X : Scheme.{u}} (t : QcqsOpenClosedTree X) :
    ∀ (F : Modules R X ⥤ D) [F.Additive]
      [PreservesFiniteLimits F] [PreservesFiniteColimits F]
      (P : ObjectProperty (_root_.DerivedCategory D)) [P.IsClosedUnderIsomorphisms]
      (N : Modules R X),
      (∀ w : Leaf t, P ((_root_.DerivedCategory.singleFunctor D 0).obj
        (F.obj ((w.2.1.extension R).obj
          ((CondensedRing.upperStar R w.2.1.toRoot).obj N))))) →
      ∃ n : ℕ, P.extensionProductIter n
        ((_root_.DerivedCategory.singleFunctor D 0).obj (F.obj N)) := by
  intro F _ _ _ P _ N hleaf
  let Q : ObjectProperty D := finiteExtensionsInHeart P
  have : Q.IsClosedUnderIsomorphisms := finiteExtensionsInHeart_closed P
  suffices hresult : Q (F.obj N) by
    simpa only [Q, finiteExtensionsInHeart] using hresult
  have hs : TreeInductionStep R Q := by
    unfold TreeInductionStep
    intro Y U Z j i _ _ _ h G _ _ _ M hU hZ
    change finiteExtensionsInHeart P _ at hU hZ ⊢
    rw [finiteExtensionsInHeart] at hU hZ ⊢
    obtain ⟨n, hn⟩ := hU
    obtain ⟨m, hm⟩ := hZ
    obtain ⟨T, hT, ⟨e₁⟩, ⟨e₃⟩, ⟨e₂⟩⟩ := localization_single_triangle R j i h M
    exact ⟨n + 1 + m, extensions_of_single_triangle G P _ M _ T hT
      e₁ e₂ e₃ n m hn hm⟩
  have hi := tree_induction R Q hs t
  rw [TreeInductionGoal] at hi
  apply hi F N
  intro w
  change finiteExtensionsInHeart P _
  rw [finiteExtensionsInHeart]
  exact ⟨0, by
    simpa only [ObjectProperty.extensionProductIter_zero, leafObject] using hleaf w⟩

private theorem path_qcqs {X W : Scheme.{u}} {t : QcqsOpenClosedTree X}
    (p : t.Path W) : CompactSpace W ∧ QuasiSeparatedSpace W := by
  induction p with
  | root t => exact tree_qcqs t
  | openBranch _ _ _ _ _ _ ih => exact ih
  | closedBranch _ _ _ _ _ _ ih => exact ih

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem model_single_properties
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (M : Modules Λ X)
    (hc : IsConstantModelConstructible Λ X M) (hf : ObjectProperty.flat M) :
    constantModelBoundedConstructible Λ X (single Λ X M) ∧
      _root_.DerivedCategory.finiteTorAmplitude (Modules Λ X) (single Λ X M) ∧
      _root_.DerivedCategory.torAmplitudeIn (Modules Λ X) 0 0 (single Λ X M) := by
  have ht := _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hf
  exact ⟨single_constructible Λ X M hc, ⟨0, 0, ht⟩, ht⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem flat_scalar_single_iso
    {X : Scheme.{u}} {A R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj R] [IsCommMonObj R]
    (a : A ⟶ R) [IsMonHom a]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) A)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hf : ObjectProperty.flat M) (e : (Mod.extendScalars a).obj M ≅ N) :
    Nonempty ((WeilConjectures.SixFunctors.integralModel_derivedScalar a).obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (DerivedCategory.singleFunctor _ 0).obj N) := by
  obtain ⟨ed⟩ := WeilConjectures.SixFunctors.integralModel_flat_derived_single a M hf
  exact ⟨ed ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem path_lisse_properties
    {A R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj R] [IsCommMonObj R]
    (a : A ⟶ R) [IsMonHom a] {X W : Scheme.{u}} {t : QcqsOpenClosedTree X}
    (p : t.Path W) (B : Modules A W) (hB : IsLisseCoefficientModule A B) :
    constantModelBoundedConstructible A X (single A X ((p.extension A).obj B)) ∧
      _root_.DerivedCategory.finiteTorAmplitude (Modules A X)
        (single A X ((p.extension A).obj B)) ∧
      _root_.DerivedCategory.torAmplitudeIn (Modules A X) 0 0
        (single A X ((p.extension A).obj B)) ∧
      Nonempty ((WeilConjectures.SixFunctors.integralModel_derivedScalar
        (coefficientMap a X)).obj
        (single A X ((p.extension A).obj B)) ≅
          single R X ((p.extension R).obj ((Mod.extendScalars (coefficientMap a W)).obj B))) := by
  obtain ⟨hWc, hWq⟩ := path_qcqs p
  have := hWc
  have := hWq
  obtain ⟨hXc, hXq⟩ := tree_qcqs t
  have := hXc
  have := hXq
  have hcB : IsConstantModelConstructible A W B := by
    rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
    exact stratified_of_finiteModel A _ _ (lisse_finiteModel A _ _ hB)
  have hc := (path_preserves A p B).1 hcB
  have hf := (path_preserves A p B).2 (leaf_lisse_flat A B hB)
  obtain ⟨hbc, hfin, ht⟩ := model_single_properties A X ((p.extension A).obj B) hc hf
  have hs := path_scalar_iso a p B
  exact ⟨hbc, hfin, ht, flat_scalar_single_iso (coefficientMap a X)
    ((p.extension A).obj B) _ hf (asIso ((scalarComparison a p).app B))⟩

private theorem nonempty_iso_single_comp
    {C D : Type*} [Category C] [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) {A B : C} {K : _root_.DerivedCategory D}
    (h : Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor D 0).obj (F.obj A)))
    (e : A ≅ B) :
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor D 0).obj (F.obj B)) := by
  obtain ⟨h⟩ := h
  exact ⟨h ≪≫ (_root_.DerivedCategory.singleFunctor D 0).mapIso (F.mapIso e)⟩

set_option backward.isDefEq.respectTransparency true in
private theorem reconstruction_general
    (ℓ : ℕ) [Fact ℓ.Prime] (I : Type) (F : I → PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (a : ∀ k : I, Profinite.padicIntegersRingObj.{u} ℓ (F k).1 ⟶ R)
    [∀ k : I, IsMonHom (a k)] : Reconstruction ℓ I F R a := by
  dsimp only [Reconstruction]
  intro X t hflat
  constructor
  · intro W p
    exact ⟨path_preserves R p, fun k ↦
      ⟨path_preserves _ p, path_preserves _ p, fun B ↦ path_scalar_iso (a k) p B⟩⟩
  · intro M d
    constructor
    · intro w
      obtain ⟨hbc, hfin, ht, he⟩ := path_lisse_properties (a (d.fieldIndex w))
        w.2.1 (d.model w) (d.lisse w)
      unfold WeilConjectures.SixFunctors.integralModel_derivedScalar at he
      exact ⟨hbc, hfin, ht,
        nonempty_iso_single_comp (w.2.1.extension R) he (d.scalarIso w)⟩
    · let P : ObjectProperty (DerivedCategory (Modules R X)) := fun K ↦ ∃ w : Leaf t,
        Nonempty (K ≅ single R X ((w.2.1.extension R).obj
          ((CondensedRing.upperStar R w.2.1.toRoot).obj M)))
      have : P.IsClosedUnderIsomorphisms := ⟨by
        intro K L e hK
        obtain ⟨w, ⟨hw⟩⟩ := hK
        exact ⟨w, ⟨e.symm ≪≫ hw⟩⟩⟩
      exact tree_reconstruct R t (𝟭 _) P M (fun w ↦ ⟨w, ⟨Iso.refl _⟩⟩)

-- Avoid repeating the large coefficient-instance comparisons during optional linting.
set_option linter.all false in
/-- Integral branch models, scalar compatibility and finite triangle reconstruction,
for E coefficients and for finite-subextension-valued algebraic-closure coefficients.
Source: Stacks Project, Tag 09AH, with Tags 09YD, 09YG, 03EL, 03ER, 0E8I and 06YU
(blueprint: lem-sfb-qcqs-lattice-tree-reconstruction).

Proof:
1. Glue finite constant-model stratifications across each complementary open and closed
pair. The extension restricts to the input on its supporting child and to zero on the
other. The rank-zero constant model handles zero modules and empty children.
2. The normalized tensor/pullback comparison tests tensor kernels on both children.
Open/closed detection proves flatness preservation. Local finite freeness proves that
the leaf lattices are flat. Induct on paths for both preservation assertions.
3. The open scalar comparison is openImmersionShriekIso. For the closed comparison,
check the actual pushHom after both restrictions. Its open restriction is between zero
objects. The mate/counit identity identifies its closed restriction, after an invertible
counit, with pullIso.inv followed by extension of an invertible closed counit. Joint
reflection of isomorphisms and path induction prove the stated scalarComparison is iso.
4. The generic flat-single theorem gives Tor amplitude [0,0]. A single of a constructible
module is bounded constructible. The K-flat single complex computes total left derived
scalar extension, giving ordinary scalar extension in degree zero. Compose with step 3
and the given leaf scalarIso.
5. Include the bounded-below localization triangle into the ordinary derived category;
its three terms are the corresponding single objects. Induct on the binary tree, allowing
an arbitrary exact additive functor to the root category. Map each localization triangle
by that functor and combine the child extension products with extensionProductIter_add.
The one-vertex case uses upperStarId. All maps remain over the fixed root coefficient
ring. Specialize the uniform argument to both coefficient families.
-/
theorem qcqs_lattice_tree_reconstruction (ℓ : ℕ) [Fact ℓ.Prime] :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Reconstruction.{u} ℓ Unit (fun _ ↦ E) (Profinite.continuousMapRingObj E.1)
        (fun _ ↦ padicIntegersRingObjToContinuousMapRingObj ℓ E)) ∧
    Reconstruction.{u} ℓ (PadicAlgCl.FiniteIntermediateField ℓ) (fun F ↦ F)
      (Profinite.padicAlgClRingObj ℓ)
      (fun F ↦ padicIntegersRingObjToContinuousMapRingObj ℓ F ≫
        Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) := by
  constructor
  · intro E
    exact reconstruction_general ℓ Unit (fun _ ↦ E) _ _
  · exact reconstruction_general ℓ (PadicAlgCl.FiniteIntermediateField ℓ) (fun F ↦ F) _ _

end AlgebraicGeometry.ProEtale.LatticeTree
