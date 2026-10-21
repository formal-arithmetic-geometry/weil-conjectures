/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

import Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import all Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Underived projection for a closed pro-etale immersion

Source: Stacks Project, proetale.tex, Tags 09AA and 09AH, and sites-modules.tex,
Section 03EK and Tag 03EL. The projection consequence is agent-formulated.
(blueprint: lem-weil-pbc-proetale-closed-underived-projection).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtaleTensorComparison

namespace AlgebraicGeometry.ProEtaleClosedProjection

/-- The actual module adjunction is uniquely characterized by its constructed unit
on every section. This fixes adjunction data, rather than choosing an arbitrary
adjunction between the functors.
Source: Stacks, Tags 03D2, 03D3 and 09AA; the canonical adjunct in the statement
(blueprint: lem-weil-pbc-proetale-closed-underived-projection).
Proof: transport the existing pullbackPushforwardAdjunction on the AsSmall model
back along the explicit module equivalences. The right-adjoint comparison is the
sectionwise identity. Evaluation of the transported unit gives inverseSection,
since the model equivalences are inverse on sections and their comparison units
are identities. For uniqueness, two units satisfying this equation agree by
sectionwise extensionality of module morphisms and natural transformations.
An adjunction is determined by its unit: the Hom equivalence sends f to the unit
followed by the right-adjoint image of f, so equal units give equal Hom equivalences,
and their inverses and counits agree. -/
theorem adjunction_exists {X Z : Scheme.{u}} (i : Z ⟶ X) (R : Rings X) :
    ∃! ai : inverse i R ⊣ proEtaleRingedDirectImage i R,
      ∀ (F : Modules R) (V : X.ProEt) (s : F.val.obj (op V)),
        (ai.unit.app F).val.app (op V) s = inverseSection i F V s := by
  refine ⟨AlgebraicGeometry.Scheme.canonicalAdjunction i R, ?_, ?_⟩
  · intro F V s
    exact AlgebraicGeometry.Scheme.canonicalUnit_sections i R F (op V) s
  · intro ai hai
    apply Adjunction.ext
    ext F V s
    exact (hai F V.unop s).trans
      (AlgebraicGeometry.Scheme.canonicalUnit_sections i R F V s).symm


/-- The canonical module adjunction, selected from the unique unit-normalized
characterization. Its data are determined by the actual inverse-image section map.
Source: Stacks, Tags 03D2, 03D3 and 09AA; the canonical adjunct in the statement
(blueprint: lem-weil-pbc-proetale-closed-underived-projection). -/
noncomputable def adjunction {X Z : Scheme.{u}} (i : Z ⟶ X) (R : Rings X) :
    inverse i R ⊣ proEtaleRingedDirectImage i R :=
  Classical.choose (adjunction_exists i R)

/-- The projection map is the specified adjunct of the normalized tensor comparison
followed by the counit on the first factor. No isomorphism or arbitrary map is chosen.
Source: Stacks, Tags 03EL and 09AA; the adjunct formula in the statement
(blueprint: lem-weil-pbc-proetale-closed-underived-projection). -/
noncomputable def projection {X Z : Scheme.{u}} (i : Z ⟶ X) (R : Rings X)
    (M : Modules (inverseRing i R)) (F : Modules R) :
    tensor ((proEtaleRingedDirectImage i R).obj M) F ⟶
      (proEtaleRingedDirectImage i R).obj (tensor M ((inverse i R).obj F)) :=
  ((adjunction i R).homEquiv _ _)
    (comparison i R ((proEtaleRingedDirectImage i R).obj M) F ≫
      tensorMap ((adjunction i R).counit.app M) (𝟙 ((inverse i R).obj F)))

/-- The ring sheaf B regarded as an R-module through the given ring morphism.
Source: Stacks, Section 03EK; the coefficient clause
(blueprint: lem-weil-pbc-proetale-closed-underived-projection). -/
noncomputable abbrev coefficientModule {X : Scheme.{u}} {R B : Rings X} (a : R ⟶ B) :
    Modules R :=
  (restrict a).obj (SheafOfModules.unit (proEtaleModuleCoefficients B))

/-- The coefficient clause expressed using module sheaves and prescribed actions.
The isomorphisms eS and eT identify their restricted R-modules with the actual tensor
objects. Their pure-tensor equations prescribe the B-actions on the second factors.
The isomorphism eB identifies the inverse image of the regular module with the
inverse-image ring, normalized by the actual ring and module units. The B-linear map
p has exactly the original projection as its underlying map. Its target is the actual
direct image over B, so its action is through B to i_*i^{-1}B. This packages B-linearity
without identifying unequal coefficient categories or replacing the projection map.
Source: Stacks, Section 03EK and Tag 03EL; the coefficient clause
(blueprint: lem-weil-pbc-proetale-closed-underived-projection). -/
def CoefficientLinear {X Z : Scheme.{u}} (i : Z ⟶ X) (R : Rings X)
    (M : Modules (inverseRing i R)) (B : Rings X) (a : R ⟶ B) : Prop :=
  ∃ eB : (inverse i R).obj (coefficientModule a) ≅
      (restrict (inverseRingMap i a)).obj
        (SheafOfModules.unit (proEtaleModuleCoefficients (inverseRing i B))),
    (∀ (V : X.ProEt) (b : B.obj.obj (op V)),
      eB.hom.val.app (op ((proEtaleBaseChange i).obj V))
        (inverseSection i (coefficientModule a) V b) =
      ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app B).hom.app (op V) b) ∧
  ∃ (S : Modules B) (T : Modules (inverseRing i B))
    (eS : (restrict a).obj S ≅
      tensor ((proEtaleRingedDirectImage i R).obj M) (coefficientModule a))
    (eT : (restrict (inverseRingMap i a)).obj T ≅
      tensor M ((inverse i R).obj (coefficientModule a))),
    (∀ (V : X.ProEt)
      (m : ((proEtaleRingedDirectImage i R).obj M).val.obj (op V))
      (b c : B.obj.obj (op V)),
      eS.inv.val.app (op V)
        (pure ((proEtaleRingedDirectImage i R).obj M) (coefficientModule a) V m (c * b)) =
      c • @id (S.val.obj (op V)) (eS.inv.val.app (op V)
        (pure ((proEtaleRingedDirectImage i R).obj M) (coefficientModule a) V m b))) ∧
    (∀ (W : Z.ProEt) (m : M.val.obj (op W))
      (b c : (inverseRing i B).obj.obj (op W)),
      eT.inv.val.app (op W)
        (pure M ((inverse i R).obj (coefficientModule a)) W m
          (eB.inv.val.app (op W) (c * b))) =
      c • @id (T.val.obj (op W)) (eT.inv.val.app (op W)
        (pure M ((inverse i R).obj (coefficientModule a)) W m
          (eB.inv.val.app (op W) b)))) ∧
    ∃ p : S ⟶ (proEtaleRingedDirectImage i B).obj T,
      IsIso p ∧ ∀ (V : X.ProEt)
        (x : (tensor ((proEtaleRingedDirectImage i R).obj M)
          (coefficientModule a)).val.obj (op V)),
        p.val.app (op V) (eS.inv.val.app (op V) x) =
        eT.inv.val.app (op ((proEtaleBaseChange i).obj V))
          ((projection i R M (coefficientModule a)).val.app (op V) x)

private theorem adjunction_unit_sections {X Z : Scheme.{u}} (i : Z ⟶ X) (R : Rings X)
    (F : Modules R) (V : X.ProEt) (s : F.val.obj (op V)) :
    ((adjunction i R).unit.app F).val.app (op V) s = inverseSection i F V s :=
  (Classical.choose_spec (adjunction_exists i R)).1 F V s

private noncomputable def regularInverseIso {X Z : Scheme.{u}} (i : Z ⟶ X)
    (B : Rings X) : (inverse i B).obj (SheafOfModules.unit (proEtaleModuleCoefficients B)) ≅
      SheafOfModules.unit (proEtaleModuleCoefficients (inverseRing i B)) := by
  let : (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : Z.ProEt ⥤ proEtaleSiteModel Z).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Z.ProEt)).functor.IsEquivalence
  have : PreservesFiniteLimits (proEtaleModelBaseChange i) := by
    dsimp only [proEtaleModelBaseChange]
    infer_instance
  have : (proEtaleModelBaseChange i).Final := inferInstance
  exact (proEtaleModuleFromModel _).mapIso
    (asIso (SheafOfModules.pullbackObjUnitToUnit (proEtaleModelRingUnit i B)))

private theorem regularInverseIso_sections {X Z : Scheme.{u}} (i : Z ⟶ X)
    (B : Rings X) (V : X.ProEt) (b : B.obj.obj (op V)) :
    (regularInverseIso i B).hom.val.app (op ((proEtaleBaseChange i).obj V))
        (inverseSection i (SheafOfModules.unit (proEtaleModuleCoefficients B)) V b) =
      ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app B).hom.app (op V) b := by
  let φ := proEtaleModelRingUnit i B
  have h := ((SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv _ _).apply_symm_apply
    (SheafOfModules.unitToPushforwardObjUnit φ)
  have h' := congrArg (fun k ↦ k.val.app (op (AsSmall.up.obj V)) b) h
  change _ = _ at h'
  exact h'

attribute [local irreducible] regularInverseIso proEtaleModuleInverseImage
  inverseSection scalarIdentification

private noncomputable def coefficientInverseIso {X Z : Scheme.{u}} (i : Z ⟶ X)
    {R B : Rings X} (a : R ⟶ B) :
    (inverse i R).obj (coefficientModule a) ≅
      (restrict (inverseRingMap i a)).obj
        (SheafOfModules.unit (proEtaleModuleCoefficients (inverseRing i B))) :=
  scalarIdentification i a (SheafOfModules.unit (proEtaleModuleCoefficients B)) ≪≫
    (restrict (inverseRingMap i a)).mapIso (regularInverseIso i B)

private theorem coefficientInverseIso_sections {X Z : Scheme.{u}} (i : Z ⟶ X)
    {R B : Rings X} (a : R ⟶ B) (V : X.ProEt) (b : B.obj.obj (op V)) :
    (coefficientInverseIso i a).hom.val.app (op ((proEtaleBaseChange i).obj V))
        (inverseSection i (coefficientModule a) V b) =
      ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app B).hom.app (op V) b := by
  have h : (scalarIdentification i a
      (SheafOfModules.unit (proEtaleModuleCoefficients B))).hom.val.app
        (op ((proEtaleBaseChange i).obj V))
        (inverseSection i (coefficientModule a) V b) =
      inverseSection i (SheafOfModules.unit (proEtaleModuleCoefficients B)) V b := by
    unfold scalarIdentification
    exact (Classical.choose_spec
      (scalarIdentification_exists i a (SheafOfModules.unit
        (proEtaleModuleCoefficients B)))).1 V b
  unfold coefficientInverseIso
  change (regularInverseIso i B).hom.val.app (op ((proEtaleBaseChange i).obj V))
    ((scalarIdentification i a (SheafOfModules.unit (proEtaleModuleCoefficients B))).hom.val.app
      (op ((proEtaleBaseChange i).obj V))
      (inverseSection i (coefficientModule a) V b)) = _
  exact (congrArg ((regularInverseIso i B).hom.val.app
    (op ((proEtaleBaseChange i).obj V))) h).trans (regularInverseIso_sections i B V b)

attribute [local irreducible] coefficientInverseIso

private noncomputable abbrev coefficientMap {X : Scheme.{u}} {R B : Rings X}
    (a : R ⟶ B) : proEtaleModuleCoefficients R ⟶ proEtaleModuleCoefficients B :=
  (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a

section
universe s h
variable {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]
  {R₀ B₀ : Sheaf J RingCat.{u + 1}}

private noncomputable def restrictSheafification
    (a : R₀ ⟶ B₀) (P : PresheafOfModules.{u + 1} B₀.obj) :
    (PresheafOfModules.sheafification.{u + 1} (𝟙 R₀.obj)).obj
      ((PresheafOfModules.restrictScalars
        a.hom).obj P) ⟶
      (SheafOfModules.restrictScalars a).obj
        ((PresheafOfModules.sheafification.{u + 1} (𝟙 B₀.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv.{u + 1} (𝟙 _)).symm
    ((PresheafOfModules.restrictScalars
      a.hom).map
        ((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 _)).unit.app P))

private theorem restrictSheafification_isIso
    (a : R₀ ⟶ B₀) (P : PresheafOfModules.{u + 1} B₀.obj) :
    IsIso (restrictSheafification a P) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf R₀)]
  have he : (SheafOfModules.toSheaf _).map (restrictSheafification a P) = 𝟙 _ := by
    unfold restrictSheafification
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply ((CategoryTheory.sheafificationAdjunction
      J AddCommGrpCat.{u + 1}).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    change (PresheafOfModules.toPresheaf B₀.obj).map
      ((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 B₀.obj)).unit.app P) =
        CategoryTheory.toSheafify J P.presheaf
    exact PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _
  rw [he]
  infer_instance

private theorem restrictSheafification_unit
    (a : R₀ ⟶ B₀) (P : PresheafOfModules.{u + 1} B₀.obj)
    (V : Cᵒᵖ) (x : P.obj V) :
    (restrictSheafification a P).val.app V
      (((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 R₀.obj)).unit.app
        ((PresheafOfModules.restrictScalars
          a.hom).obj P)).app V x) =
      ((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 B₀.obj)).unit.app P).app V x := by
  have h := (PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (P := (PresheafOfModules.restrictScalars
      a.hom).obj P)
    (F := (SheafOfModules.restrictScalars a).obj
      ((PresheafOfModules.sheafification.{u + 1} (𝟙 B₀.obj)).obj P)) (𝟙 R₀.obj)).apply_symm_apply
    ((PresheafOfModules.restrictScalars
      a.hom).map
        ((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 B₀.obj)).unit.app P))
  exact congrArg (fun k ↦ k.app V x) h

end

private noncomputable def rawExtensionIso {X : Scheme.{u}} {R B : Rings X}
    (a : R ⟶ B) (M : Modules R) :
    SheafOfModules.siteTensorPresheaf M.val (coefficientModule a).val ≅
      (PresheafOfModules.restrictScalars
        (coefficientMap a).hom).obj
          (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
            (J := ProEt.topology X) a M) := by
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · exact (TensorProduct.comm (R.obj.obj V) (M.val.obj V)
      ((coefficientModule a).val.obj V)).toModuleIso
  · intro V W f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m b
    change _ = SheafOfModules.changeOfRingsMapOfUniverses.{u, u + 1, u + 1, u + 1} a M f
      (b ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] m)
    change (B.obj.map f b) ⊗ₜ[R.obj.obj W, (a.hom.app W).hom] (M.val.map f m) = _
    exact (SheafOfModules.changeOfRingsMap_tmulOfUniverses.{u, u + 1, u + 1, u + 1}
      a M f b m).symm

private noncomputable def extensionTensorIso {X : Scheme.{u}} {R B : Rings X}
    (a : R ⟶ B) (M : Modules R) :
    (restrict a).obj (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (J := ProEt.topology X) a M) ≅
      tensor M (coefficientModule a) := by
  have := restrictSheafification_isIso (coefficientMap a)
    (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
            (J := ProEt.topology X) a M)
  exact ((PresheafOfModules.sheafification.{u + 1} (𝟙 (proEtaleModuleCoefficients R).obj)).mapIso
    (rawExtensionIso a M) ≪≫
      asIso (restrictSheafification (coefficientMap a)
        (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
            (J := ProEt.topology X) a M))).symm

private theorem extensionTensorIso_pure {X : Scheme.{u}} {R B : Rings X}
    (a : R ⟶ B) (M : Modules R) (V : X.ProEt) (m : M.val.obj (op V))
    (b : B.obj.obj (op V)) :
    (extensionTensorIso a M).inv.val.app (op V) (pure M (coefficientModule a) V m b) =
      ((PresheafOfModules.sheafificationAdjunction.{u + 1}
        (𝟙 (proEtaleModuleCoefficients B).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
            (J := ProEt.topology X) a M)).app (op V)
            (b ⊗ₜ[R.obj.obj (op V), (a.hom.app (op V)).hom] m) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 (proEtaleModuleCoefficients R).obj)
  have hn := congrArg (fun k ↦ k.app (op V) (m ⊗ₜ[R.obj.obj (op V)]
      (show (coefficientModule a).val.obj (op V) from b)))
    (adj.unit.naturality (rawExtensionIso a M).hom)
  change (restrictSheafification (coefficientMap a) _).val.app (op V)
    (((PresheafOfModules.sheafification.{u + 1} (𝟙 (proEtaleModuleCoefficients R).obj)).map
      (rawExtensionIso a M).hom).val.app (op V)
        (pure M (coefficientModule a) V m b)) = _
  change _ = ((PresheafOfModules.sheafification.{u + 1}
    (𝟙 (proEtaleModuleCoefficients R).obj)).map (rawExtensionIso a M).hom).val.app (op V)
      (pure M (coefficientModule a) V m b) at hn
  rw [← hn]
  exact restrictSheafification_unit (coefficientMap a) _ _ _

private theorem extensionTensorIso_smul {X : Scheme.{u}} {R B : Rings X}
    (a : R ⟶ B) (M : Modules R) (V : X.ProEt) (m : M.val.obj (op V))
    (b c : B.obj.obj (op V)) :
    (extensionTensorIso a M).inv.val.app (op V)
        (pure M (coefficientModule a) V m (c * b)) =
      c • @id ((SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (J := ProEt.topology X) a M).val.obj (op V))
        ((extensionTensorIso a M).inv.val.app (op V)
          (pure M (coefficientModule a) V m b)) := by
  rw [extensionTensorIso_pure, extensionTensorIso_pure]
  change _ = c • (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 (proEtaleModuleCoefficients B).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
            (J := ProEt.topology X) a M)).app (op V)) _
  rw [← map_smul]
  rfl

private theorem tensorSecond_id {X : Scheme.{u}} {R : Rings X} (M N : Modules R) :
    SheafOfModules.siteSheafTensorSecondMap M (𝟙 N) = 𝟙 (tensor M N) := by
  let S := PresheafOfModules.sheafification.{u + 1} (𝟙 (proEtaleModuleCoefficients R).obj)
  change S.map _ = 𝟙 _
  rw [← S.map_id]
  congr 1
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

private theorem tensorSecond_comp {X : Scheme.{u}} {R : Rings X}
    (M : Modules R) {N N' N'' : Modules R} (b : N ⟶ N') (c : N' ⟶ N'') :
    SheafOfModules.siteSheafTensorSecondMap M (b ≫ c) =
      SheafOfModules.siteSheafTensorSecondMap M b ≫
        SheafOfModules.siteSheafTensorSecondMap M c := by
  let S := PresheafOfModules.sheafification.{u + 1} (𝟙 (proEtaleModuleCoefficients R).obj)
  change S.map _ = S.map _ ≫ S.map _
  rw [← S.map_comp]
  congr 1
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

private theorem tensorMap_id {X : Scheme.{u}} {R : Rings X} (M N : Modules R) :
    tensorMap (𝟙 M) (𝟙 N) = 𝟙 (tensor M N) := by
  unfold tensorMap
  rw [tensorSecond_id, Category.comp_id]
  exact (SheafOfModules.siteSheafTensorRight N).map_id M

private theorem tensorMap_comp {X : Scheme.{u}} {R : Rings X}
    {M M' M'' N N' N'' : Modules R}
    (a : M ⟶ M') (a' : M' ⟶ M'') (b : N ⟶ N') (b' : N' ⟶ N'') :
    tensorMap (a ≫ a') (b ≫ b') = tensorMap a b ≫ tensorMap a' b' := by
  simp only [tensorMap, Functor.map_comp, tensorSecond_comp, Category.assoc]
  rw [← Category.assoc (SheafOfModules.siteSheafTensorSecondMap M' b)]
  rw [← SheafOfModules.siteSheafTensorSecondMap_naturality a' b]
  simp only [Category.assoc]

private noncomputable def tensorIso {X : Scheme.{u}} {R : Rings X}
    {M M' N N' : Modules R} (e : M ≅ M') (f : N ≅ N') :
    tensor M N ≅ tensor M' N' where
  hom := tensorMap e.hom f.hom
  inv := tensorMap e.inv f.inv
  hom_inv_id := by rw [← tensorMap_comp, e.hom_inv_id, f.hom_inv_id, tensorMap_id]
  inv_hom_id := by rw [← tensorMap_comp, e.inv_hom_id, f.inv_hom_id, tensorMap_id]

private theorem tensorMap_pure {X : Scheme.{u}} {R : Rings X}
    {M M' N N' : Modules R} (a : M ⟶ M') (b : N ⟶ N') (V : X.ProEt)
    (m : M.val.obj (op V)) (n : N.val.obj (op V)) :
    (tensorMap a b).val.app (op V) (pure M N V m n) =
      pure M' N' V (a.val.app (op V) m) (b.val.app (op V) n) := by
  let L := PresheafOfModules.sheafification.{u + 1}
    (𝟙 (proEtaleModuleCoefficients R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 (proEtaleModuleCoefficients R).obj)
  let f := SheafOfModules.siteTensorHom a.val N.val ≫
    SheafOfModules.siteTensorSecondMap M'.val b.val
  have hn := congrArg (fun k ↦ k.app (op V) (m ⊗ₜ[R.obj.obj (op V)] n))
    (adj.unit.naturality f)
  change (L.map _ ≫ L.map _).val.app (op V) (pure M N V m n) = _
  rw [← L.map_comp]
  exact hn.symm

private theorem projection_pure {X Z : Scheme.{u}} (i : Z ⟶ X) (R : Rings X)
    (M : Modules (inverseRing i R)) (F : Modules R) (V : X.ProEt)
    (m : ((proEtaleRingedDirectImage i R).obj M).val.obj (op V))
    (f : F.val.obj (op V)) :
    (projection i R M F).val.app (op V)
        (pure ((proEtaleRingedDirectImage i R).obj M) F V m f) =
      pure M ((inverse i R).obj F) ((proEtaleBaseChange i).obj V) m
        (inverseSection i F V f) := by
  have htriangle := congrArg (fun k ↦ k.val.app (op V) m)
    ((adjunction i R).right_triangle_components M)
  change ((adjunction i R).counit.app M).val.app (op ((proEtaleBaseChange i).obj V))
    (((adjunction i R).unit.app ((proEtaleRingedDirectImage i R).obj M)).val.app
      (op V) m) = m at htriangle
  rw [adjunction_unit_sections] at htriangle
  unfold projection
  rw [Adjunction.homEquiv_unit]
  change (tensorMap _ _).val.app _ ((comparison i R _ _).val.app _
    (((adjunction i R).unit.app _).val.app (op V) _)) = _
  rw [adjunction_unit_sections]
  have hc := (Classical.choose_spec (comparison_exists i R
    ((proEtaleRingedDirectImage i R).obj M) F)).1 V m f
  change (comparison i R _ _).val.app _ _ = _ at hc
  erw [hc]
  erw [tensorMap_pure, htriangle]
  rfl

private theorem tensorCounit_isIso {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (R : Rings X) (M : Modules (inverseRing i R))
    (F : Modules R) :
    IsIso (tensorMap ((adjunction i R).counit.app M) (𝟙 ((inverse i R).obj F))) := by
  have := proEtale_ringed_closed_counit i R (adjunction i R) M
  unfold tensorMap
  rw [tensorSecond_id, Category.comp_id]
  infer_instance

private theorem projection_natural {X Z : Scheme.{u}} (i : Z ⟶ X) (R : Rings X)
    (M M' : Modules (inverseRing i R)) (F F' : Modules R)
    (a : M ⟶ M') (b : F ⟶ F') :
    tensorMap ((proEtaleRingedDirectImage i R).map a) b ≫ projection i R M' F' =
      projection i R M F ≫
        (proEtaleRingedDirectImage i R).map (tensorMap a ((inverse i R).map b)) := by
  unfold projection
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  congr 1
  have hn := (inverseImage_tensor_comparison (𝟙 Z) i R
    ((proEtaleRingedDirectImage i R).obj M) F).2.2.1
    ((proEtaleRingedDirectImage i R).obj M') F'
    ((proEtaleRingedDirectImage i R).map a) b
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← tensorMap_comp, Category.comp_id, Category.id_comp]
  congr 2
  exact (adjunction i R).counit.naturality a

private theorem projection_isIso {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ) (R : Rings X)
    (M : Modules (inverseRing i R)) (F : Modules R) : IsIso (projection i R M F) := by
  obtain ⟨_, _, ai, aj, hc, _, hz, _, _, _, _, _, hs, _⟩ :=
    proEtale_ringed_open_closed i U hU R
  let H := tensor ((proEtaleRingedDirectImage i R).obj M) F
  obtain ⟨e, _, _⟩ := SheafOfModules.exists_localizedSiteTensorRestriction.{u + 1, u, u + 1, u + 1}
    (ProEt.topology X) R U
  have hres : IsZero ((SheafOfModules.overFunctor (proEtaleModuleCoefficients R) U).obj H) :=
    ((SheafOfModules.siteSheafTensorRight (A := R.over U) (F.over U)).map_isZero
      (hz M)).of_iso (e _ _)
  have : (proEtaleRingedExtensionByZero U R).IsLeftAdjoint := aj.isLeftAdjoint
  have hleft := (proEtaleRingedExtensionByZero U R).map_isZero hres
  let T := ComposableArrows.mk₂ (aj.counit.app H) (ai.unit.app H)
  have hT : T.Exact := (hs H).2.2
  have he := (T.exact₂_iff hT.toIsComplex).1 hT
  have : Mono (ai.unit.app H) := he.mono_g (hleft.eq_of_src _ _)
  have : Epi (ai.unit.app H) := (hs H).2.1
  have : IsIso (ai.unit.app H) := isIso_of_mono_of_epi _
  have : IsIso ai.counit := by
    have := hc
    exact NatIso.isIso_of_isIso_app _
  have : (proEtaleRingedDirectImage i R).Full := ai.fullyFaithfulROfIsIsoCounit.full
  have : (proEtaleRingedDirectImage i R).Faithful := ai.fullyFaithfulROfIsIsoCounit.faithful
  have : IsIso ((adjunction i R).unit.app H) :=
    (adjunction i R).isIso_unit_app_iff_mem_essImage.2
      ⟨(inverse i R).obj H, ⟨(asIso (ai.unit.app H)).symm⟩⟩
  have := (inverseImage_tensor_comparison (𝟙 Z) i R
    ((proEtaleRingedDirectImage i R).obj M) F).1
  have := tensorCounit_isIso i R M F
  change IsIso (((adjunction i R).homEquiv _ _) _)
  rw [Adjunction.homEquiv_unit]
  infer_instance

private noncomputable def directRestrictIso {X Z : Scheme.{u}} (i : Z ⟶ X)
    {R B : Rings X} (a : R ⟶ B) (T : Modules (inverseRing i B)) :
    (restrict a).obj ((proEtaleRingedDirectImage i B).obj T) ≅
      (proEtaleRingedDirectImage i R).obj ((restrict (inverseRingMap i a)).obj T) := by
  let P := (restrict a).obj ((proEtaleRingedDirectImage i B).obj T)
  let Q := (proEtaleRingedDirectImage i R).obj ((restrict (inverseRingMap i a)).obj T)
  have h (V : X.ProEtᵒᵖ) (r : R.obj.obj V) :
      ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app B).hom.app V
          (a.hom.app V r) =
        (inverseRingMap i a).hom.app ((proEtaleBaseChange i).op.obj V)
          (((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app R).hom.app V r) :=
    congrArg (fun k ↦ k.hom.app V r)
      ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.naturality a)
  let f : P ⟶ Q :=
    { val :=
      { app := fun V ↦ ModuleCat.ofHom (X := P.val.obj V) (Y := Q.val.obj V)
          { toFun := id
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun r t ↦ by
              exact congrArg (fun z : (inverseRing i B).obj.obj
                ((proEtaleBaseChange i).op.obj V) ↦
                  z • @id (T.val.obj ((proEtaleBaseChange i).op.obj V)) t) (h V r) }
        naturality := by intros; rfl } }
  let g : Q ⟶ P :=
    { val :=
      { app := fun V ↦ ModuleCat.ofHom (X := Q.val.obj V) (Y := P.val.obj V)
          { toFun := id
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun r t ↦ by
              exact congrArg (fun z : (inverseRing i B).obj.obj
                ((proEtaleBaseChange i).op.obj V) ↦
                  z • @id (T.val.obj ((proEtaleBaseChange i).op.obj V)) t) (h V r).symm }
        naturality := by intros; rfl } }
  exact ⟨f, g, by ext; rfl, by ext; rfl⟩

attribute [local irreducible] extensionTensorIso

private theorem coefficient_linear {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ) (R : Rings X)
    (M : Modules (inverseRing i R)) (B : Rings X) (a : R ⟶ B) :
    CoefficientLinear i R M B a := by
  let eB := coefficientInverseIso i a
  let c : inverseRing i R ⟶ inverseRing i B := inverseRingMap i a
  let T : Modules (inverseRing i B) :=
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} (J := ProEt.topology Z) c M
  let eT : (restrict c).obj T ≅ tensor M ((inverse i R).obj (coefficientModule a)) :=
    extensionTensorIso c M ≪≫ tensorIso (Iso.refl M) eB.symm
  have ht (W : Z.ProEt) (m : M.val.obj (op W)) (b : (inverseRing i B).obj.obj (op W)) :
      eT.inv.val.app (op W)
        (pure M ((inverse i R).obj (coefficientModule a)) W m (eB.inv.val.app (op W) b)) =
      (extensionTensorIso c M).inv.val.app (op W)
        (pure M (coefficientModule c) W m b) := by
    change (extensionTensorIso c M).inv.val.app (op W)
      ((tensorMap (𝟙 M) eB.hom).val.app (op W) _) = _
    rw [tensorMap_pure]
    congr 2
    exact congrArg (fun k ↦ k.val.app (op W) b) eB.inv_hom_id
  have ht' (W : Z.ProEt) (m : M.val.obj (op W))
      (b : ((inverse i R).obj (coefficientModule a)).val.obj (op W)) :
      eT.inv.val.app (op W)
        (pure M ((inverse i R).obj (coefficientModule a)) W m b) =
      (extensionTensorIso c M).inv.val.app (op W)
        (pure M (coefficientModule c) W m (eB.hom.val.app (op W) b)) := by
    change (extensionTensorIso c M).inv.val.app (op W)
      ((tensorMap (𝟙 M) eB.hom).val.app (op W) _) = _
    rw [tensorMap_pure]
    rfl
  have hproj := projection_isIso i U hU R M (coefficientModule a)
  let S := (proEtaleRingedDirectImage i B).obj T
  let eS : (restrict a).obj S ≅
      tensor ((proEtaleRingedDirectImage i R).obj M) (coefficientModule a) :=
    directRestrictIso i a T ≪≫ (proEtaleRingedDirectImage i R).mapIso eT ≪≫
      (asIso (projection i R M (coefficientModule a))).symm
  have hs (V : X.ProEt)
      (x : (tensor ((proEtaleRingedDirectImage i R).obj M) (coefficientModule a)).val.obj
        (op V)) :
      eS.inv.val.app (op V) x =
        eT.inv.val.app (op ((proEtaleBaseChange i).obj V))
          ((projection i R M (coefficientModule a)).val.app (op V) x) := by
    rfl
  refine ⟨eB, coefficientInverseIso_sections i a, S, T, eS, eT, ?_, ?_,
    𝟙 S, inferInstance, ?_⟩
  · intro V m b d
    rw [hs, hs, projection_pure, projection_pure, ht', ht']
    have hB := coefficientInverseIso_sections i a V b
    have hdb := coefficientInverseIso_sections i a V (d * b)
    change eB.hom.val.app _ (inverseSection i (coefficientModule a) V b) = _ at hB
    change eB.hom.val.app _ (inverseSection i (coefficientModule a) V (d * b)) = _ at hdb
    erw [hdb, hB]
    rw [map_mul]
    exact extensionTensorIso_smul c M ((proEtaleBaseChange i).obj V) m _ _
  · intro W m b d
    rw [ht, ht]
    exact extensionTensorIso_smul c M W m b d
  · intro V x
    exact hs V x

/-- The specified projection is invertible, jointly natural, and B-linear under every
commutative coefficient extension. The adjunct uses the actual constructed module
adjunction, fixed by its actual sectionwise unit, with no arbitrary choice and no
hypothesis on coefficients or modules.

Source: Stacks Project, Tags 09AA, 09AH and 03EL; agent-formulated consequence
(blueprint: lem-weil-pbc-proetale-closed-underived-projection).

Proof:
1. Put H = i_*M tensor F and N = M tensor i^{-1}F. The tensor comparison sigma
is invertible by lem-pur-proetale-inverse-image-tensor-comparison. The counit is
invertible by lem-weil-pbc-proetale-ringed-closed-counit, for every adjunction on
these functors. Thus alpha = sigma followed by epsilon_M tensor identity is invertible.
The adjunct formula defining projection is eta_H followed by i_*(alpha).
2. The open restriction of H is zero: inverse image commutes with tensor and the
open restriction of i_*M is zero by lem-weil-pbc-proetale-ringed-open-closed. Tensor
with zero is zero by the sheafified sectionwise construction. Apply the ringed
localization sequence 0 -> j_!j^{-1}H -> H -> i_*i^{-1}H -> 0. Its left term
vanishes, so eta_H is an isomorphism. Quasi-compactness of the open is exactly the
hypothesis required by Tag 09AH.
3. Consequently projection is a composite of isomorphisms, with inverse
 i_*(alpha^{-1}) followed by eta_H^{-1}. Naturality of sigma, the counit and the
unit gives the displayed equation for every pair of module maps.
4. Regard B as an R-module. Applying inverse image to its regular action gives the
unit-normalized eB. Sheafify the sectionwise tensors with the B-action on the B
factor to obtain S and T and their identifications eS and eT. On sections over V,
projection sends m tensor b to m tensor bar(b), where bar is the ring adjunction
unit. Hence projection(m tensor cb) = m tensor bar(c)bar(b), the prescribed target
B-action through B -> i_*i^{-1}B. Locally sections of a sheafified tensor are sums
of pure tensors, so this equality gives a B-linear map p with the specified
underlying projection. Its inverse is B-linear by injectivity of p: apply p to the
two sides of p^{-1}(cy) = c p^{-1}(y). This gives IsIso p, without flatness, finite
presentation, constructibility or any restriction on the ring map. -/
theorem closed_underived_projection {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ) (R : Rings X) :
    (∀ (M : Modules (inverseRing i R)) (F : Modules R), IsIso (projection i R M F)) ∧
    (∀ (M M' : Modules (inverseRing i R)) (F F' : Modules R)
      (a : M ⟶ M') (b : F ⟶ F'),
      tensorMap ((proEtaleRingedDirectImage i R).map a) b ≫ projection i R M' F' =
        projection i R M F ≫
          (proEtaleRingedDirectImage i R).map (tensorMap a ((inverse i R).map b))) ∧
    (∀ (M : Modules (inverseRing i R)) (B : Rings X) (a : R ⟶ B),
      CoefficientLinear i R M B a) := by
  exact ⟨projection_isIso i U hU R, projection_natural i R, coefficient_linear i U hU R⟩

end AlgebraicGeometry.ProEtaleClosedProjection
