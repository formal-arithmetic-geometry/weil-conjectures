/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.ConstructibleSheaf.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
import all Sheaf.Paper.ProEtaleConstantModuleConstructibility
import all Sheaf.Paper.ProEtaleConstantModulePullbackEncoding
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver

/-!
# Surjective closed immersions and ordinary module sheaves

Source: Stacks Project, Tag 09AB (lemma-thickening), Tag 04DZ
(theorem-topological-invariance), and Modules on Sites, lemma-pullback-locally-constant
(blueprint: lem-sfb-surjective-closed-module-invariance).

The two local-model predicates expand the finite and finite-projective clauses of this
node. They use the existing constant sheaves and localized restrictions. The Boolean
selects whether a finite-free splitting is required; it does not change the chosen site.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The finite local models in this node on the etale site. For `projective = true`,
each model is explicitly a retract of a finite free module; for `false`, only finiteness
is required. This refines the existing `LocallyConstantDatum`, with the same covers and
localized constant module sheaves, rather than using a stalk-finiteness surrogate.
Source: Stacks, Modules on Sites, lemma-pullback-locally-constant, with the finite-model
clause of blueprint det-sf-flat-model-generation
(blueprint: lem-sfb-surjective-closed-module-invariance). -/
def sfbEtaleFiniteLocalModels {Y : Scheme.{u}} (A : Type (u + 1)) [CommRing A]
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) (projective : Bool) : Prop :=
  ∃ d : LocallyConstantDatum H, ∀ j : d.cover.I₀,
    ∃ M : ModuleCat.{u + 1} A, Finite M ∧
      Nonempty (H.over (d.cover.etalePrecoverageToEtale j) ≅
        (constantSheaf
          (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale j))
          (ModuleCat.{u + 1} A)).obj M) ∧
      (projective = true → ∃ (n : ℕ) (i : M →ₗ[A] (Fin n → A))
        (r : (Fin n → A) →ₗ[A] M), r.comp i = LinearMap.id)

/-- The finite local models in this node on the original small pro-etale ringed site.
This is the covering datum of `IsLocallyConstantProEtaleModuleSheaf` with finite models,
and, when requested, explicit finite-free splittings. No etale-origin condition occurs.
Source: Stacks, Modules on Sites, lemma-pullback-locally-constant, and Tag 09AB;
blueprint det-sf-flat-model-generation, clause (2)
(blueprint: lem-sfb-surjective-closed-module-invariance). -/
def sfbProEtaleFiniteLocalModels (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (H : proEtaleRingModules Y (proEtaleConstantRing Y A)) (projective : Bool) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → Y.ProEt)
    (f : ∀ j : I, U j ⟶ ProEt.mk (𝟙 Y)),
    Presieve.ofArrows U f ∈ (ProEt.precoverage Y).coverings _ ∧
      ∀ j : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} A), Finite M ∧
        Nonempty (H.over (U j) ≅ proEtaleConstantModuleSheafOver Y A (U j) M) ∧
        (projective = true → ∃ (n : ℕ)
          (i : M →ₗ[ULift.{u + 1, u} A] (Fin n → ULift.{u + 1, u} A))
          (r : (Fin n → ULift.{u + 1, u} A) →ₗ[ULift.{u + 1, u} A] M),
          r.comp i = LinearMap.id)

private theorem sfbEtale_over_model_iff {Y : Scheme.{u}}
    (A : Type (u + 1)) [CommRing A]
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) (U : Y.Etale)
    (M : ModuleCat.{u + 1} A) :
    Nonempty (H.over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} A)).obj M) ↔
    Nonempty ((Etale.upperStar (ModuleCat.{u + 1} A) U.hom).obj H ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) := by
  let E := Etale.overSheafEquiv U (ModuleCat.{u + 1} A)
  let e := overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} A) U H
  let c := (Etale.overEquiv U).constantSheafSheafCongrIso
    (Y.smallEtaleTopology.over U) U.left.smallEtaleTopology (ModuleCat.{u + 1} A)
    CategoryTheory.Over.mkIdTerminal
  constructor
  · rintro ⟨i⟩
    exact ⟨e.symm ≪≫ E.functor.mapIso i ≪≫ c.app M⟩
  · rintro ⟨i⟩
    exact ⟨E.functor.preimageIso (e ≪≫ i ≪≫ (c.app M).symm)⟩

/-- Surjective closed restriction on the etale site: the actual adjunction is an
adjoint equivalence, constants pull back to the same module models, and finite local
models, with or without finite-free splittings, are preserved and reflected.
Source: Stacks, Tags 04DZ, 03SI and Modules on Sites, lemma-pullback-locally-constant
(blueprint: lem-sfb-surjective-closed-module-invariance).

Proof: a surjective closed immersion is a universal homeomorphism. The existing
etale topological-invariance theorem applies directly to ModuleCat-valued sheaves,
so both functors are equivalences and the actual adjunction unit and counit are
isomorphisms. The constant comparison is upperStarConstantSheafIso.
For preservation, pull back a trivializing cover and each chosen module isomorphism.
The composition comparisons identify the two pullbacks around the cartesian square;
the constant comparison retains the exact same module M.
For reflection, lift each member of a trivializing cover through the equivalence of
etale sites. The lifts cover Y: lift a point to T, then to a cover member and project
its image in the corresponding fiber product to the lifted member over Y.
On each lifted member, pull the given trivialization back along the isomorphism to
the original member. The composition comparisons identify its source with the
pullback of H. The base-changed universal homeomorphism has fully faithful module
inverse image, so preimageIso descends the trivialization with the same model M.
The localization equivalence and its constant-sheaf comparison convert between
the localized-site and scheme-site presentations throughout. All finiteness proofs,
integers n and splitting maps are reused unchanged. The cover arguments quantify
over points, so empty covers and schemes need no exception. -/
theorem sfbEtale_surjectiveClosed_module_invariance
    {T Y : Scheme.{u}} (h : T ⟶ Y) [IsClosedImmersion h] [Surjective h]
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    IsIso (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit ∧
    IsIso (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).counit ∧
    (Etale.upperStar (ModuleCat.{u + 1} A) h).IsEquivalence ∧
    (Etale.lowerStar (ModuleCat.{u + 1} A) h).IsEquivalence ∧
    (∀ M : ModuleCat.{u + 1} A,
      Nonempty ((Etale.upperStar (ModuleCat.{u + 1} A) h).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) ≅
          (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)) ∧
    (∀ (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) (projective : Bool),
      sfbEtaleFiniteLocalModels A H projective ↔
        sfbEtaleFiniteLocalModels A
          ((Etale.upperStar (ModuleCat.{u + 1} A) h).obj H) projective) := by
  have : (Etale.upperStar (ModuleCat.{u + 1} A) h).IsEquivalence :=
    Etale.isEquivalence_upperStar _ h
  have : (Etale.lowerStar (ModuleCat.{u + 1} A) h).IsEquivalence :=
    Etale.isEquivalence_lowerStar _ h
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro M
    exact ⟨(upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).app M⟩
  · intro H projective
    have : JointlySurjective etalePrecoverage.{u} :=
      inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))
    constructor
    · rintro ⟨d, hd⟩
      let D := ModuleCat.{u + 1} A
      let G := (Etale.upperStar D h).obj H
      have hm (j : d.cover.I₀) :
          ∃ M : D, Finite M ∧
            Nonempty (G.over (Cover.etalePrecoverageToEtale (d.cover.pullback₂ h) j) ≅
              (constantSheaf
                (T.smallEtaleTopology.over (Cover.etalePrecoverageToEtale (d.cover.pullback₂ h) j))
                D).obj M) ∧
            (projective = true → ∃ (n : ℕ) (i : M →ₗ[A] (Fin n → A))
              (r : (Fin n → A) →ₗ[A] M), r.comp i = LinearMap.id) := by
        obtain ⟨M, hM, eM, hp⟩ := hd j
        obtain ⟨iM⟩ := (sfbEtale_over_model_iff A H _ M).mp eM
        let e : (Etale.upperStar D (Limits.pullback.fst (d.cover.f j) h)).obj
            ((Etale.upperStar D (d.cover.f j)).obj H) ≅
            (Etale.upperStar D (Limits.pullback.snd (d.cover.f j) h)).obj G :=
          ((Etale.upperStarComp D (Limits.pullback.fst (d.cover.f j) h)
            (d.cover.f j)).app H).symm ≪≫
            eqToIso (congrArg (fun m ↦ (Etale.upperStar D m).obj H) Limits.pullback.condition) ≪≫
            (Etale.upperStarComp D (Limits.pullback.snd (d.cover.f j) h) h).app H
        let iG := e.symm ≪≫
          (Etale.upperStar D (Limits.pullback.fst (d.cover.f j) h)).mapIso iM ≪≫
          (upperStarConstantSheafIso D (Limits.pullback.fst (d.cover.f j) h)).app M
        exact ⟨M, hM, (sfbEtale_over_model_iff A G _ M).mpr ⟨iG⟩, hp⟩
      refine ⟨⟨d.cover.pullback₂ h, ?_⟩, hm⟩
      intro j
      obtain ⟨M, _, ⟨iM⟩, _⟩ := hm j
      exact Sheaf.isConstant_of_iso _ iM
    · rintro ⟨d, hd⟩
      let D := ModuleCat.{u + 1} A
      let G := (Etale.upperStar D h).obj H
      let V (i : d.cover.I₀) : Y.Etale :=
        h.Etale.objPreimage (d.cover.etalePrecoverageToEtale i)
      let e (i : d.cover.I₀) : h.Etale.obj (V i) ≅ d.cover.etalePrecoverageToEtale i :=
        h.Etale.objObjPreimageIso _
      have hinv (i : d.cover.I₀) :
          (e i).inv.left ≫ Limits.pullback.snd (V i).hom h = d.cover.f i :=
        MorphismProperty.Over.w (e i).inv
      let C : Cover.{u} etalePrecoverage Y :=
        { I₀ := d.cover.I₀
          X i := (V i).left
          f i := (V i).hom
          mem₀ := by
            refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun y ↦ ?_, fun i ↦ (V i).prop⟩
            obtain ⟨x, rfl⟩ := h.surjective y
            obtain ⟨i, x', rfl⟩ := d.cover.exists_eq x
            refine ⟨i, (Limits.pullback.fst (V i).hom h) ((e i).inv.left x'), ?_⟩
            change ((e i).inv.left ≫ Limits.pullback.fst (V i).hom h ≫ (V i).hom) x' =
              (d.cover.f i ≫ h) x'
            rw [Limits.pullback.condition, ← Category.assoc, hinv]
            rfl }
      have hm (i : d.cover.I₀) :
          ∃ M : D, Finite M ∧
            Nonempty (H.over (C.etalePrecoverageToEtale i) ≅
              (constantSheaf (Y.smallEtaleTopology.over (C.etalePrecoverageToEtale i)) D).obj M) ∧
            (projective = true → ∃ (n : ℕ) (j : M →ₗ[A] (Fin n → A))
              (r : (Fin n → A) →ₗ[A] M), r.comp j = LinearMap.id) := by
        obtain ⟨M, hM, eM, hp⟩ := hd i
        obtain ⟨iM⟩ := (sfbEtale_over_model_iff A G _ M).mp eM
        have hsnd : Limits.pullback.snd (V i).hom h = (e i).hom.left ≫ d.cover.f i :=
          (MorphismProperty.Over.w (e i).hom).symm
        let e' : (Etale.upperStar D (Limits.pullback.fst (V i).hom h)).obj
            ((Etale.upperStar D (V i).hom).obj H) ≅
            (Etale.upperStar D (e i).hom.left).obj
              ((Etale.upperStar D (d.cover.f i)).obj G) :=
          ((Etale.upperStarComp D (Limits.pullback.fst (V i).hom h) (V i).hom).app H).symm ≪≫
            eqToIso (congrArg (fun m ↦ (Etale.upperStar D m).obj H) Limits.pullback.condition) ≪≫
            (Etale.upperStarComp D (Limits.pullback.snd (V i).hom h) h).app H ≪≫
            eqToIso (congrArg (fun m ↦ (Etale.upperStar D m).obj G) hsnd) ≪≫
            (Etale.upperStarComp D (e i).hom.left (d.cover.f i)).app G
        have : (Etale.upperStar D (Limits.pullback.fst (V i).hom h)).IsEquivalence :=
          Etale.isEquivalence_upperStar D _
        let iV := (Etale.upperStar D (Limits.pullback.fst (V i).hom h)).preimageIso
          (e' ≪≫ (Etale.upperStar D (e i).hom.left).mapIso iM ≪≫
            (upperStarConstantSheafIso D (e i).hom.left).app M ≪≫
            ((upperStarConstantSheafIso D (Limits.pullback.fst (V i).hom h)).app M).symm)
        exact ⟨M, hM, (sfbEtale_over_model_iff A H _ M).mpr ⟨iV⟩, hp⟩
      refine ⟨⟨C, ?_⟩, hm⟩
      intro i
      obtain ⟨M, _, ⟨iM⟩, _⟩ := hm i
      exact Sheaf.isConstant_of_iso _ iM

private theorem sfbProEtale_fixed_equivalence
    {T Y : Scheme.{u}} (h : T ⟶ Y) [IsClosedImmersion h] [Surjective h]
    (A : Type (u + 1)) [CommRing A] :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) h).IsEquivalence := by
  let L := ProEtale.upperStar (ModuleCat.{u + 1} A) h
  let adj := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h
  have : L.Faithful := by
    constructor
    intro F G f g he
    apply sub_eq_zero.mp
    apply ProEtale.eq_zero_of_forall_upperStar_map_eq_zero A
      (fun _ : PUnit.{u + 1} ↦ h)
      (fun y ↦ ⟨PUnit.unit, h.surjective y⟩)
    intro _
    change L.map (f - g) = 0
    rw [L.map_sub, he, sub_self]
  have (F : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) :
      IsIso (adj.unit.app F) := by
    have : IsIso (L.map (adj.unit.app F) ≫ adj.counit.app (L.obj F)) := by
      have he : L.map (adj.unit.app F) ≫ adj.counit.app (L.obj F) = 𝟙 _ :=
        adj.left_triangle_components F
      rw [he]
      infer_instance
    have : IsIso (L.map (adj.unit.app F)) :=
      IsIso.of_isIso_comp_right _ (adj.counit.app (L.obj F))
    have : Mono (adj.unit.app F) := L.mono_of_mono_map (by infer_instance)
    have : Epi (adj.unit.app F) := L.epi_of_epi_map (by infer_instance)
    exact isIso_of_mono_of_epi _
  exact adj.toEquivalence.isEquivalence_functor

private theorem sfbProEtale_module_equivalence
    {T Y : Scheme.{u}} (h : T ⟶ Y) [IsClosedImmersion h] [Surjective h]
    (A : Type u) [CommRing A] :
    (proEtaleConstantRingPullback A h).IsEquivalence := by
  have := sfbProEtale_fixed_equivalence h (ULift.{u + 1, u} A)
  have := (ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).isEquivalence_right_of_isEquivalence_left
  have := proEtaleModuleRestriction_isEquivalence T A
  have := proEtaleModuleRestriction_isEquivalence Y A
  have : (proEtaleConstantRingPushforward A h ⋙ proEtaleModuleRestriction Y A).IsEquivalence :=
    Functor.isEquivalence_of_iso (directImageComparison h A).symm
  have : (proEtaleConstantRingPushforward A h).IsEquivalence :=
    Functor.isEquivalence_of_comp_right _ (proEtaleModuleRestriction Y A)
  exact (proEtaleConstantRingAdjunction A h).isEquivalence_left_of_isEquivalence_right

private theorem sfbProEtale_over_fixed_model_iff (Y : Scheme.{u})
    (A : Type u) [CommRing A]
    (H : proEtaleRingModules Y (proEtaleConstantRing Y A)) (U : Y.ProEt)
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :
    Nonempty (H.over U ≅ proEtaleConstantModuleSheafOver Y A U M) ↔
    Nonempty (((proEtaleModuleRestriction Y A).obj H).over U ≅
      (constantSheaf ((ProEt.topology Y).over U)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj M) := by
  let J := (ProEt.topology Y).over U
  let R := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A)
  let a := Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit Y A)
  have : Presheaf.IsLocallyInjective J a :=
    (proEtaleConstantRingUnit_over_locallyBijective Y A U).1
  have : Presheaf.IsLocallySurjective J a :=
    (proEtaleConstantRingUnit_over_locallyBijective Y A U).2
  let E := ConstantScalarComparison.restriction J (ULift.{u + 1, u} A) (R.over U) a
  have hc := ConstantScalarComparison.constantComparisonHom_isIso.{u}
    J (ULift.{u + 1, u} A) (R.over U) a M
  let c := asIso (ConstantScalarComparison.constantComparisonHom.{u}
    J (ULift.{u + 1, u} A) (R.over U) a M)
  constructor
  · rintro ⟨e⟩
    exact ⟨E.mapIso e ≪≫ c.symm⟩
  · rintro ⟨e⟩
    exact ⟨(ConstantScalarComparison.restrictionFullyFaithful
      J (ULift.{u + 1, u} A) (R.over U) a).preimageIso (e ≪≫ c)⟩

private theorem sfbProEtale_fixed_over_model_iff {Y : Scheme.{u}}
    (A : Type (u + 1)) [CommRing A]
    (H : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) (U : Y.ProEt)
    (M : ModuleCat.{u + 1} A) :
    Nonempty (H.over U ≅
      (constantSheaf ((ProEt.topology Y).over U) (ModuleCat.{u + 1} A)).obj M) ↔
    Nonempty ((ProEtale.upperStar (ModuleCat.{u + 1} A) U.hom).obj H ≅
      (constantSheaf (ProEt.topology U.left) (ModuleCat.{u + 1} A)).obj M) := by
  have := ProEt.sliceDense Y U
  let E := (ProEt.sliceEquiv Y U).sheafCongr ((ProEt.topology Y).over U)
    (ProEt.topology U.left) (ModuleCat.{u + 1} A)
  let r : E.functor.obj (H.over U) ≅
      (ProEtale.localizationRestriction (ModuleCat.{u + 1} A) U.hom U.prop).obj H :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let e := (ProEtale.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} A) U.hom U.prop).app H
  let c := ((ProEt.sliceEquiv Y U).constantSheafSheafCongrIso
    ((ProEt.topology Y).over U) (ProEt.topology U.left) (ModuleCat.{u + 1} A)
    (Over.mkIdTerminal (X := U))).app M
  constructor
  · rintro ⟨i⟩
    exact ⟨e ≪≫ r.symm ≪≫ E.functor.mapIso i ≪≫ c⟩
  · rintro ⟨i⟩
    exact ⟨E.functor.preimageIso (r ≪≫ e.symm ≪≫ i ≪≫ c.symm)⟩

private def sfbProEtale_fixedModels {Y : Scheme.{u}} (A : Type (u + 1)) [CommRing A]
    (H : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A))
    (P : ModuleCat.{u + 1} A → Prop) : Prop :=
  ∃ C : Cover.{u + 1} proetalePrecoverage Y, ∀ j : C.I₀,
    ∃ M : ModuleCat.{u + 1} A, P M ∧
      Nonempty ((ProEtale.upperStar (ModuleCat.{u + 1} A) (C.f j)).obj H ≅
        (constantSheaf (ProEt.topology (C.X j)) (ModuleCat.{u + 1} A)).obj M)

private theorem sfbProEtale_local_models_iff (Y : Scheme.{u})
    (A : Type u) [CommRing A]
    (H : proEtaleRingModules Y (proEtaleConstantRing Y A)) (projective : Bool) :
    sfbProEtaleFiniteLocalModels Y A H projective ↔
      sfbProEtale_fixedModels (ULift.{u + 1, u} A) ((proEtaleModuleRestriction Y A).obj H)
        (fun M ↦ Finite M ∧ (projective = true → ∃ (n : ℕ)
          (i : M →ₗ[ULift.{u + 1, u} A] (Fin n → ULift.{u + 1, u} A))
          (r : (Fin n → ULift.{u + 1, u} A) →ₗ[ULift.{u + 1, u} A] M),
          r.comp i = LinearMap.id)) := by
  constructor
  · rintro ⟨I, U, f, hf, hm⟩
    have hmem : Presieve.ofArrows (fun j ↦ (U j).left) (fun j ↦ (U j).hom) ∈
        proetalePrecoverage Y := by
      rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hf
      have he (j : I) : (f j).left = (U j).hom := by
        exact (Category.comp_id (f j).left).symm.trans (MorphismProperty.Over.w (f j))
      change Presieve.ofArrows (fun j ↦ (U j).left) (fun j ↦ (f j).left) ∈
        proetalePrecoverage Y at hf
      simpa only [he] using hf
    let C : Cover.{u + 1} proetalePrecoverage Y := ⟨⟨I, fun j ↦ (U j).left,
      fun j ↦ (U j).hom⟩, hmem⟩
    refine ⟨C, fun j ↦ ?_⟩
    obtain ⟨M, hM, e, hp⟩ := hm j
    exact ⟨M, ⟨hM, hp⟩, (sfbProEtale_fixed_over_model_iff _ _ (U j) M).mp
      ((sfbProEtale_over_fixed_model_iff Y A H (U j) M).mp e)⟩
  · rintro ⟨C, hm⟩
    have hw (j : C.I₀) : WeaklyEtale (C.f j) :=
      proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ ⟨j⟩
    let U (j : C.I₀) : Y.ProEt := @ProEt.mk Y (C.X j) (C.f j) (hw j)
    let f (j : C.I₀) : U j ⟶ ProEt.mk (𝟙 Y) :=
      MorphismProperty.Over.homMk (C.f j) (Category.comp_id _)
    refine ⟨C.I₀, U, f, ?_, fun j ↦ ?_⟩
    · rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
      exact C.mem₀
    · obtain ⟨M, ⟨hM, hp⟩, e⟩ := hm j
      exact ⟨M, hM, (sfbProEtale_over_fixed_model_iff Y A H (U j) M).mpr
        ((sfbProEtale_fixed_over_model_iff _ _ (U j) M).mpr e), hp⟩

private noncomputable def sfbProEtale_fixed_constant_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type (u + 1)) [CommRing A]
    (M : ModuleCat.{u + 1} A) :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj
      ((constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)).obj M) ≅
        (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)).obj M :=
  (Functor.isoWhiskerLeft (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A))
    (Functor.sheafPullbackConstruction.sheafPullbackIso (proEtaleBaseChange f)
      (ModuleCat.{u + 1} A) (ProEt.topology Y) (ProEt.topology X)).symm).app M ≪≫
    ((proEtaleBaseChange f).constantSheafsheafPullbackIso (ModuleCat.{u + 1} A)
      (ProEt.topology Y) (ProEt.topology X) (ProEt.isTerminalMkId Y)
      ((ProEt.isTerminalMkId Y).isTerminalObj (proEtaleBaseChange f) _)).app M

private theorem sfbProEtale_fixedModels_of_iso {Y : Scheme.{u}}
    (A : Type (u + 1)) [CommRing A]
    {H G : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)} (e : H ≅ G)
    (P : ModuleCat.{u + 1} A → Prop) (hH : sfbProEtale_fixedModels A H P) :
    sfbProEtale_fixedModels A G P := by
  obtain ⟨C, hm⟩ := hH
  refine ⟨C, fun j ↦ ?_⟩
  obtain ⟨M, hM, ⟨i⟩⟩ := hm j
  exact ⟨M, hM, ⟨(ProEtale.upperStar (ModuleCat.{u + 1} A) (C.f j)).mapIso e.symm ≪≫ i⟩⟩

private theorem sfbProEtale_fixedModels_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A]
    (H : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A))
    (P : ModuleCat.{u + 1} A → Prop) (hH : sfbProEtale_fixedModels A H P) :
    sfbProEtale_fixedModels A ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj H) P := by
  obtain ⟨C, hm⟩ := hH
  refine ⟨C.pullback₂ f, fun j ↦ ?_⟩
  obtain ⟨M, hM, ⟨i⟩⟩ := hm j
  let D := ModuleCat.{u + 1} A
  exact ⟨M, hM, ⟨((ProEtale.upperStarComp D (Limits.pullback.snd (C.f j) f) f).app H).symm
    ≪≫ eqToIso (congrArg (fun g ↦ (ProEtale.upperStar D g).obj H)
      Limits.pullback.condition.symm)
    ≪≫ (ProEtale.upperStarComp D (Limits.pullback.fst (C.f j) f) (C.f j)).app H
    ≪≫ (ProEtale.upperStar D (Limits.pullback.fst (C.f j) f)).mapIso i
    ≪≫ sfbProEtale_fixed_constant_iso _ A M⟩⟩

private theorem sfbProEtale_fixedModels_reflect
    {T Y : Scheme.{u}} (h : T ⟶ Y) [IsClosedImmersion h] [Surjective h]
    (A : Type (u + 1)) [CommRing A]
    (H : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A))
    (P : ModuleCat.{u + 1} A → Prop)
    (hH : sfbProEtale_fixedModels A
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) h).obj H) P) :
    sfbProEtale_fixedModels A H P := by
  let : Precoverage.Small.{u} proetalePrecoverage :=
    inferInstanceAs (Precoverage.Small.{u} (propQCPrecoverage @WeaklyEtale))
  obtain ⟨C₀, hm⟩ := hH
  let C : Cover.{u} proetalePrecoverage T := C₀.restrictIndexOfSmall.{u}
  obtain ⟨B, hB⟩ := exists_cover_refinement_surjective_closed h C
  let B' : Cover.{u + 1} proetalePrecoverage Y :=
    ⟨B.toPreZeroHypercover.restrictIndex (((Equiv.ulift : ULift.{u + 1, u} B.I₀ ≃ B.I₀))), by
      simpa only [PreZeroHypercover.presieve₀_restrictIndex_equiv] using B.mem₀⟩
  refine ⟨B', fun j ↦ ?_⟩
  obtain ⟨a, W, q, p, r, sq, hr⟩ := hB j.down
  obtain ⟨M, hM, ⟨i⟩⟩ := hm (Precoverage.ZeroHypercover.Small.restrictFun.{u} C₀ a)
  have : IsClosedImmersion q := MorphismProperty.of_isPullback sq.flip inferInstance
  have : Surjective q := MorphismProperty.of_isPullback sq.flip inferInstance
  have := sfbProEtale_fixed_equivalence q A
  let D := ModuleCat.{u + 1} A
  let e : (ProEtale.upperStar D q).obj ((ProEtale.upperStar D (B.f j.down)).obj H) ≅
      (constantSheaf (ProEt.topology W) D).obj M :=
    ((ProEtale.upperStarComp D q (B.f j.down)).app H).symm ≪≫
      eqToIso (congrArg (fun g ↦ (ProEtale.upperStar D g).obj H) sq.w) ≪≫
      (ProEtale.upperStarComp D p h).app H ≪≫
      eqToIso (congrArg (fun g ↦ (ProEtale.upperStar D g).obj
        ((ProEtale.upperStar D h).obj H)) hr.symm) ≪≫
      (ProEtale.upperStarComp D r (C.f a)).app
        ((ProEtale.upperStar D h).obj H) ≪≫
      (ProEtale.upperStar D r).mapIso i ≪≫ sfbProEtale_fixed_constant_iso r A M
  exact ⟨M, hM, ⟨(ProEtale.upperStar D q).preimageIso
    (e ≪≫ (sfbProEtale_fixed_constant_iso q A M).symm)⟩⟩

private noncomputable def sfbProEtale_constant_encoding_iso (Y : Scheme.{u})
    (A : Type u) [CommRing A] (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :
    (proEtaleModuleRestriction Y A).obj (proEtaleConstantModuleSheaf Y A M) ≅
      (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj M := by
  letI : LocallySmall.{u + 1} Y.ProEt := ProEt.locallySmall Y
  letI := WeilConjectures.integralCoefficientAbSheafify.{u, 0} Y
  letI := WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} Y
  letI : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  letI : (ProEt.topology Y).WEqualsLocallyBijective
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
      u + 1, u + 2, u + 1} _
  let J : GrothendieckTopology Y.ProEt := ProEt.topology Y
  let R : Sheaf J RingCat.{u + 1} :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing Y A)
  let a : (Functor.const Y.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)) ⟶ R.obj :=
    proEtaleModuleScalarUnit Y A
  have : Presheaf.IsLocallyInjective J a := (proEtaleConstantRingUnit_locallyBijective Y A).1
  have : Presheaf.IsLocallySurjective J a := (proEtaleConstantRingUnit_locallyBijective Y A).2
  have := ConstantScalarComparison.constantComparisonHom_isIso.{u}
    J (ULift.{u + 1, u} A) R a M
  let c := (asIso (ConstantScalarComparison.constantComparisonHom.{u}
    J (ULift.{u + 1, u} A) R a M)).symm
  exact c

/-- Surjective closed restriction on the pro-etale site, for the published ordinary
constant-ring module operations and their tensor-unit-normalized adjunction.
Source: Stacks, Tag 09AB, Modules on Sites, lemma-adjoint-pullback-pushforward-modules
and lemma-pullback-locally-constant; blueprint det-sf-flat-model-generation, clause (2)
(blueprint: lem-sfb-surjective-closed-module-invariance).

Proof: (1) A surjective closed immersion and each base change are universal
homeomorphisms [lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism].
Pro-etale topological invariance makes the actual set unit and counit invertible
[lem-trf-proetale-topological-invariance].
(2) Constant-coefficient inverse image agrees with abelian inverse image and its unit
[lem-pe-constant-left-module-inverse-image]. The finite-product adjunction lifting
identifies this with the set unit [lem-weil-pbc-adjunction-lifts-group-ring-objects].
The canonical constant-ring map and module adjunction give exactly the scalar actions
used here [prop-weil-pbc-proetale-constant-ring-map,
lem-weil-pbc-ringed-topoi-module-adjunction]. The inverse of an invertible underlying
linear map is linear, so the actual module unit is invertible.
(3) Direct image reflects isomorphisms and the triangle identity makes the actual
counit invertible; these natural maps exhibit the quasi-inverse equivalences.
(4) The geometric constant-module comparison preserves every model, without finiteness
[lem-sfb-geometric-inverse-image-constant-module].
(5) Base change preserves weakly etale arrows and fpqc covers
[lem-weil-pbc-weakly-etale-composition-base-change,
lem-galois-fpqc-covering-base-change]. Object inverse image is localized restriction
[lem-sfb-proetale-object-inverse-image-restriction], so a trivializing cover pulls back.
(7) Conversely refine a trivializing cover on T by a cover on Y
[new-lem-weil-pbc-proetale-surjective-closed-cover-refinement]. Each refined member
W is a base change of h and maps to an old cover member; that map is weakly etale
[lem-trf-weakly-etale-between-objects]. Pull its trivialization back. Composition and
localized-restriction compatibility identify its left side with the base-changed
pullback of H. The constant-module comparison identifies its right side with the
same model. Full faithfulness for the base-changed surjective closed immersion lifts
this isomorphism and its inverse to Y; faithfulness identifies their composites.
(8) The unchanged models and splitting maps give both equivalences of finite local
conditions. Empty schemes and empty covers, the zero ring and rank zero are included.
No assertion that every weakly etale object lifts, no Noetherianity and no uniform
nilpotence bound is required. -/
theorem sfbProEtale_surjectiveClosed_module_invariance
    {T Y : Scheme.{u}} (h : T ⟶ Y) [IsClosedImmersion h] [Surjective h]
    (A : Type u) [CommRing A] [Finite A] :
    IsIso (proEtaleConstantRingAdjunction A h).unit ∧
    IsIso (proEtaleConstantRingAdjunction A h).counit ∧
    (proEtaleConstantRingPullback A h).IsEquivalence ∧
    (proEtaleConstantRingPushforward A h).IsEquivalence ∧
    (∀ M : ModuleCat.{u + 1} (ULift.{u + 1, u} A),
      Nonempty ((proEtaleConstantRingPullback A h).obj
        (proEtaleConstantModuleSheaf Y A M) ≅ proEtaleConstantModuleSheaf T A M)) ∧
    (∀ (H : proEtaleRingModules Y (proEtaleConstantRing Y A)) (projective : Bool),
      sfbProEtaleFiniteLocalModels Y A H projective ↔
        sfbProEtaleFiniteLocalModels T A
          ((proEtaleConstantRingPullback A h).obj H) projective) := by
  have := sfbProEtale_module_equivalence h A
  have := (proEtaleConstantRingAdjunction A h).isEquivalence_right_of_isEquivalence_left
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro M
    let E := proEtaleModuleEncoding T A
    obtain ⟨e⟩ := proEtaleModuleRestriction_pullback_of_isIso h A
      (proEtaleConstantModuleSheaf Y A M)
    exact ⟨E.functor.preimageIso (e ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).mapIso
        (sfbProEtale_constant_encoding_iso Y A M) ≪≫
      sfbProEtale_fixed_constant_iso h _ M ≪≫
      (sfbProEtale_constant_encoding_iso T A M).symm)⟩
  · intro H projective
    rw [sfbProEtale_local_models_iff, sfbProEtale_local_models_iff]
    obtain ⟨e⟩ := proEtaleModuleRestriction_pullback_of_isIso h A H
    constructor
    · intro hH
      exact sfbProEtale_fixedModels_of_iso _ e.symm _
        (sfbProEtale_fixedModels_pullback h _ _ _ hH)
    · intro hH
      exact sfbProEtale_fixedModels_reflect h _ _ _
        (sfbProEtale_fixedModels_of_iso _ e _ hH)

end AlgebraicGeometry.Scheme
