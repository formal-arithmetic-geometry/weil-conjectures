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
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

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
  sorry

end AlgebraicGeometry.Scheme
