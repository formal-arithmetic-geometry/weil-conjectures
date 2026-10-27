/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.IntegralModelSurjectiveClosedReflection
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.ProEtaleScalarLocalModelRepresentatives
import Sheaf.CategoryTheory.JointAdjunctionModelEmbedding
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Small stratum-product and image-subsheaf models

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-int-integral-heart/sk-lem-int-integral-heart-triangulated.proof.md, paragraph (2),
final sentence (blueprint: lem-sfb-stratified-constant-model-product-bound).

The index types below lie in `u + 1`, the universe of the bounded sites and sections.
The coefficient rings and schemes lie in `u`. Image indices are actual families of
submodules whose underlying presheaf is a sheaf, rather than arbitrary chosen objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
  AlgebraicGeometry.ProEtale.integralModelCondensedCoefficients
  CategoryTheory.Sheaf.monoidalCategory

namespace AlgebraicGeometry.ProEtale.StratifiedConstantModels

/-- Schemes occurring as strata of finite locally closed stratifications of X.
Source: paragraph (2), finite stratifications
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
abbrev Stratum (X : Scheme.{u}) : Type (u + 1) :=
  {T : Scheme.{u} // ∃ (S : Scheme.FiniteLocallyClosedStratification X)
    (s : Fin S.n), S.domain s = T}

/-- The stratum scheme at one position, with its occurrence witness.
Source: paragraph (2), finite stratifications
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
abbrev stratumAt {X : Scheme.{u}} (S : Scheme.FiniteLocallyClosedStratification X)
    (s : Fin S.n) : Stratum X :=
  ⟨S.domain s, S, s, rfl⟩

/-- All pairs of a bounded finite stratification and a tuple of local-model labels.
This is a type in `u + 1`, including the unique empty tuple when `S.n = 0`.
Source: paragraph (2), the small set of gluing data
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
abbrev Index (X : Scheme.{u}) (I : Stratum X → Type (u + 1)) : Type (u + 1) :=
  Σ S : Scheme.FiniteLocallyClosedStratification X, ∀ s : Fin S.n, I (stratumAt S s)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Internal coefficient modules, using the existing pulled-back ring object.
Source: paragraph (2), modules on the small pro-etale site
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
abbrev Modules (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)

/-- The product of the direct images of the chosen stratum models.
Source: paragraph (2), gluing data, and Stacks Tag 03DB for products
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
abbrev product {X : Scheme.{u}} (I : Stratum X → Type (u + 1))
    (F : ∀ T : Stratum X, I T → Modules Λ T.val) (j : Index X I) : Modules Λ X :=
  ∏ᶜ fun s : Fin j.1.n ↦
    (CondensedRing.lowerStar Λ (j.1.immersion s)).obj (F (stratumAt j.1 s) (j.2 s))

/-- The existing internal-to-sectionwise equivalence, preserving underlying sections.
Source: Stacks Tag 00YV, as used in paragraph (2)
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
abbrev sectionModule {X : Scheme.{u}} (P : Modules Λ X) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)).functor.obj P

/-- Actual families of submodules of the sections of P, stable under restriction,
whose associated presheaf satisfies the sheaf condition. This index is in `u + 1`.
Source: paragraph (2), small-site gluing data; Stacks Tag 03DA
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
abbrev ImageIndex {X : Scheme.{u}} (P : Modules Λ X) : Type (u + 1) :=
  {N : (sectionModule Λ P).val.Submodule //
    Presheaf.IsSheaf (Scheme.ProEt.topology X) N.toPresheafOfModules.presheaf}

/-- All image-subsheaf labels for all stratum products, in the same small universe.
Source: paragraph (2), the set of all gluing data
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
abbrev TotalImageIndex {X : Scheme.{u}} (I : Stratum X → Type (u + 1))
    (F : ∀ T : Stratum X, I T → Modules Λ T.val) : Type (u + 1) :=
  Σ j : Index X I, ImageIndex Λ (product Λ I F j)

/-- The image subsheaf specified by its family of subsets, with inherited operations.
Source: paragraph (2), small-site gluing data; Stacks Tag 03DA
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
def imageSheaf {X : Scheme.{u}} (P : Modules Λ X) (N : ImageIndex Λ P) :
    SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) (condensedRingObj Λ X))) :=
  ⟨N.val.toPresheafOfModules, N.property⟩

/-- Inclusion of the actual image subsheaf into P, on every section.
Source: paragraph (2), small-site gluing data; Stacks Tag 03DA
(blueprint: lem-sfb-stratified-constant-model-product-bound). -/
def imageInclusion {X : Scheme.{u}} (P : Modules Λ X) (N : ImageIndex Λ P) :
    imageSheaf Λ P N ⟶ sectionModule Λ P :=
  ⟨N.val.ι⟩

/-- The stratum unit maps are jointly monic, with the canonical product as target. -/
private theorem mono_stratum_product {X : Scheme.{u}} [CompactSpace X]
    [IsLocallyNoetherian X] (S : Scheme.FiniteLocallyClosedStratification X)
    (M : Modules Λ X) (F : ∀ s : Fin S.n, Modules Λ (S.domain s))
    (φ : ∀ s : Fin S.n, (CondensedRing.upperStar Λ (S.immersion s)).obj M ≅ F s) :
    Mono (Pi.lift (fun s : Fin S.n ↦
      (CondensedRing.upperStarLowerStarAdjunction Λ (S.immersion s)).unit.app M ≫
        (CondensedRing.lowerStar Λ (S.immersion s)).map (φ s).hom)) := by
  have : IsNoetherian X := {}
  have : ∀ s : Fin S.n, IsImmersion (S.immersion s) := S.isImmersion
  have : ∀ s : Fin S.n, TopologicalSpace.NoetherianSpace (S.domain s) :=
    fun s ↦ (S.immersion s).isEmbedding.noetherianSpace
  have : ∀ s : Fin S.n, QuasiCompact (S.immersion s) := fun s ↦ inferInstance
  have hcover : ∀ x : X, ∃ s, x ∈ Set.range (S.immersion s) := by
    intro x
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    exact ⟨s, (S.range_immersion s).symm ▸ hs⟩
  have hzero (N : Modules Λ X)
      (hN : ∀ s : Fin S.n, IsZero ((CondensedRing.upperStar Λ (S.immersion s)).obj N)) :
      IsZero N := by
    apply CondensedRing.isZero_of_isZero_X Λ
    rw [IsZero.iff_id_eq_zero]
    apply eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp S.immersion hcover
    intro s
    exact (((Mod.forget _).map_isZero (hN s)).of_iso
      (CondensedRing.upperStarObjXIso Λ (S.immersion s) N).symm).eq_of_src _ _
  exact mono_pi_lift_adjunction_models
    (fun s ↦ CondensedRing.upperStar Λ (S.immersion s))
    (fun s ↦ CondensedRing.lowerStar Λ (S.immersion s))
    (fun s ↦ CondensedRing.upperStarLowerStarAdjunction Λ (S.immersion s)) hzero M F φ

omit [IsCommMonObj Λ] in
/-- A labelled product with no strata is zero, for every coefficient ring. -/
private theorem product_isZero_of_empty {X : Scheme.{u}}
    (I : Stratum X → Type (u + 1)) (F : ∀ T : Stratum X, I T → Modules Λ T.val)
    (j : Index X I) (hj : j.1.n = 0) : IsZero (product Λ I F j) := by
  have : IsEmpty (Fin j.1.n) := ⟨fun s ↦ Fin.elim0 (hj ▸ s)⟩
  dsimp only [product]
  apply (IsZero.iff_id_eq_zero _).2
  apply Pi.hom_ext
  intro s
  exact isEmptyElim s

/-- A monomorphism of module sheaves is isomorphic over its target to its range. -/
private theorem range_factor {A : Type*} [Category A] {J : GrothendieckTopology A}
    {R : Sheaf J RingCat.{u + 1}} {M P : SheafOfModules.{u + 1} R}
    (m : M ⟶ P) [Mono m] :
    ∃ (N : P.val.Submodule)
      (hN : Presheaf.IsSheaf J N.toPresheafOfModules.presheaf)
      (e : M ≅ (⟨N.toPresheafOfModules, hN⟩ : SheafOfModules R)),
      e.hom ≫ (⟨N.ι⟩ : (⟨N.toPresheafOfModules, hN⟩ : SheafOfModules R) ⟶ P) = m := by
  classical
  have hinj (V : Aᵒᵖ) : Function.Injective (m.val.app V) := by
    have : Mono m.val := (SheafOfModules.forget _).map_mono m
    exact PresheafOfModules.injective_of_mono m.val V
  let N : P.val.Submodule :=
    { obj V := LinearMap.range (m.val.app V).hom
      map := by
        intro V W g y hy
        rcases hy with ⟨x, rfl⟩
        exact ⟨M.val.map g x, PresheafOfModules.naturality_apply m.val g x⟩ }
  let e : M.val ≅ N.toPresheafOfModules :=
    PresheafOfModules.isoMk (fun V ↦
      (LinearEquiv.ofInjective (m.val.app V).hom (hinj V)).toModuleIso) (by
        intro V W g
        ext x
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply m.val g x)
  have hN : Presheaf.IsSheaf J N.toPresheafOfModules.presheaf :=
    (Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf _).mapIso e)).1 M.isSheaf
  refine ⟨N, hN, (SheafOfModules.fullyFaithfulForget _).preimageIso e, ?_⟩
  apply SheafOfModules.hom_ext
  ext V x
  rfl

/-- Forget constructibility of the strata while retaining any predicate on their maps. -/
private theorem finite_stratification_of_stratification {X : Scheme.{u}}
    (P : ∀ T : Scheme.{u}, (T ⟶ X) → Prop)
    (h : ∃ S : Scheme.Stratification X, ∀ s : Fin S.n, P (S.domain s) (S.immersion s)) :
    ∃ S : Scheme.FiniteLocallyClosedStratification X,
      ∀ s : Fin S.n, P (S.domain s) (S.immersion s) := by
  obtain ⟨S, hS⟩ := h
  exact ⟨{ n := S.n
           stratum := S.stratum
           isLocallyClosed_stratum := S.isLocallyClosed_stratum
           iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
           pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
           domain := S.domain
           immersion := S.immersion
           isImmersion := S.isImmersion
           range_immersion := S.range_immersion }, hS⟩

private theorem choose_index {X : Scheme.{u}}
    (I : Scheme.{u} → Type (u + 1))
    (P : ∀ T : Scheme.{u}, (T ⟶ X) → I T → Prop)
    (S : Scheme.FiniteLocallyClosedStratification X)
    (h : ∀ s : Fin S.n, ∃ t, P (S.domain s) (S.immersion s) t) :
    ∃ j : Index X (fun T ↦ I T.val),
      ∀ s : Fin j.1.n, P (j.1.domain s) (j.1.immersion s) (j.2 s) := by
  choose t ht using h
  exact ⟨⟨S, t⟩, ht⟩

/-- Assemble representatives, unit-component embeddings, and actual range subsheaves. -/
private theorem assemble_bound
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (I : Scheme.{u} → Type (u + 1)) (F : ∀ T, I T → Modules Λ T)
    (hlocal : ∀ T t, HasFiniteConstantLocalModel Λ T (F T t))
    (hrep : ∀ T (M : Modules Λ T), HasFiniteConstantLocalModel Λ T M →
      ∃ t : I T, Nonempty (M ≅ F T t)) :
    ∃ (I : Stratum X → Type (u + 1))
      (F : ∀ T : Stratum X, I T →
        Modules Λ T.val),
      (∀ (T : Stratum X) (t : I T),
        HasFiniteConstantLocalModel Λ T.val (F T t)) ∧
      (∀ (T : Stratum X) (M : Modules Λ T.val),
        HasFiniteConstantLocalModel Λ T.val M →
          ∃ t : I T, Nonempty (M ≅ F T t)) ∧
      (∀ (C : Modules Λ X),
        IsConstantModelConstructible Λ X C →
          ∃ (j : Index X I)
            (φ : ∀ s : Fin j.1.n,
              (CondensedRing.upperStar Λ
                (j.1.immersion s)).obj C ≅ F (stratumAt j.1 s) (j.2 s))
            (v : C ⟶ product Λ I F j),
            Mono v ∧ ∀ s : Fin j.1.n,
              v ≫ Pi.π (fun s : Fin j.1.n ↦
                (CondensedRing.lowerStar Λ
                  (j.1.immersion s)).obj (F (stratumAt j.1 s) (j.2 s))) s =
                (CondensedRing.upperStarLowerStarAdjunction
                  Λ (j.1.immersion s)).unit.app C ≫
                  (CondensedRing.lowerStar Λ
                    (j.1.immersion s)).map (φ s).hom) ∧
      (∀ (j : Index X I),
        (∀ N : ImageIndex Λ
          (product Λ I F j),
          Mono (imageInclusion Λ _ N)) ∧
        (∀ (M : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
                (Scheme.ProEt.topology X)
                (condensedRingObj Λ X))))
          (m : M ⟶ sectionModule Λ
            (product Λ I F j)),
          Mono m → ∃ (N : ImageIndex Λ
              (product Λ I F j))
            (e : M ≅ imageSheaf Λ _ N),
            e.hom ≫ imageInclusion Λ _ N = m)) ∧
      (IsEmpty X → ∃ j : Index X I, j.1.n = 0) ∧
      (∀ j : Index X I, j.1.n = 0 →
        IsZero (product Λ I F j)) := by
  classical
  refine ⟨(fun T ↦ I T.val), (fun T ↦ F T.val),
    (fun T ↦ hlocal T.val), (fun T ↦ hrep T.val), ?_, ?_, ?_, ?_⟩
  · intro C hC
    have hqcqs : CompactSpace X ∧ QuasiSeparatedSpace X :=
      ⟨inferInstance, inferInstance⟩
    unfold IsConstantModelConstructible at hC
    rw [if_pos hqcqs] at hC
    obtain ⟨S', hS'⟩ := finite_stratification_of_stratification
      (fun T f ↦ HasFiniteConstantLocalModel Λ T ((CondensedRing.upperStar Λ f).obj C)) hC
    obtain ⟨j, ht⟩ := choose_index I
      (fun T f t ↦ Nonempty ((CondensedRing.upperStar Λ f).obj C ≅ F T t)) S'
      (fun s ↦ hrep (S'.domain s) _ (hS' s))
    let φ : ∀ s : Fin j.1.n,
        (CondensedRing.upperStar Λ
          (j.1.immersion s)).obj C ≅ F (j.1.domain s) (j.2 s) :=
      fun s ↦ (ht s).some
    let v : C ⟶ product Λ
        (fun T ↦ I T.val) (fun T ↦ F T.val) j := Pi.lift (fun s : Fin j.1.n ↦
      (CondensedRing.upperStarLowerStarAdjunction
        Λ (j.1.immersion s)).unit.app C ≫
      (CondensedRing.lowerStar Λ
        (j.1.immersion s)).map (φ s).hom)
    refine ⟨j, φ, v, ?_, ?_⟩
    · exact mono_stratum_product Λ
        j.1 C (fun s ↦ F (j.1.domain s) (j.2 s)) φ
    · intro s
      exact Pi.lift_π _ s
  · intro j
    constructor
    · intro N
      exact (SheafOfModules.forget _).mono_of_mono_map (by
        change Mono N.val.ι
        infer_instance)
    · intro M m hm
      have : Mono m := hm
      obtain ⟨N, hN, e, he⟩ := range_factor m
      exact ⟨⟨N, hN⟩, e, he⟩
  · intro hX
    have : IsEmpty X := hX
    let S : Scheme.FiniteLocallyClosedStratification X :=
      { n := 0
        stratum := Fin.elim0
        isLocallyClosed_stratum := fun s ↦ Fin.elim0 s
        iUnion_stratum_eq_univ := by ext x; exact isEmptyElim x
        pairwise_disjoint_stratum := fun s ↦ Fin.elim0 s
        domain := Fin.elim0
        immersion := fun s ↦ Fin.elim0 s
        isImmersion := fun s ↦ Fin.elim0 s
        range_immersion := fun s ↦ Fin.elim0 s }
    exact ⟨⟨S, fun s ↦ Fin.elim0 s⟩, rfl⟩
  · intro j hj
    exact product_isZero_of_empty Λ
      (fun T ↦ I T.val) (fun T ↦ F T.val) j hj

/-- The small family of products and their actual image subsheaves bounds all
constructible integral coefficient modules. Labels are supplied for each stratum
scheme, and all choices of stratification and labels occur in `Index`.

Source: blueprint main-20261015, sk-lem-int-integral-heart-triangulated.proof.md,
paragraph (2), final sentence
(blueprint: lem-sfb-stratified-constant-model-product-bound).

Proof:
1. Each bounded pro-etale site has terminal object and finite limits, using weakly
   etale stability and scheme fibre products; pass to its small skeleton.
2. Finite matrices over O_E form a small set; their actual cokernels represent every
   finitely presented scalar module (def-sc-finitely-presented-module).
3. Pro-etale localization and proEtaleObjectInverseImageRestriction identify these
   scalar models with slice-local models, using cartesian coefficients. Apply
   essentiallySmall_locally_prescribed and choose representatives simultaneously
   over the set of stratum schemes.
4. Finite stratifications form a set in `u + 1`. Dependent sums of their finite
   tuples of representative labels give exactly `Index X I` in `u + 1`.
5. Form the products using the module adjunctions and sectionwise limits. The
   internal-to-sectionwise equivalence preserves the sections of these products.
6. A constructible module has a finite constant-model stratification: quasi-compact
   locally Noetherian X is qcqs. Choose representative labels and isomorphisms.
7. Cartesian pullback is exact. Noetherian stratum detection says these pullbacks
   jointly detect zero objects. Apply mono_pi_lift_adjunction_models to obtain
   the monomorphism with the specified adjunction-unit components.
8. For a mono m, the ranges of its injective section maps form a submodule family.
   The sectionwise bijections from its source to these ranges transport the
   sheaf axiom and give an isomorphism over the product. Equal families identify the
   subobjects over that product; general non-monic images are not used.
9. Such families belong to the product of the powersets of the section sets, in
   `u + 1`. `ImageIndex` takes precisely the sheaf subfamilies, so the dependent
   sum over `Index X I` is still a type in `u + 1`.
10. Zero models are allowed. For empty X the empty stratification is allowed;
    its product is the zero module, and all module sheaves on the empty site are
    zero by the empty covering sheaf axiom. Empty strata cause no exception. -/
theorem exists_stratified_constant_model_product_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X] :
    ∃ (I : Stratum X → Type (u + 1))
      (F : ∀ T : Stratum X, I T →
        Modules (integralModelCondensedCoefficients l E).X T.val),
      (∀ (T : Stratum X) (t : I T),
        HasFiniteConstantLocalModel (integralModelCondensedCoefficients l E).X T.val (F T t)) ∧
      (∀ (T : Stratum X) (M : Modules (integralModelCondensedCoefficients l E).X T.val),
        HasFiniteConstantLocalModel (integralModelCondensedCoefficients l E).X T.val M →
          ∃ t : I T, Nonempty (M ≅ F T t)) ∧
      (∀ (C : Modules (integralModelCondensedCoefficients l E).X X),
        IsConstantModelConstructible (integralModelCondensedCoefficients l E).X X C →
          ∃ (j : Index X I)
            (φ : ∀ s : Fin j.1.n,
              (CondensedRing.upperStar (integralModelCondensedCoefficients l E).X
                (j.1.immersion s)).obj C ≅ F (stratumAt j.1 s) (j.2 s))
            (v : C ⟶ product (integralModelCondensedCoefficients l E).X I F j),
            Mono v ∧ ∀ s : Fin j.1.n,
              v ≫ Pi.π (fun s : Fin j.1.n ↦
                (CondensedRing.lowerStar (integralModelCondensedCoefficients l E).X
                  (j.1.immersion s)).obj (F (stratumAt j.1 s) (j.2 s))) s =
                (CondensedRing.upperStarLowerStarAdjunction
                  (integralModelCondensedCoefficients l E).X (j.1.immersion s)).unit.app C ≫
                  (CondensedRing.lowerStar (integralModelCondensedCoefficients l E).X
                    (j.1.immersion s)).map (φ s).hom) ∧
      (∀ (j : Index X I),
        (∀ N : ImageIndex (integralModelCondensedCoefficients l E).X
          (product (integralModelCondensedCoefficients l E).X I F j),
          Mono (imageInclusion (integralModelCondensedCoefficients l E).X _ N)) ∧
        (∀ (M : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
                (Scheme.ProEt.topology X)
                (condensedRingObj (integralModelCondensedCoefficients l E).X X))))
          (m : M ⟶ sectionModule (integralModelCondensedCoefficients l E).X
            (product (integralModelCondensedCoefficients l E).X I F j)),
          Mono m → ∃ (N : ImageIndex (integralModelCondensedCoefficients l E).X
              (product (integralModelCondensedCoefficients l E).X I F j))
            (e : M ≅ imageSheaf (integralModelCondensedCoefficients l E).X _ N),
            e.hom ≫ imageInclusion (integralModelCondensedCoefficients l E).X _ N = m)) ∧
      (IsEmpty X → ∃ j : Index X I, j.1.n = 0) ∧
      (∀ j : Index X I, j.1.n = 0 →
        IsZero (product (integralModelCondensedCoefficients l E).X I F j)) := by
  classical
  choose I F hlocal hrep using fun T : Scheme.{u} ↦
    (proetale_scalar_local_model_representatives l E T).1
  exact assemble_bound (integralModelCondensedCoefficients l E).X X I F hlocal hrep


end AlgebraicGeometry.ProEtale.StratifiedConstantModels
