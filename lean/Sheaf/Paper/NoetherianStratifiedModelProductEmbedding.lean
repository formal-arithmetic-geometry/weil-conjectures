/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Paper.IntegralModelSurjectiveClosedReflection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.CategoryTheory.JointAdjunctionModelEmbedding
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Stratified products and the unit-component embedding

Source: blueprint main-20261015, `sk-lem-int-integral-heart-triangulated.proof.md`,
paragraph (2), final sentence, and the extracted product-bound argument, steps 4–7.
(blueprint: lem-sfb-noetherian-stratified-model-product-embedding).

The index consists of actual bounded stratification codes and labels, rather than
isomorphism classes. The category and section functor below are specializations of the
recorded coefficient construction and internal-to-sectionwise equivalence.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The integral coefficient module category for a bounded scheme.
Source: blueprint integral-heart proof (2), product-bound construction
(blueprint: lem-sfb-noetherian-stratified-model-product-embedding). -/
noncomputable abbrev integralStratifiedModelModules (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (integralModelCondensedCoefficients l E).X T)

/-- The bounded schemes on which the supplied families are required.
Source: blueprint integral-heart proof (2), bounded stratification codes
(blueprint: lem-sfb-noetherian-stratified-model-product-embedding). -/
abbrev LocallyClosedModelDomain (X : Scheme.{u}) : Type (u + 1) :=
  {T : Scheme.{u} // ∃ a : T ⟶ X, IsImmersion a}

/-- A stratum, regarded as a bounded domain; its immersion is not extra family data.
Source: blueprint integral-heart proof (2), bounded stratification codes
(blueprint: lem-sfb-noetherian-stratified-model-product-embedding). -/
def stratificationModelDomain {X : Scheme.{u}}
    (h : Scheme.FiniteLocallyClosedStratification X) (s : Fin h.n) :
    LocallyClosedModelDomain X :=
  ⟨h.domain s, h.immersion s, h.isImmersion s⟩

/-- The small dependent sum of labelled finite stratifications.
Source: blueprint integral-heart proof (2), bounded stratification codes
(blueprint: lem-sfb-noetherian-stratified-model-product-embedding). -/
abbrev StratifiedModelIndex (X : Scheme.{u})
    (I : LocallyClosedModelDomain X → Type (u + 1)) : Type (u + 1) :=
  Σ h : Scheme.FiniteLocallyClosedStratification X,
    ∀ s : Fin h.n, I (stratificationModelDomain h s)

/-- The finite family of direct images attached to a labelled stratification.
Source: blueprint integral-heart proof (2), sectionwise product construction
(blueprint: lem-sfb-noetherian-stratified-model-product-embedding). -/
noncomputable def stratifiedModelFactors (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (I : LocallyClosedModelDomain X → Type (u + 1))
    (F : ∀ T : LocallyClosedModelDomain X, I T → integralStratifiedModelModules l E T.val)
    (j : StratifiedModelIndex X I) (s : Fin j.1.n) :
    integralStratifiedModelModules l E X :=
  (CondensedRing.lowerStar (integralModelCondensedCoefficients l E).X
    (j.1.immersion s)).obj (F (stratificationModelDomain j.1 s) (j.2 s))

/-- Sections through the recorded internal-to-sectionwise module equivalence.
Source: blueprint integral-heart proof (2), sectionwise product construction;
Stacks Tag 03DB
(blueprint: lem-sfb-noetherian-stratified-model-product-embedding). -/
noncomputable def integralStratifiedModelSections (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (V : X.ProEt) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X)
    (condensedRingObj (integralModelCondensedCoefficients l E).X X)).functor ⋙
      SheafOfModules.evaluation _ (Opposite.op V)

set_option backward.isDefEq.respectTransparency false in
/-- Small labelled stratifications have sectionwise products, with zero empty product,
and the specified adjunction-unit map from any matching module is monic.

Source: blueprint main-20261015, integral-heart triangulated proof (2), final sentence;
Stacks Tags 03DB and 03CO; the proved source-library finite quasi-compact
abelian-sheaf detection theorem, as expanded in the node's six proof steps.
(blueprint: lem-sfb-noetherian-stratified-model-product-embedding).

Proof:
1. Bounded schemes and morphisms are in universe `u + 1`. Finite tuples satisfying
   the stratification conditions form `H` in that universe; the displayed dependent
   sum `StratifiedModelIndex X I` is `J` in the same universe. No quotient is taken.
2. Take the categorical finite product of the direct-image factors. The recorded
   internal-to-sectionwise equivalence and section evaluation preserve this limit,
   as does forgetting module sections to types. Uniqueness of limits identifies
   its section comparison with the isomorphism to the ordinary dependent product.
   All section modules have carrier universe `u + 1`.
3. The module categories are abelian; the existing module pullback instances
   give additivity and preservation of kernels. Since X is Noetherian, the stratum
   domains have Noetherian underlying spaces and their immersions are quasi-compact.
   Their images cover X. Apply the proved finite quasi-compact abelian-sheaf detection
   theorem to the identity of the underlying sheaf. The comparison upperStarObjXIso
   turns vanishing of the module pullbacks into vanishing of the abelian pullbacks.
   Faithfulness of the module forgetful functor then gives joint zero detection.
4. Apply `lem-sfb-joint-adjunction-model-embedding` with these pullbacks, direct
   images, the specified `upperStarLowerStarAdjunction`, and the given isomorphisms.
   Use the chosen categorical product cone; its projection equations are
   exactly the unit followed by the direct image of each supplied isomorphism.
5. Choosing labels and restriction isomorphisms on any stratification gives `j`
   and this monomorphism. Conversely, the same isomorphisms witness representation
   by the supplied families. An empty label set need not yield any such `j`.
6. If there are no strata, product extensionality identifies the identity and zero
   on the cone point. The same finite-family detection argument includes an empty
   family over an empty scheme, so the monicity argument needs no exception. -/
theorem noetherian_stratified_model_product_embedding
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X]
    (I : LocallyClosedModelDomain X → Type (u + 1))
    (F : ∀ T : LocallyClosedModelDomain X, I T → integralStratifiedModelModules l E T.val) :
    ∀ j : StratifiedModelIndex X I,
      ∃ c : Fan (stratifiedModelFactors l E X I F j),
        Nonempty (IsLimit c) ∧
        (∀ V : X.ProEt, Function.Bijective
          (fun x : (integralStratifiedModelSections l E X V).obj c.pt ↦
            fun s : Fin j.1.n ↦
              (integralStratifiedModelSections l E X V).map (c.π.app ⟨s⟩) x)) ∧
        (j.1.n = 0 → IsZero c.pt) ∧
        (∀ (M : integralStratifiedModelModules l E X)
          (φ : ∀ s : Fin j.1.n,
            (CondensedRing.upperStar (integralModelCondensedCoefficients l E).X
              (j.1.immersion s)).obj M ≅
                F (stratificationModelDomain j.1 s) (j.2 s)),
          ∃ f : M ⟶ c.pt, Mono f ∧
            ∀ s : Fin j.1.n, f ≫ c.π.app ⟨s⟩ =
              (CondensedRing.upperStarLowerStarAdjunction
                (integralModelCondensedCoefficients l E).X (j.1.immersion s)).unit.app M ≫
                  (CondensedRing.lowerStar (integralModelCondensedCoefficients l E).X
                    (j.1.immersion s)).map (φ s).hom) := by
  classical
  intro j
  let factors := stratifiedModelFactors l E X I F j
  have : IsNoetherian X := {}
  have : ∀ s : Fin j.1.n, IsImmersion (j.1.immersion s) := j.1.isImmersion
  have : ∀ s : Fin j.1.n, TopologicalSpace.NoetherianSpace (j.1.domain s) :=
    fun s ↦ (j.1.immersion s).isEmbedding.noetherianSpace
  have : ∀ s : Fin j.1.n, QuasiCompact (j.1.immersion s) := fun s ↦ inferInstance
  have hcover : ∀ x : X, ∃ s, x ∈ Set.range (j.1.immersion s) := by
    intro x
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp
      (j.1.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    exact ⟨s, (j.1.range_immersion s).symm ▸ hs⟩
  have hzero (N : integralStratifiedModelModules l E X)
      (hN : ∀ s : Fin j.1.n, IsZero ((CondensedRing.upperStar
        (integralModelCondensedCoefficients l E).X (j.1.immersion s)).obj N)) :
      IsZero N := by
    apply CondensedRing.isZero_of_isZero_X (integralModelCondensedCoefficients l E).X
    rw [IsZero.iff_id_eq_zero]
    apply eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp j.1.immersion hcover
    intro s
    exact (((Mod.forget _).map_isZero (hN s)).of_iso
      (CondensedRing.upperStarObjXIso
        (integralModelCondensedCoefficients l E).X (j.1.immersion s) N).symm).eq_of_src _ _
  refine ⟨Fan.mk (∏ᶜ factors) (Pi.π factors), ⟨productIsProduct factors⟩, ?_, ?_, ?_⟩
  · intro V
    let S := integralStratifiedModelSections l E X V
    let T := S ⋙ CategoryTheory.forget _
    have : PreservesFiniteLimits S := by
      dsimp only [S, integralStratifiedModelSections]
      infer_instance
    have : PreservesFiniteLimits T := by
      dsimp only [T]
      infer_instance
    have ht := isLimitOfHasProductOfPreservesLimit T factors
    let e := ht.conePointUniqueUpToIso
      (Types.productLimitCone (fun s ↦ T.obj (factors s))).isLimit
    have he : (fun x s ↦ e.hom x s) = (fun x s ↦ T.map (Pi.π factors s) x) := by
      funext x s
      exact ConcreteCategory.congr_hom
        (ht.conePointUniqueUpToIso_hom_comp
          (Types.productLimitCone (fun s ↦ T.obj (factors s))).isLimit ⟨s⟩) x
    change Function.Bijective (fun x s ↦ T.map (Pi.π factors s) x)
    rw [← he]
    exact ConcreteCategory.bijective_of_isIso e.hom
  · intro hn
    have : IsEmpty (Fin j.1.n) := ⟨fun s ↦ Fin.elim0 (hn ▸ s)⟩
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro s
    exact isEmptyElim s
  · intro M φ
    let components : ∀ s : Fin j.1.n, M ⟶ factors s := fun s ↦
      (CondensedRing.upperStarLowerStarAdjunction
        (integralModelCondensedCoefficients l E).X (j.1.immersion s)).unit.app M ≫
          (CondensedRing.lowerStar (integralModelCondensedCoefficients l E).X
            (j.1.immersion s)).map (φ s).hom
    refine ⟨Pi.lift components, ?_, fun s ↦ Pi.lift_π components s⟩
    exact mono_pi_lift_adjunction_models
      (fun s ↦ CondensedRing.upperStar (integralModelCondensedCoefficients l E).X (j.1.immersion s))
      (fun s ↦ CondensedRing.lowerStar (integralModelCondensedCoefficients l E).X (j.1.immersion s))
      (fun s ↦ CondensedRing.upperStarLowerStarAdjunction
        (integralModelCondensedCoefficients l E).X (j.1.immersion s))
      hzero M (fun s ↦ F (stratificationModelDomain j.1 s) (j.2 s)) φ

end AlgebraicGeometry.ProEtale
