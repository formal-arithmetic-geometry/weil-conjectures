/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
import Sheaf.NumberTheory.Padics.IntegersCosetBasis
import all Sheaf.Paper.FiniteCoefficientModelComparison
import all Sheaf.SixFunctors.ProEtale.IntegralCompletionPresentation
import Sheaf.SixFunctors.ProEtale.IntegralNormalizedSectionSquares
import Sheaf.SixFunctors.ProEtale.InternalRoosCompleteness
import Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import all Sheaf.Algebra.Homology.SuccessiveQuotientFlatTensorSequence
import all Sheaf.Paper.StrictDvrFlatTensorSequence
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Paper.CompletedCoefficientRegularQuotients
import Sheaf.Paper.ProEtaleFiniteScalarRestrictionConstructible
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Constructibility of all integral reductions from the first

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-integral-criterion/sk-prop-integral-criterion-reductions.md
(blueprint: det-prop-integral-criterion-reductions).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

/-- Derived completeness, constructibility of every positive reduction and a common
finite cohomological interval. The reduction index n denotes the exponent n+1.
There is no Tor-amplitude condition and no boundedness requirement on K itself.
The predicate is intrinsic to X and E; the global convention l != p has no role in it.
Source: Weil blueprint, order 1459, and the final paragraph of
sk-prop-integral-criterion-reductions
(blueprint: det-prop-integral-criterion-reductions). -/
def continuousIntegralConstructible (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) : ObjectProperty (DerivedCategory (AdicCompletion.Modules l E X)) :=
  fun K ↦ IsDerivedComplete l E X K ∧
    (∀ n : ℕ, constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1))
      X ((AdicCompletion.derivedReduction l E X n).obj K)) ∧
    ∃ r s : ℤ, r ≤ s ∧ ∀ (n : ℕ) (q : ℤ), q < r ∨ s < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((AdicCompletion.derivedReduction l E X n).obj K))

/-- The full subcategory with the inherited ambient derived morphisms.
Source: Weil blueprint, order 1459
(blueprint: det-prop-integral-criterion-reductions). -/
abbrev ContinuousIntegralConstructible (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) := (continuousIntegralConstructible l E X).FullSubcategory

private theorem finiteConstantEndomorphism (X : Scheme.{u})
    (h : sfbFiniteConstantSets X ⟶ sfbFiniteConstantSets X) : h = 𝟙 _ := by
  let J := Scheme.ProEt.topology X
  let O := FintypeCat.of (ULift.{u} Unit)
  let F := sfbFiniteConstantSets X
  have ht : IsTerminal (ULift.{u + 1, u} (ULift.{u} Unit)) :=
    (Types.isTerminalEquivUnique _).symm inferInstance
  have ht' : IsTerminal (F.obj O) :=
    (ht.isTerminalObj (constantSheaf J (Type (u + 1))) _).isTerminalObj
      (sheafToPresheaf J (Type (u + 1))) _
  have hO : h.app O = 𝟙 _ := ht'.hom_ext _ _
  apply NatTrans.ext
  funext T
  apply sheafify_hom_ext J _ _
    (((constantSheaf J (Type (u + 1))).obj (ULift.{u + 1, u} T)).property)
  ext V x
  let k : O ⟶ T := FintypeCat.homMk fun _ ↦ x.down
  let z := (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
    (ULift.{u + 1, u} (ULift.{u} Unit)))).app V (ULift.up (ULift.up ()))
  have hn := congrArg (fun t ↦ t.app V) (h.naturality k)
  rw [hO, Category.id_comp] at hn
  have hc : (F.map k).app V z =
      (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1, u} T))).app V x := by
    exact (congrArg (fun t ↦ t.app V
      (ULift.up (ULift.up () : ULift.{u} Unit))) (toSheafify_naturality J
      ((Functor.const X.ProEtᵒᵖ).map
        (uliftFunctor.{u + 1, u}.map ((forget FintypeCat).map k))))).symm
  change (h.app T).app V
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1, u} T))).app V x) =
    (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1, u} T))).app V x
  rw [← hc]
  exact congrArg (fun t ↦ t z) hn

private theorem finiteRepresentation_unique (X : Scheme.{u})
    (a b : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X) : a = b := by
  apply Iso.ext
  have h := finiteConstantEndomorphism X (a.hom ≫ b.inv)
  have h' := congrArg (fun f ↦ f ≫ b.hom) h
  simpa using h'

/-- The projection-normalized comparison is independent of all auxiliary finite-set
representations and limit-cone witnesses. SfbIntegralComparison retains the unit
and all reduction equations, not just existence of an isomorphism.
Source: blueprint integral-limit clause 3; integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions).
Proof: existence is sfb_integral_coefficient_limit. For uniqueness, the finite-label
representation is unique: on a singleton both sheaves are terminal, and naturality
with every singleton-to-finite-set inclusion fixes each constant label; sheafification
then fixes the whole natural transformation. For each cone witness the composite
j followed by its nth projection is the specified quotient on every integer, so
changing the cone changes none of these maps. The adjunction-mate normalization
therefore gives the same nth projection for both comparisons on every profinite
test object and continuous integer-valued function. The adjunction and Yoneda
identify the maps; finally the limit projections jointly distinguish them. -/
theorem integralLimitAbComparison_existsUnique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ∃! e : (coefficientRing X (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E X,
      SfbIntegralComparison l E X e := by
  obtain ⟨a, c, j, hq, hc, _, _, _, e, he, hu⟩ :=
    sfb_integral_coefficient_limit l E X
  refine ⟨e, ⟨he.1, he.2.1, a, c, j, hq, hc, he.2.2⟩, ?_⟩
  intro e' he'
  obtain ⟨hm, hi, b, d, k, hq', hd, hn⟩ := he'
  have hab : b = a := finiteRepresentation_unique X b a
  subst b
  apply hu e'
  refine ⟨hm, hi, ?_⟩
  intro S f n
  rw [hn]
  congr 2
  apply ConcreteCategory.hom_ext
  intro x
  exact (hq' n (f x)).trans (hq n (f x)).symm

/-- The unique integral-limit comparison with the published adjunction-mate and
finite-projection normalization. No finite representation or equivalence is selected
from a bare existence statement.
Source: blueprint integral-limit clause 3; integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions). -/
def integralLimitAbComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :=
  (integralLimitAbComparison_existsUnique l E X).exists.choose

private theorem continuousRingSheaf_topology_eq (T : Type u) [Ring T]
    (t₁ t₂ : TopologicalSpace T) (h : t₁ = t₂)
    (h₁ : @IsTopologicalRing T t₁ _) (h₂ : @IsTopologicalRing T t₂ _) :
    @Profinite.continuousMapRingSheafOfUniverse.{u, u} T t₁ _ h₁ =
      @Profinite.continuousMapRingSheafOfUniverse.{u, u} T t₂ _ h₂ := by
  subst t₂
  rfl

private theorem integralPointMon_eq (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon.mk (DerivedNakayama.integerRing l E) = sfbCondensedIntegers l E := by
  have hm : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  have ht := congrArg (fun m : PseudoMetricSpace E ↦
    m.toUniformSpace.toTopologicalSpace) hm.symm
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  have hs := continuousRingSheaf_topology_eq
    (Padic.coefficientExtensionIntegers l E) _ _ hti
    (by let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField; infer_instance)
    (by let := spectralNorm.normedField (Padic l) E; infer_instance)
  let F : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} →
      Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := fun R ↦
    Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)
  exact congrArg F hs

/-- The coefficient presentations have the same underlying abelian sheaves.
Source: blueprint integral-limit clause 3 and integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions).
Proof: the section-ring construction keeps the additive group and restriction maps
of the internal ring. On the point the two continuous-function constructions have
identical sections and restrictions: the extending absolute value is the spectral
norm, hence defines the same topology. Presheaf extensionality and proof irrelevance
identify these sheaves, and applying the same point inverse image preserves equality.
The completed commutative ring sheaf retains the ring data of the completed ring
sheaf; forgetting its commutativity and multiplication keeps exactly its additive
groups and restrictions. Sheaf extensionality gives the second equality. -/
theorem integralSectionAbIdentifications (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) (AdicCompletion.ring l E X)) =
        (coefficientRing X (sfbCondensedIntegers l E)).X ∧
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E X) =
        sfbCompletedIntegersAb l E X := by
  constructor
  · change (upperStarFromPoint X).obj (DerivedNakayama.integerRing l E) =
      (upperStarFromPoint X).obj (sfbCondensedIntegers l E).X
    exact congrArg (fun R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ↦
      (upperStarFromPoint X).obj R.X) (integralPointMon_eq l E)
  · rfl

private theorem ringPresheafMon_eq
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (R : Sheaf J RingCat.{u + 1}) :
    (sheafToPresheaf J Ab.{u + 1}).monObjObj
      ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R) =
        R.obj.monObjCompForget₂ := by
  apply MonObj.ext
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  let : MonObj A.obj := R.obj.monObjCompForget₂
  exact Sheaf.μ_comp_map_mul A

private theorem liftSectionRingIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (A : Sheaf J Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (S : Sheaf J CommRingCat.{u + 1})
    (a : A ≅ (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    [IsMonHom a.hom] :
    ∃! e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A ≅ S,
      (sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.hom = a.hom := by
  let F := (Monoidal.monFunctorCategoryEquivalence Cᵒᵖ Ab.{u + 1}).functor
  let h := Functor.whiskerRight
    (F.map ((sheafToPresheaf J Ab.{u + 1}).mapMon.map (Mon.ofHom a.hom)))
    InternalAbelianSheafModule.monToRing
  let k := Functor.whiskerRight
    (F.map ((sheafToPresheaf J Ab.{u + 1}).mapMon.map (Mon.ofHom a.inv)))
    InternalAbelianSheafModule.monToRing
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let B := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hmon : (sheafToPresheaf J Ab.{u + 1}).monObjObj B = R.obj.monObjCompForget₂ :=
    ringPresheafMon_eq J R
  let BP := F.obj ((sheafToPresheaf J Ab.{u + 1}).mapMon.obj (Mon.mk B)) ⋙
    InternalAbelianSheafModule.monToRing
  let b : BP ≅ R.obj := by
    refine NatIso.ofComponents (fun U ↦ ?_) (fun _ ↦ ?_)
    · refine @RingEquiv.toRingCatIso (BP.obj U) (R.obj.obj U)
        (RingCat.ring _) (RingCat.ring _) ?_
      refine { toEquiv := Equiv.refl _, map_add' := fun _ _ ↦ rfl, map_mul' := ?_ }
      intro x y
      change (((sheafToPresheaf J Ab.{u + 1}).monObjObj B).mul.app U).hom
        (TensorProduct.tmul ℤ x y) = _
      have hh := congrArg (fun m : MonObj B.obj ↦ m.mul) hmon
      rw [hh]
      rfl
    · ext x
      rfl
  let d : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A ≅ S :=
    { hom := ⟨{ app := fun U ↦
                  @CommRingCat.ofHom
                    ((InternalAbelianSheafModule.sectionRingSheaf J A).obj.obj U)
                    (S.obj.obj U) _ _ ((h ≫ b.hom).app U).hom
                naturality := fun U V f ↦ by
                  apply (forget₂ CommRingCat RingCat).map_injective
                  exact (h ≫ b.hom).naturality f }⟩
      inv := ⟨{ app := fun U ↦
                  @CommRingCat.ofHom (S.obj.obj U)
                    ((InternalAbelianSheafModule.sectionRingSheaf J A).obj.obj U)
                    _ _ ((b.inv ≫ k).app U).hom
                naturality := fun U V f ↦ by
                  apply (forget₂ CommRingCat RingCat).map_injective
                  exact (b.inv ≫ k).naturality f }⟩
      hom_inv_id := by
        ext U x
        have hh := congr_app (congrArg (fun f : A ⟶ A ↦ f.hom) a.hom_inv_id) U
        exact ConcreteCategory.congr_hom hh x
      inv_hom_id := by
        ext U x
        have hh := congr_app (congrArg (fun f : B ⟶ B ↦ f.hom) a.inv_hom_id) U
        exact ConcreteCategory.congr_hom hh x }
  have hd : (sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map d.hom = a.hom := by
    ext U x
    rfl
  refine ⟨d, hd, ?_⟩
  intro e he
  apply Iso.ext
  apply (sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).map_injective
  exact he.trans hd.symm

/-- Reconstructing section rings retains the unique projection-normalized coefficient
comparison. After the endpoint identifications, forgetting to abelian sheaves fixes
the entire underlying additive map.
Source: blueprint integral-limit clause 3 and integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions).
Proof: the spectral absolute value defining DerivedNakayama.integerRing is the
spectral norm defining sfbCondensedIntegers, so the continuous-function sheaves and
their point pullbacks agree. The chosen abelian comparison is a monoid homomorphism
in both directions by sfb_integral_coefficient_limit. Evaluating its multiplication
and unit identities reconstructs a commutative-ring isomorphism on sections.
Naturality is unchanged. Forgetting to abelian sheaves is faithful, so the fixed
underlying comparison determines this ring isomorphism uniquely. -/
theorem integralSectionRingIso_existsUnique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ∃! e : CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (AdicCompletion.ring l E X) ≅
        WeilConjectures.completedIntegralCommRingSheafUnrestricted l E X,
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.hom =
          eqToHom (integralSectionAbIdentifications l E X).1 ≫
            (integralLimitAbComparison l E X).hom ≫
              eqToHom (integralSectionAbIdentifications l E X).2.symm := by
  let J := Scheme.ProEt.topology X
  let A := AdicCompletion.ring l E X
  let B := sfbCompletedIntegersAb l E X
  let c := eqToIso (congrArg (coefficientRing X) (integralPointMon_eq l E))
  have hm : IsMonHom (integralLimitAbComparison l E X).hom :=
    (integralLimitAbComparison_existsUnique l E X).exists.choose_spec.1
  let := hm
  let am := c ≪≫ Mon.mkIso' (integralLimitAbComparison l E X)
  let a : A ≅ B := (Mon.forget _).mapIso am
  have ha : IsMonHom a.hom := am.hom.isMonHom_hom
  let := ha
  let S := WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E X
  obtain ⟨d, hd, _⟩ := liftSectionRingIso J A S a
  have hn : (sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map d.hom =
      eqToHom (integralSectionAbIdentifications l E X).1 ≫
        (integralLimitAbComparison l E X).hom ≫
          eqToHom (integralSectionAbIdentifications l E X).2.symm := by
    rw [hd]
    dsimp only [a, am, Iso.trans_hom, Functor.mapIso_hom, c, eqToIso.hom]
    rw [Functor.map_comp]
    change (Mon.forget _).map (eqToHom _) ≫ _ = _
    rw [eqToHom_map]
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  refine ⟨d, hn, ?_⟩
  intro e he
  apply Iso.ext
  apply (sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map_injective
  exact he.trans hn.symm

/-- The ring comparison fixed by the published finite-projection normalization.
Source: blueprint integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions). -/
def integralSectionRingIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :=
  (integralSectionRingIso_existsUnique l E X).exists.choose

/-- The actual section-action functor, followed by scalar transport along the inverse
of the specified coefficient isomorphism. Neither functor is chosen by existence.
Source: Stacks 00YV; blueprint integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions). -/
def integralSectionFunctor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    AdicCompletion.Modules l E X ⥤ WeilConjectures.scalarReductionSource.{u, u} l E X :=
  (CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (AdicCompletion.ring l E X)).functor ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralSectionRingIso l E X).inv)

private noncomputable def restrictionRoundTrip
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.restrictScalars.{u + 1} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{u + 1} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
        (c.hom.hom.app U).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

private theorem restrictionTriangle
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) (M : SheafOfModules.{u + 1} S) :
    (SheafOfModules.restrictScalars c.hom).map ((restrictionRoundTrip c).inv.app M) ≫
      (restrictionRoundTrip c.symm).hom.app
        ((SheafOfModules.restrictScalars c.hom).obj M) = 𝟙 _ := by
  ext U x
  rfl

private noncomputable def restrictionEquivalence
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (restrictionRoundTrip c).symm
  counitIso := restrictionRoundTrip c.symm
  functor_unitIso_comp := restrictionTriangle c

private theorem restriction_isEquivalence
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} c.hom).IsEquivalence :=
  (restrictionEquivalence c).isEquivalence_functor

/-- The prescribed section-action comparison is an additive equivalence.
Source: Stacks 00YV, 03DA; blueprint integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions).
Proof: sectionModuleEquivalence is the existing exact equivalence with the same
underlying abelian sheaves. Restriction along the inverse coefficient isomorphism
has inverse restriction along its forward map. The unit and counit are the identity
on sections, with the two scalar actions identified by the inverse equations.
Both functors preserve addition on every section, so their composite is additive. -/
theorem integralSectionFunctor_properties (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    (integralSectionFunctor l E X).Additive ∧
      (integralSectionFunctor l E X).IsEquivalence := by
  let c := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (integralSectionRingIso l E X).symm
  let : (SheafOfModules.restrictScalars c.hom).IsEquivalence := restriction_isEquivalence c
  let F := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (AdicCompletion.ring l E X)
  let : F.functor.IsEquivalence := F.isEquivalence_functor
  constructor
  · dsimp only [integralSectionFunctor]
    infer_instance
  · exact inferInstanceAs (F.functor ⋙ SheafOfModules.restrictScalars c.hom).IsEquivalence

/-- Additivity of the actual section-action functor.
Source: blueprint integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions). -/
instance integralSectionFunctor_additive (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) : (integralSectionFunctor l E X).Additive :=
  (integralSectionFunctor_properties l E X).1

/-- Equivalence of the actual section-action functor.
Source: blueprint integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions). -/
instance integralSectionFunctor_isEquivalence (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) : (integralSectionFunctor l E X).IsEquivalence :=
  (integralSectionFunctor_properties l E X).2

/-- Localization of the fixed section-action equivalence on unbounded complexes.
Its forward functor is the localization of integralSectionFunctor, with Mathlib's
canonical localization comparison on every complex.
Source: Stacks 05RU; blueprint integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions). -/
def integralSectionDerivedEquivalence (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    DerivedCategory (AdicCompletion.Modules l E X) ≌
      DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E X) :=
  letI : (integralSectionFunctor l E X).asEquivalence.functor.Additive :=
    (integralSectionFunctor_properties l E X).1
  (integralSectionFunctor l E X).asEquivalence.mapDerivedCategory

private def integralEncoding (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) : IntegralPresentation.Encoding l E X where
  ringIso := integralSectionRingIso l E X
  modules := (integralSectionFunctor l E X).asEquivalence
  functor_eq := rfl
  additive := by
    change (integralSectionFunctor l E X).Additive
    infer_instance
  inverseAdditive := by
    let : (integralSectionFunctor l E X).asEquivalence.functor.Additive :=
      inferInstanceAs (integralSectionFunctor l E X).Additive
    infer_instance

private theorem finiteTopology_discrete (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have hm : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  have ht := congrArg (fun m : PseudoMetricSpace E ↦
    m.toUniformSpace.toTopologicalSpace) hm
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  apply QuotientAddGroup.discreteTopology
  apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
  have hb := (Padic.coefficientExtension_integers_coset_basis l E 0).mem_of_mem
    (i := n) trivial
  change @Membership.mem (Set (Padic.coefficientExtensionIntegers l E)) _ _
    (@nhds _ (TopologicalSpace.induced _ _) 0) _ at hb
  change @Membership.mem (Set (Padic.coefficientExtensionIntegers l E)) _ _
    (@nhds _ (TopologicalSpace.induced _ _) 0) _
  rw [← hti]
  have he : {y : Padic.coefficientExtensionIntegers l E |
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) y =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) 0} =
      (Padic.coefficientExtensionIdeal l E (n + 1)).toAddSubgroup := by
    ext y
    change _ = _ ↔ y ∈ Padic.coefficientExtensionIdeal l E (n + 1)
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
  rw [he] at hb
  exact hb

private theorem finiteEncoding_ringIso_unique
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) (e f : FiniteDiscreteOrdinary.Encoding A X) :
    e.ringIso = f.ringIso := by
  apply Iso.ext
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    (FiniteDiscreteOrdinary.sectionRing A X).property
  ext U a
  exact (e.normalization U a).trans (f.normalization U a).symm

private theorem finiteEncoding_functor_eq
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) (e f : FiniteDiscreteOrdinary.Encoding A X) :
    e.ordinary.functor = f.ordinary.functor := by
  rw [e.ordinary_functor, f.ordinary_functor, finiteEncoding_ringIso_unique A X e f]

private theorem finiteBounded_iso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Finite A]
    (X : Scheme.{u}) {K L : Scheme.proEtaleDerivedCategory X A} (e : K ≅ L) :
    FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X K ↔
      FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X L := by
  constructor
  · intro h
    exact ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e h.1,
      fun q ↦ FiniteDiscreteOrdinary.constructible_of_iso A X
        ((DerivedCategory.homologyFunctor _ q).mapIso e) (h.2 q)⟩
  · intro h
    exact ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e.symm h.1,
      fun q ↦ FiniteDiscreteOrdinary.constructible_of_iso A X
        ((DerivedCategory.homologyFunctor _ q).mapIso e.symm) (h.2 q)⟩

private theorem finiteEncoding_constructible
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A] (X : Scheme.{u}) [IsNoetherian X]
    (e : FiniteDiscreteOrdinary.Encoding A X)
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A X)) :
    constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X K ↔
      FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X
        (e.ordinaryDerived.functor.obj K) := by
  obtain ⟨f, hf⟩ := FiniteDiscreteOrdinary.finiteCoefficientModelComparison A X
  have h := finiteEncoding_functor_eq A X e f
  exact (hf.boundedConstructible K).trans
    (finiteBounded_iso A X
      ((Functor.mapDerivedCategoryNatIso (eqToIso h)).app K).symm)

private theorem reflect_roos_complete
    {C D : Type*} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] [F.IsEquivalence]
    {V : ℕ → C} {W : ℕ → D} [HasProduct V] [HasProduct W]
    (t : ∀ n, V (n + 1) ⟶ V n) (s : ∀ n, W (n + 1) ⟶ W n)
    (a : ∀ n, F.obj (V n) ≅ W n)
    (K : C) (p : ∀ n, K ⟶ V n) (q : ∀ n, F.obj K ⟶ W n)
    (ht : ∀ n, F.map (t n) ≫ (a n).hom = (a (n + 1)).hom ≫ s n)
    (hp : ∀ n, F.map (p n) ≫ (a n).hom = q n)
    (δ : (∏ᶜ W) ⟶ (F.obj K)⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle s (F.obj K) (Pi.lift q) δ) :
    ∃ δ' : (∏ᶜ V) ⟶ K⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle t K (Pi.lift p) δ' := by
  let : HasProduct (fun n ↦ F.obj (V n)) :=
    hasLimit_of_iso (Discrete.natIso (F := Discrete.functor W)
      (G := Discrete.functor (fun n ↦ F.obj (V n))) (fun n ↦ (a n.as).symm))
  let B : F.obj (∏ᶜ V) ≅ ∏ᶜ W := PreservesProduct.iso F V ≪≫
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by apply Pi.hom_ext; intro n; simp [Category.assoc]
      inv_hom_id := by apply Pi.hom_ext; intro n; simp [Category.assoc] }
  have hB (n : ℕ) : B.hom ≫ Pi.π W n = F.map (Pi.π V n) ≫ (a n).hom := by
    simp [B]
  have hfirst : F.map (Pi.lift p) ≫ B.hom = Pi.lift q := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hB, Pi.lift_π]
    rw [← Category.assoc, ← F.map_comp, Pi.lift_π, hp]
  have hmiddle : F.map (towerTransitionEndomorphism t) ≫ B.hom =
      B.hom ≫ towerTransitionEndomorphism s := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hB, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Pi.lift_π, Functor.map_sub]
    simp only [reassoc_of% hB]
    erw [F.map_id, Category.id_comp]
    congr 1
    rw [← F.map_comp_assoc, Pi.lift_π, Functor.map_comp, Category.assoc, ht]
  let δ' := F.preimage (B.hom ≫ δ ≫ (F.commShiftIso (1 : ℤ)).inv.app K)
  refine ⟨δ', (F.map_distinguished_iff _).mp ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hT _
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) B B ?_ ?_ ?_
  · change F.map (Pi.lift p) ≫ B.hom = 𝟙 _ ≫ Pi.lift q
    simpa only [Category.id_comp] using hfirst
  · exact hmiddle
  · change (F.map δ' ≫ (F.commShiftIso (1 : ℤ)).hom.app K) ≫
      (shiftFunctor D (1 : ℤ)).map (𝟙 _) = B.hom ≫ δ
    erw [(shiftFunctor D (1 : ℤ)).map_id]
    simp only [δ', F.map_preimage, Category.assoc, Iso.inv_hom_id_app]
    simp only [Functor.comp_obj, Category.comp_id]

private theorem finiteSupport_of_interval
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (a b : ℤ)
    (h : ∀ q : ℤ, q < a ∨ b < q → IsZero ((DerivedCategory.homologyFunctor C q).obj K)) :
    Set.Finite {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C q).obj K)} := by
  apply (Set.finite_Icc a b).subset
  intro q hq
  by_contra hn
  exact hq (h q (by simpa only [Set.mem_Icc, not_and_or, not_le] using hn))

private theorem bounded_of_interval
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (a b : ℤ)
    (h : ∀ q : ℤ, q < a ∨ b < q → IsZero ((DerivedCategory.homologyFunctor C q).obj K)) :
    DerivedCategory.TStructure.t.bounded K := by
  exact ⟨⟨a, (DerivedCategory.isGE_iff K a).mpr (fun q hq ↦ h q (Or.inl hq))⟩,
    ⟨b, (DerivedCategory.isLE_iff K b).mpr (fun q hq ↦ h q (Or.inr hq))⟩⟩

private theorem support_subset_iff_interval
    {X : Scheme.{u}} {A : Type u} [CommRing A]
    (K : Scheme.proEtaleDerivedCategory X A) (a b : ℤ) :
    Scheme.proEtaleCohomologicalSupport K ⊆ Set.Icc a b ↔
      ∀ q : ℤ, q < a ∨ b < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
  classical
  constructor
  · intro h q hq
    by_contra hz
    have hh := h hz
    rcases hq with hq | hq
    · exact (not_lt_of_ge hh.1) hq
    · exact (not_lt_of_ge hh.2) hq
  · intro h q hq
    by_contra hn
    exact hq (h q (by simpa only [Set.mem_Icc, not_and_or, not_le] using hn))

/-- The continuous predicate is the existing integral predicate under the canonical
coefficient and section-action comparison, rather than an unrelated new notion.
Source: blueprint integral-criterion final sentence, proof step 8
(blueprint: det-prop-integral-criterion-reductions).
Proof: the finite projections of integralSectionRingIso are the specified quotient
maps by its underlying integral-limit normalization. On a K-flat representative,
the section-action equivalence identifies tensoring with each quotient with the
recorded scalarReductionDerivedExtension; this also identifies the quotient units
and transitions. Exact equivalences preserve products and the augmented Roos
triangle, so IsDerivedComplete agrees with IsSfDerivedComplete. At each positive
finite level the continuous ring is constant. Finite constant local models agree
with locally constant finite modules: finite presentation over a finite ring gives
a finite module, and a finite module has a finite presentation. The Noetherian
finite stratifications agree. Finally homology is preserved by the exact
equivalence, and support in [r,s] means precisely vanishing outside [r,s]. These
identifications give both implications, including the same uniform interval. -/
theorem continuousIntegralConstructible_iff_sfIntegralConstructible (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    continuousIntegralConstructible l E X K ↔
      WeilConjectures.sfIntegralConstructible l E X
        ((integralSectionDerivedEquivalence l E X).functor.obj K) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := integralEncoding l E X
  obtain ⟨e, a, ha⟩ := IntegralPresentation.fixed_integral_section_squares l E X A
    (integralLimitAbComparison l E X)
    (integralLimitAbComparison_existsUnique l E X).exists.choose_spec
    (integralSectionAbIdentifications l E X).1
    (integralSectionAbIdentifications l E X).2
    (integralSectionRingIso_existsUnique l E X).exists.choose_spec
  have hb (n : ℕ) := IntegralPresentation.finiteComparison_existsUnique l E X A n (e n) (a n)
  choose b hbu _ using hb
  have ht := IntegralPresentation.integral_completion_transition_comparison l E X A e a ha b hbu
  let : A.derived.functor.Additive :=
    by change A.modules.functor.mapDerivedCategory.Additive; infer_instance
  let : A.derived.functor.CommShift ℤ :=
    by change A.modules.functor.mapDerivedCategory.CommShift ℤ; infer_instance
  let : A.derived.functor.IsTriangulated :=
    by change A.modules.functor.mapDerivedCategory.IsTriangulated; infer_instance
  let : HasCountableProducts (DerivedCategory (WeilConjectures.scalarReductionSource l E X)) :=
    IntegralPresentation.completedProducts l E X
  let : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E X)) :=
    { out := fun I _ ↦ Adjunction.hasLimitsOfShape_of_equivalence A.derived.functor }
  have hcomplete : IsDerivedComplete l E X K ↔
      WeilConjectures.IsSfDerivedComplete l E X (A.derived.functor.obj K) := by
    constructor
    · intro hK
      exact (IntegralPresentation.integral_completion_presentation.{u, u} l E X A e a ha K hK).1
    · rintro ⟨hp, δ, hδ⟩
      let := hp
      have ht' (n : ℕ) :
          A.derived.functor.map (AdicCompletion.integralStep l E X K n) ≫
              (IntegralPresentation.restrictedComparison l E X A n (e n) (a n)
                (b n) K).inv =
            (IntegralPresentation.restrictedComparison l E X A (n + 1) (e (n + 1))
              (a (n + 1)) (b (n + 1)) K).inv ≫
                (WeilConjectures.sfDerivedReductionTransition l E X n).app
                  (A.derived.functor.obj K) := by
        have h := ht K n
        change (WeilConjectures.sfDerivedReductionTransition l E X n).app
            (A.derived.functor.obj K) ≫
              (IntegralPresentation.restrictedComparison l E X A n (e n) (a n)
                (b n) K).hom =
            (IntegralPresentation.restrictedComparison l E X A (n + 1) (e (n + 1))
              (a (n + 1)) (b (n + 1)) K).hom ≫
                A.derived.functor.map (AdicCompletion.integralStep l E X K n) at h
        apply (cancel_epi (IntegralPresentation.restrictedComparison l E X A (n + 1)
          (e (n + 1)) (a (n + 1)) (b (n + 1)) K).hom).mp
        simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
          Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id] using
          congrArg (fun f ↦ f ≫
            (IntegralPresentation.restrictedComparison l E X A n (e n) (a n) (b n) K).inv)
            h.symm
      have hu' (n : ℕ) :
          A.derived.functor.map ((Mod.derivedExtendMapDerivedCategoryAdjunction
            (AdicCompletion.quotient l E X n)).unit.app K) ≫
              (IntegralPresentation.restrictedComparison l E X A n (e n) (a n)
                (b n) K).inv =
            (WeilConjectures.sfDerivedReductionUnit l E X n).app
              (A.derived.functor.obj K) := by
        simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
          congrArg (fun f ↦ f ≫
            (IntegralPresentation.restrictedComparison l E X A n (e n) (a n) (b n) K).inv)
            (hbu n K).symm
      obtain ⟨δ', hδ'⟩ := reflect_roos_complete
        (V := AdicCompletion.integralLevel l E X K)
        (W := fun n ↦ (WeilConjectures.sfDerivedReductionRestricted l E X n).obj
          (A.derived.functor.obj K)) A.derived.functor
        (AdicCompletion.integralStep l E X K)
        (fun n ↦ (WeilConjectures.sfDerivedReductionTransition l E X n).app
          (A.derived.functor.obj K))
        (fun n ↦ (IntegralPresentation.restrictedComparison l E X A n (e n) (a n)
          (b n) K).symm) K
        (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction
          (AdicCompletion.quotient l E X n)).unit.app K)
        (fun n ↦ (WeilConjectures.sfDerivedReductionUnit l E X n).app
          (A.derived.functor.obj K))
        (by simpa only [Iso.symm_hom] using ht')
        (by simpa only [Iso.symm_hom] using hu') δ hδ
      exact AdicCompletion.isDerivedComplete_of_roos l E X K δ' hδ'
  let (n : ℕ) : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let (n : ℕ) : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) :=
    finiteTopology_discrete l E n
  have hmodel (n : ℕ) :
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) X
          ((AdicCompletion.derivedReduction l E X n).obj K) ↔
        FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible
          (Padic.coefficientExtensionRing l E (n + 1)) X
          ((WeilConjectures.scalarReductionDerivedExtension l E X n).obj
            (A.derived.functor.obj K)) := by
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    exact (finiteEncoding_constructible (Padic.coefficientExtensionRing l E (n + 1)) X
      (e n) _).trans (finiteBounded_iso _ X ((b n).app K).symm)
  have hbounds (n : ℕ) (r s : ℤ) :
      (∀ q : ℤ, q < r ∨ s < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((AdicCompletion.derivedReduction l E X n).obj K))) ↔
      (∀ q : ℤ, q < r ∨ s < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((WeilConjectures.scalarReductionDerivedExtension l E X n).obj
            (A.derived.functor.obj K)))) := by
    apply forall_congr'
    intro q
    apply imp_congr_right
    intro _
    exact (show IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((AdicCompletion.derivedReduction l E X n).obj K)) ↔
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((e n).ordinaryDerived.functor.obj
          ((AdicCompletion.derivedReduction l E X n).obj K))) from
      ⟨(e n).ordinary.functor.isZero_homologyFunctor_mapDerivedCategory_obj,
        Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
          (e n).ordinary.functor⟩).trans
        ((DerivedCategory.homologyFunctor _ q).mapIso ((b n).app K)).isZero_iff.symm
  change _ ↔ WeilConjectures.sfIntegralConstructible l E X (A.derived.functor.obj K)
  constructor
  · rintro ⟨hK, hcons, r, s, hrs, hv⟩
    refine ⟨hcomplete.mp hK, r, s, hrs, fun n ↦ ?_⟩
    have hc := (hmodel n).mp (hcons n)
    have hz := (hbounds n r s).mp (hv n)
    exact ⟨⟨finiteSupport_of_interval _ r s hz, hc.2⟩,
      (support_subset_iff_interval _ r s).mpr hz⟩
  · rintro ⟨hK, r, s, hrs, h⟩
    have hv (n : ℕ) := (support_subset_iff_interval _ r s).mp (h n).2
    refine ⟨hcomplete.mpr hK, fun n ↦ ?_, r, s, hrs, fun n ↦ (hbounds n r s).mpr (hv n)⟩
    apply (hmodel n).mpr
    exact ⟨bounded_of_interval _ r s (hv n), (h n).1.2⟩

attribute [local irreducible] WeilConjectures.scalarReductionExistence
  WeilConjectures.scalarReductionDerivedExistence

private theorem reductionAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

private theorem reductionAbLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

private theorem reductionRingSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  hasSheafifyEssentiallySmallSite _ _

private theorem reductionSiteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance] reductionSiteSmall

attribute [local instance] reductionAbSheafify reductionAbLocallyBijective reductionRingSheafify

attribute [local instance] WeilConjectures.scalarReductionExtensionAdditive
  WeilConjectures.scalarReductionRestrictionLimits
  WeilConjectures.scalarReductionRestrictionColimits
  Scheme.proEtaleRingRestrictScalars_preservesFiniteLimits
  Scheme.proEtaleRingRestrictScalars_preservesFiniteColimits

private abbrev finiteScalarRestriction (X : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (a : A →+* B) :=
  Scheme.proEtaleRingRestrictScalars
    ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (R := ULift.{u + 1, u} A)
        (S := ULift.{u + 1, u} B) a.ulift.{u + 1, u + 1}))

private def coefficientModuleIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {B Q S : Sheaf J CommRingCat.{u + 1}} (p : B ⟶ Q) (q : B ⟶ S)
    (e : Q ≅ S) (he : p ≫ e.hom = q) :
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map p)).obj
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Q)) ≅
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map q)).obj
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) := by
  have hc (U : Cᵒᵖ) (b : B.obj.obj U) :
      e.hom.hom.app U (p.hom.app U b) = q.hom.app U b :=
    ConcreteCategory.congr_hom (congr_app (congrArg (fun f ↦ f.hom) he) U) b
  refine (SheafOfModules.fullyFaithfulForget.{u + 1} _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ ?_) ?_)
  · let UQ := ((SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map p)).obj
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Q))).val.obj U
    let US := ((SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map q)).obj
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))).val.obj U
    refine { hom := ModuleCat.ofHom (X := UQ) (Y := US)
               { toFun := fun x ↦ e.hom.hom.app U x
                 map_add' := fun x y ↦ map_add _ x y
                 map_smul' := ?_ }
             inv := ModuleCat.ofHom (X := US) (Y := UQ)
               { toFun := fun x ↦ e.inv.hom.app U x
                 map_add' := fun x y ↦ map_add _ x y
                 map_smul' := ?_ }
             hom_inv_id := ?_
             inv_hom_id := ?_ }
    · intro b x
      change B.obj.obj U at b
      change Q.obj.obj U at x
      change e.hom.hom.app U (p.hom.app U b * x) =
        q.hom.app U b * e.hom.hom.app U x
      rw [map_mul, hc]
    · intro b x
      change B.obj.obj U at b
      change S.obj.obj U at x
      change e.inv.hom.app U (q.hom.app U b * x) =
        p.hom.app U b * e.inv.hom.app U x
      rw [map_mul, ← hc]
      have h := ConcreteCategory.congr_hom
        (congr_app (congrArg (fun f ↦ f.hom) e.hom_inv_id) U) (p.hom.app U b)
      rw [show e.inv.hom.app U (e.hom.hom.app U (p.hom.app U b)) =
        p.hom.app U b from h]
    · ext x
      exact ConcreteCategory.congr_hom
        (congr_app (congrArg (fun f ↦ f.hom) e.hom_inv_id) U) x
    · ext x
      exact ConcreteCategory.congr_hom
        (congr_app (congrArg (fun f ↦ f.hom) e.inv_hom_id) U) x
  · intro U V f
    ext x
    exact ConcreteCategory.congr_hom (e.hom.hom.naturality f) x

private def tensorCoefficientIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective Ab.{u + 1}] [HasSheafify J Ab.{u + 1}]
    {B : Sheaf J CommRingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)} (e : M ≅ N) :
    SheafOfModules.leftTensorSheaf M ≅ SheafOfModules.leftTensorSheaf N :=
  NatIso.ofComponents (fun P ↦ (SheafOfModules.siteSheafTensorRight P).mapIso e)
    (fun f ↦ (SheafOfModules.siteSheafTensorSecondMap_naturality e.hom f).symm)

private theorem ordinarySuccessiveReductionTriangle (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (K : DerivedCategory (WeilConjectures.scalarReductionSource l E X))
    (n : ℕ) :
    ∃ (a : Padic.coefficientExtensionRing l E (n + 2) →+*
          Padic.coefficientExtensionRing l E (n + 1))
      (b : Padic.coefficientExtensionRing l E (n + 2) →+*
          Padic.coefficientExtensionRing l E 1)
      (T : CategoryTheory.Pretriangulated.Triangle
        (Scheme.proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 2)))),
      T ∈ distTriang _ ∧
      Nonempty (T.obj₁ ≅ (finiteScalarRestriction X a).mapDerivedCategory.obj
        ((WeilConjectures.scalarReductionDerivedExtension.{u, u} l E X n).obj K)) ∧
      Nonempty (T.obj₂ ≅
        (WeilConjectures.scalarReductionDerivedExtension.{u, u} l E X (n + 1)).obj K) ∧
      Nonempty (T.obj₃ ≅ (finiteScalarRestriction X b).mapDerivedCategory.obj
        ((WeilConjectures.scalarReductionDerivedExtension.{u, u} l E X 0).obj K)) := by
  classical
  let J := Scheme.ProEt.topology X
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify J Ab.{u + 1} := WeilConjectures.integralCoefficientAbSheafify.{u, u} X
  let : J.WEqualsLocallyBijective Ab.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X
  let B := WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E X
  let t := spCompletedScalarSection.{u, u} l E X (Padic.coefficientExtensionUniformizer l E)
  obtain ⟨_, _, _, hreg, _, e, _, he, _, htr⟩ :=
    sp_completed_coefficient_regular_quotients.{u, u} l E X
  have hcompat (m k : ℕ) (h : m ≤ k) :
      WeilConjectures.completedIntegralCommRingProjectionUnrestricted.{u, u} l E X k ≫
          spUniformizerQuotientTransition.{u, u} l E X h =
        WeilConjectures.completedIntegralCommRingProjectionUnrestricted.{u, u} l E X m := by
    obtain ⟨r, _, hr, _, hs, _⟩ := htr m k h
    rw [← he k, Category.assoc, ← hs, ← Category.assoc, hr, he m]
  obtain ⟨P, f, hP, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := B) (DerivedCategory.Q.objPreimage K)
  let : QuasiIso f := hf
  let eK : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let S :=
    SheafOfModules.tensorCoefficientBCochainSequence.{u + 1, u, u + 1} B t (n + 2) (by omega) P
  have hS : S.ShortExact :=
    SheafOfModules.tensorCoefficientBCochainSequence_shortExact.{u + 1, u, u + 1} B t (n + 2)
      (by omega) (fun U ↦ by simpa using (hreg 0 U).1) P (fun i ↦
        (exactFunctor _ _).prop_of_iso
          (SheafOfModules.siteSheafTensorRightIso B (P.X i)).symm (hflat i))
  let E' (k : ℕ) := WeilConjectures.scalarReductionExtension.{u, u} l E X k
  let R (k : ℕ) := WeilConjectures.scalarReductionRestriction.{u, u} l E X k
  let c (k : ℕ) : SheafOfModules.quotientTensorB.{u + 1, u, u + 1} B t (k + 1) ≅ E' k ⋙ R k :=
    tensorCoefficientIso (coefficientModuleIso
      (principalPowerRingProjection B t (k + 1))
      (WeilConjectures.completedIntegralCommRingProjectionUnrestricted.{u, u} l E X k)
      (e k) (he k)) ≪≫ WeilConjectures.reductionTensorIso.{u, u} l E X k
  let a : Padic.coefficientExtensionRing l E (n + 2) →+*
      Padic.coefficientExtensionRing l E (n + 1) :=
    Ideal.Quotient.factorPow (Ideal.span {Padic.coefficientExtensionUniformizer l E})
      (by omega)
  let b : Padic.coefficientExtensionRing l E (n + 2) →+*
      Padic.coefficientExtensionRing l E 1 :=
    Ideal.Quotient.factorPow (Ideal.span {Padic.coefficientExtensionUniformizer l E})
      (by omega)
  let A := finiteScalarRestriction X a
  let D := finiteScalarRestriction X b
  let V := (R (n + 1)).mapHomologicalComplex (.up ℤ)
  have : Presheaf.IsLocallySurjective J
      (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (WeilConjectures.completedIntegralCommRingProjectionUnrestricted.{u, u} l E X
          (n + 1))).hom) := by
    rw [← he (n + 1), Functor.map_comp]
    have := SheafOfModules.principalProjection_locallySurjective.{u + 1, u, u + 1} B t (n + 2)
    infer_instance
  have : (R (n + 1)).Full :=
    SheafOfModules.restriction_full
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (WeilConjectures.completedIntegralCommRingProjectionUnrestricted.{u, u} l E X (n + 1)))
  have : (R (n + 1)).Faithful := SheafOfModules.restriction_faithful _
  let cA : A ⋙ R (n + 1) ≅ R n :=
    SheafOfModules.restrictionComp _ _ _
      (by
        rw [← Functor.map_comp]
        exact congrArg
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
          (hcompat n (n + 1) (by omega)))
  let cD : D ⋙ R (n + 1) ≅ R 0 :=
    SheafOfModules.restrictionComp _ _ _
      (by
        rw [← Functor.map_comp]
        exact congrArg
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
          (hcompat 0 (n + 1) (by omega)))
  let N (k : ℕ) := ((E' k).mapHomologicalComplex (.up ℤ)).obj P
  let M₁ := (A.mapHomologicalComplex (.up ℤ)).obj (N n)
  let M₂ := N (n + 1)
  let M₃ := (D.mapHomologicalComplex (.up ℤ)).obj (N 0)
  let c₁ : S.X₁ ≅ V.obj M₁ := by
    change (((SheafOfModules.quotientTensorB B t (n + 2 - 1)).mapHomologicalComplex
      (.up ℤ)).obj P) ≅ V.obj M₁
    rw [show n + 2 - 1 = n + 1 by omega]
    exact (NatIso.mapHomologicalComplex (c n) (.up ℤ)).app P ≪≫
      ((Functor.mapHomologicalComplexCompIso cA (.up ℤ)).app (N n)).symm
  let c₂ : S.X₂ ≅ V.obj M₂ :=
    (NatIso.mapHomologicalComplex (c (n + 1)) (.up ℤ)).app P
  let c₃ : S.X₃ ≅ V.obj M₃ :=
    (NatIso.mapHomologicalComplex (c 0) (.up ℤ)).app P ≪≫
      ((Functor.mapHomologicalComplexCompIso cD (.up ℤ)).app (N 0)).symm
  let α := c₁.inv ≫ S.f ≫ c₂.hom
  let β := c₂.inv ≫ S.g ≫ c₃.hom
  have hαβ : α ≫ β = 0 := by simp [α, β, Category.assoc]
  have hSES : (ShortComplex.mk α β hαβ).ShortExact :=
    ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk c₁ c₂ c₃ (by simp [α]) (by simp [β])) hS
  obtain ⟨α', β', hz, hSES', _, _⟩ :=
    SheafOfModules.lift_shortExact V α β hαβ hSES
  let T := DerivedCategory.triangleOfSES hSES'
  have ec (k : ℕ) :
      (WeilConjectures.scalarReductionDerivedExtension.{u, u} l E X k).obj K ≅
        DerivedCategory.Q.obj (N k) := by
    letI : IsIso ((WeilConjectures.scalarReductionCounit.{u, u} l E X k).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
      (WeilConjectures.scalarReductionDerivedExistence.{u, u} l E X k).choose_spec
        |>.choose_spec.2.2 P hP
    exact ((WeilConjectures.scalarReductionDerivedExtension.{u, u} l E X k).mapIso eK).symm ≪≫
      asIso ((WeilConjectures.scalarReductionCounit.{u, u} l E X k).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
  refine ⟨a, b, T, DerivedCategory.triangleOfSES_distinguished hSES', ?_, ?_, ?_⟩
  · exact ⟨((A.mapDerivedCategoryFactors).app (N n)).symm ≪≫
      A.mapDerivedCategory.mapIso (ec n).symm⟩
  · exact ⟨(ec (n + 1)).symm⟩
  · exact ⟨((D.mapDerivedCategoryFactors).app (N 0)).symm ≪≫
      D.mapDerivedCategory.mapIso (ec 0).symm⟩

private theorem finiteRestriction_preserves (X : Scheme.{u}) [IsNoetherian X]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (a : A →+* B)
    (K : Scheme.proEtaleDerivedCategory X B) (r s : ℤ)
    (hK : FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible B X K)
    (hv : ∀ q : ℤ, q < r ∨ s < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) :
    FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X
        ((finiteScalarRestriction X a).mapDerivedCategory.obj K) ∧
      ∀ q : ℤ, q < r ∨ s < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((finiteScalarRestriction X a).mapDerivedCategory.obj K)) := by
  have h := Scheme.proEtaleFiniteScalarRestriction_constructible X A B a
  exact ⟨h.2.2.2.2.2 K hK.1 hK.2, fun q hq ↦ (h.2.2.2.2.1 K q).mpr (hv q hq)⟩

private theorem ordinaryConstructible_extension (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (T : CategoryTheory.Pretriangulated.Triangle (Scheme.proEtaleDerivedCategory X A))
    (hT : T ∈ distTriang _) (r s : ℤ)
    (h₁ : FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X T.obj₁)
    (h₃ : FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X T.obj₃)
    (hv₁ : ∀ q : ℤ, q < r ∨ s < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj T.obj₁))
    (hv₃ : ∀ q : ℤ, q < r ∨ s < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj T.obj₃)) :
    FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X T.obj₂ ∧
      ∀ q : ℤ, q < r ∨ s < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj T.obj₂) := by
  let P : ObjectProperty (Scheme.proEtaleDerivedCategory X A) := fun K ↦
    Set.Finite {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ q).obj K)} ∧
      ∀ q : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf X A
        ((DerivedCategory.homologyFunctor _ q).obj K)
  let := (Scheme.proEtale_bounded_constructible_isTriangulated X A).1
  let := (Scheme.proEtale_bounded_constructible_isTriangulated X A).2
  have hz (q : ℤ) (hq : q < r ∨ s < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj T.obj₂) := by
    exact (DerivedCategory.HomologySequence.exact₂ T hT q).isZero_of_both_isZero
      (hv₁ q hq) (hv₃ q hq)
  have hp : P T.obj₂ := P.ext_of_isTriangulatedClosed₂ T hT
    ⟨finiteSupport_of_interval _ r s hv₁, h₁.2⟩
    ⟨finiteSupport_of_interval _ r s hv₃, h₃.2⟩
  exact ⟨⟨bounded_of_interval _ r s hz, hp.2⟩, hz⟩

/-- First reduction versus all positive reductions with a uniform cohomological interval.
Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-integral-criterion/sk-prop-integral-criterion-reductions.md
(blueprint: det-prop-integral-criterion-reductions).

Proof:
1. For the reverse implication take n=0, which denotes exponent 1.
2. The finite extension DVR and finite quotient results give finite coefficient rings.
   Their continuous condensed sheaves are constant, and finitely presented modules over
   them are precisely finite modules. Thus the two finite constructibility conventions
   agree (sk-def-sfb-constructible, def-weil-proetale-constructible-sheaf,
   sk-def-sfb-pullback-from-point, det-prop-sfb-qlbar-colimit-x-integral-limit).
3. Cancellation of the uniformizer gives the short exact coefficient sequence
   0 -> R_(n-1) -> R_n -> R_1 -> 0 for n>1, with its R_n-linear maps
   (det-pe-derived-nakayama-resolution, def-weil-sheaf-of-modules-category).
4. Choose a flat-term K-flat resolution of K (lem-pc-kflat-resolution). Termwise
   tensor preserves that sequence (def-pc-flat-sheaf-modules). Its short-exact-sequence
   triangle (lem-weil-pbc-complex-ses-triangle) computes the reductions in D(R_n)
   by lem-pur-derived-change-of-rings, with the outer terms restricted from their
   quotient coefficient rings. No boundedness of the original K is required.
5. Exact restriction of scalars leaves the underlying sheaves and finite local models
   unchanged, so preserves constructibility and cohomological bounds
   (def-pc-sheaf-restrict-scalars, def-weil-proetale-constructible-sheaf).
6. Fix r<=s bounding K_1. Induction on the positive exponent and closure under
   distinguished triangles (lem-weil-proetale-dbc-triangulated) prove constructibility.
7. The long exact cohomology sequence (lem-sf-derived-homology-long-exact) has zero
   outer terms outside [r,s], hence zero middle term. This is the same interval at
   every level. Completeness is retained as in the source, though steps 1--7 do not use it.
8. For the integral interpretation, the pulled-back continuous integer ring is the
   completed finite coefficient tower (det-prop-sfb-qlbar-colimit-x-integral-limit).
   The canonical completion isomorphism identifies its augmented Roos triangle with
   the completeness triangle (sk-def-pe-derived-completion, def-weil-derived-limit,
   def-weil-derived-complete). Finite constructibility agrees by step 2, and support
   in [r,s] is exactly vanishing outside it (def-weil-cohomological-support).
   Thus the all-reductions condition is precisely the remaining integral condition
   of def-weil-derived-complete-integral-detailed. No Tor-amplitude is inserted. -/
theorem integral_reductions_constructible_iff (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X))
    (_hK : IsDerivedComplete l E X K) :
    constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
        ((AdicCompletion.derivedReduction l E X 0).obj K) ↔
      (∀ n : ℕ, constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1))
        X ((AdicCompletion.derivedReduction l E X n).obj K)) ∧
      ∃ r s : ℤ, r ≤ s ∧ ∀ (n : ℕ) (q : ℤ), q < r ∨ s < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((AdicCompletion.derivedReduction l E X n).obj K)) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := integralEncoding l E X
  obtain ⟨e, a, ha⟩ := IntegralPresentation.fixed_integral_section_squares l E X A
    (integralLimitAbComparison l E X)
    (integralLimitAbComparison_existsUnique l E X).exists.choose_spec
    (integralSectionAbIdentifications l E X).1
    (integralSectionAbIdentifications l E X).2
    (integralSectionRingIso_existsUnique l E X).exists.choose_spec
  have hb (n : ℕ) := IntegralPresentation.finiteComparison_existsUnique l E X A n (e n) (a n)
  choose b _ _ using hb
  let L := A.derived.functor.obj K
  let R (n : ℕ) := (WeilConjectures.scalarReductionDerivedExtension l E X n).obj L
  let (n : ℕ) : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let (n : ℕ) : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) :=
    finiteTopology_discrete l E n
  have hc (n : ℕ) :
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) X
          ((AdicCompletion.derivedReduction l E X n).obj K) ↔
        FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible
          (Padic.coefficientExtensionRing l E (n + 1)) X (R n) :=
    (finiteEncoding_constructible _ X (e n) _).trans
      (finiteBounded_iso _ X ((b n).app K).symm)
  have hv (n : ℕ) (q : ℤ) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((AdicCompletion.derivedReduction l E X n).obj K)) ↔
        IsZero ((DerivedCategory.homologyFunctor _ q).obj (R n)) := by
    exact (show IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((AdicCompletion.derivedReduction l E X n).obj K)) ↔
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((e n).ordinaryDerived.functor.obj
          ((AdicCompletion.derivedReduction l E X n).obj K))) from
      ⟨(e n).ordinary.functor.isZero_homologyFunctor_mapDerivedCategory_obj,
        Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
          (e n).ordinary.functor⟩).trans
        ((DerivedCategory.homologyFunctor _ q).mapIso ((b n).app K)).isZero_iff.symm
  constructor
  · intro h
    have h₀ := (hc 0).mp h
    obtain ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ := h₀.1
    let r' := min r s
    have hz₀ (q : ℤ) (hq : q < r' ∨ s < q) :
        IsZero ((DerivedCategory.homologyFunctor _ q).obj (R 0)) := by
      rcases hq with hq | hq
      · exact (DerivedCategory.isGE_iff _ r).mp hr q (lt_of_lt_of_le hq (min_le_left _ _))
      · exact (DerivedCategory.isLE_iff _ s).mp hs q hq
    have hn (n : ℕ) :
        FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible
            (Padic.coefficientExtensionRing l E (n + 1)) X (R n) ∧
          ∀ q : ℤ, q < r' ∨ s < q →
            IsZero ((DerivedCategory.homologyFunctor _ q).obj (R n)) := by
      induction n with
      | zero => exact ⟨h₀, hz₀⟩
      | succ n ih =>
        obtain ⟨α, β, T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
          ordinarySuccessiveReductionTriangle l E X L n
        have h₁ := finiteRestriction_preserves X α (R n) r' s ih.1 ih.2
        have h₃ := finiteRestriction_preserves X β (R 0) r' s h₀ hz₀
        have h₁' := (finiteBounded_iso _ X e₁).mpr h₁.1
        have h₃' := (finiteBounded_iso _ X e₃).mpr h₃.1
        have z₁ (q : ℤ) (hq : q < r' ∨ s < q) :=
          (h₁.2 q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e₁)
        have z₃ (q : ℤ) (hq : q < r' ∨ s < q) :=
          (h₃.2 q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e₃)
        obtain ⟨h₂, z₂⟩ := ordinaryConstructible_extension X _ T hT r' s h₁' h₃' z₁ z₃
        exact ⟨(finiteBounded_iso _ X e₂).mp h₂, fun q hq ↦
          (z₂ q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e₂.symm)⟩
    exact ⟨fun n ↦ (hc n).mpr (hn n).1,
      r', s, min_le_right _ _, fun n q hq ↦ (hv n q).mpr ((hn n).2 q hq)⟩
  · intro h
    exact h.1 0

/-- The first-reduction criterion describes the bounded constructible complete integral
category in the same continuous coefficient presentation.
Source: blueprint main-20261015, final sentence of sk-prop-integral-criterion-reductions.md
(blueprint: det-prop-integral-criterion-reductions).
Proof: apply integral_reductions_constructible_iff to the assumed complete K, and unfold
continuousIntegralConstructible. Its first conjunct is the given completeness, and its
remaining conjuncts are exactly all positive constructible reductions and the common
interval. The coefficient, completeness and support identifications are step 8 of the
preceding proof plan; in the original global setting this applies when l != p. -/
theorem continuousIntegralConstructible_iff_first_reduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X))
    (_hK : IsDerivedComplete l E X K) :
    continuousIntegralConstructible l E X K ↔
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
        ((AdicCompletion.derivedReduction l E X 0).obj K) := by
  exact ⟨fun h ↦ (integral_reductions_constructible_iff l E X K _hK).mpr h.2,
    fun h ↦ ⟨_hK, (integral_reductions_constructible_iff l E X K _hK).mp h⟩⟩

/-- The first-reduction criterion in the existing sectionwise integral category.
Source: blueprint integral-criterion final sentence
(blueprint: det-prop-integral-criterion-reductions).
Proof: combine continuousIntegralConstructible_iff_sfIntegralConstructible with
continuousIntegralConstructible_iff_first_reduction. Both comparisons use the same
specified coefficient transport and the original complete object K. -/
theorem sfIntegralConstructible_iff_first_reduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X))
    (_hK : IsDerivedComplete l E X K) :
    WeilConjectures.sfIntegralConstructible l E X
        ((integralSectionDerivedEquivalence l E X).functor.obj K) ↔
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
        ((AdicCompletion.derivedReduction l E X 0).obj K) := by
  exact (continuousIntegralConstructible_iff_sfIntegralConstructible l E X K).symm.trans
    (continuousIntegralConstructible_iff_first_reduction l E X K _hK)

end AlgebraicGeometry.ProEtale
