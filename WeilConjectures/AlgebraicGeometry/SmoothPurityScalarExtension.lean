/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import WeilConjectures.Topology.ContinuousMapCondensedRingMap
public import WeilConjectures.SixFunctors.ScalarSixPullback
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullbackSupplement
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.InternalSectionScalarAdjunctionSupplement

/-! # Scalar extension on constructible finite-Tor pro-etale complexes

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-def-sp-scalar-extension/_section.md (blueprint: sk-def-sp-scalar-extension).

The ambient functor and its normalized associator are the recorded construction.
The full-subcategory lift changes neither objects nor morphisms after inclusion.
Finite discrete condensed coefficients use the existing normalized section encoding;
unit equations fix the comparison of derived scalar extensions uniquely.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
private theorem spCtf_bounded_support
    {A : Type u} [CommRing A] [Finite A] (T : Scheme.{u})
    (K : proEtaleDerivedCategory T A)
    (h : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) → IsZero
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K)) :
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K)} := by
  obtain ⟨a, b, hab, hz⟩ := h
  apply Set.Finite.subset (Set.finite_Icc a b)
  intro i hi
  constructor <;> by_contra! hn
  · exact hi (hz i (.inl hn))
  · exact hi (hz i (.inr hn))

private theorem spCtf_bounded_of_support
    {A : Type u} [CommRing A] [Finite A] (T : Scheme.{u})
    (K : proEtaleDerivedCategory T A)
    (h : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K)}) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) → IsZero
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K) := by
  obtain ⟨a, ha⟩ := h.bddBelow
  obtain ⟨b, hb⟩ := h.bddAbove
  refine ⟨min a b, max a b, min_le_max, ?_⟩
  intro i hi
  rcases hi with hi | hi
  · by_contra hn
    exact (not_lt_of_ge (ha hn)) (lt_of_lt_of_le hi (min_le_left _ _))
  · by_contra hn
    exact (not_lt_of_ge (hb hn)) (lt_of_le_of_lt (le_max_right _ _) hi)

/-- Well-definedness of the restriction, without flatness of the coefficient map.
Source: blueprint, extension of coefficients and det-sp-scalar-extension-functor, clause 2
(blueprint: sk-def-sp-scalar-extension).
Proof: unpack finite Tor amplitude to an ordered interval [a,b]. Apply
scalarExtensionFunctor_preserves_constructible_tor to the finite cohomological support,
every intrinsic constructible cohomology sheaf and this interval. Boundedness is equivalent
to finite cohomological support for integer degrees. Its three conclusions give the
recorded spFiniteConstructibleTor conditions, with the same Tor interval. -/
theorem scalarExtensionCtf_preserved
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (f : A →+* B) (T : Scheme.{u}) (K : spFiniteConstructibleTorCategory T A) :
    spFiniteConstructibleTor T B ((scalarExtensionFunctor f T).obj K.obj) := by
  obtain ⟨hb, hc, ht⟩ := K.property
  obtain ⟨a, b, ht⟩ := ht
  obtain ⟨hb', hc', ht'⟩ := scalarExtensionFunctor_preserves_constructible_tor
    ℓ hA hB f T K.obj (spCtf_bounded_support T K.obj hb) hc a b ht
  exact ⟨spCtf_bounded_of_support T _ hb', hc', ⟨a, b, ht'⟩⟩

/-- K ↦ K tensor^L B and u ↦ u tensor^L id_B on the stated full subcategories.
The ambient functor is the derived change of rings with the B action on its tensor factor.
Source: blueprint, displayed formula and following sentence
(blueprint: sk-def-sp-scalar-extension). -/
def scalarExtensionCtfFunctor
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (f : A →+* B) (T : Scheme.{u}) :
    spFiniteConstructibleTorCategory T A ⥤ spFiniteConstructibleTorCategory T B :=
  (spFiniteConstructibleTor T B).lift
    ((spFiniteConstructibleTor T A).ι ⋙ scalarExtensionFunctor f T)
    (scalarExtensionCtf_preserved ℓ hA hB f T)

/-- The uniquely determined restriction of the canonical ambient associator.
Source: blueprint, associativity sentence; det-sp-scalar-extension-functor, clause 4
(blueprint: sk-def-sp-scalar-extension).
Proof: apply ObjectProperty.isoMk to each component of scalarExtensionFunctor_composition.
Naturality is its ambient naturality, since the subcategories are full and their inclusions
are faithful. Faithfulness also gives uniqueness from the displayed component equation. -/
theorem scalarExtensionCtfComposition_existsUnique
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (ℓ : ℕ) [Fact ℓ.Prime]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (hC : ∃ n : ℕ, ∀ x : C, (ℓ ^ n) • x = 0)
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    ∃! α : scalarExtensionCtfFunctor ℓ hA hB f T ⋙
        scalarExtensionCtfFunctor ℓ hB hC g T ≅
          scalarExtensionCtfFunctor ℓ hA hC (g.comp f) T,
      ∀ K : spFiniteConstructibleTorCategory T A,
        (α.hom.app K).hom = (scalarExtensionFunctor_composition f g T).hom.app K.obj := by
  let α : scalarExtensionCtfFunctor ℓ hA hB f T ⋙
      scalarExtensionCtfFunctor ℓ hB hC g T ≅
      scalarExtensionCtfFunctor ℓ hA hC (g.comp f) T :=
    NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _
        ((scalarExtensionFunctor_composition f g T).app K.obj)) (by
          intro K L u
          apply (spFiniteConstructibleTor T C).hom_ext
          exact (scalarExtensionFunctor_composition f g T).hom.naturality u.hom)
  refine ⟨α, ?_, ?_⟩
  · intro K
    rfl
  · intro β hβ
    apply Iso.ext
    ext K
    simpa [α] using hβ K

/-- The displayed natural comparison (K_B)_C ≅ K_C, inherited from K-flat balancing.
Source: blueprint, associativity sentence (blueprint: sk-def-sp-scalar-extension). -/
def scalarExtensionCtfComposition
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (ℓ : ℕ) [Fact ℓ.Prime]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (hC : ∃ n : ℕ, ∀ x : C, (ℓ ^ n) • x = 0)
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    scalarExtensionCtfFunctor ℓ hA hB f T ⋙ scalarExtensionCtfFunctor ℓ hB hC g T ≅
      scalarExtensionCtfFunctor ℓ hA hC (g.comp f) T :=
  (scalarExtensionCtfComposition_existsUnique ℓ hA hB hC f g T).exists.choose

/-- The finite discrete ring regarded as a commutative condensed ring, with sections C(S,A).
Source: blueprint, coefficient convention (blueprint: sk-def-sp-scalar-extension). -/
abbrev scalarExtensionDiscreteRing (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : CondensedRing.ScalarSixRing.{u} :=
  CommMon.mk (Profinite.continuousCoefficientRingObj A)

/-- The specified coefficient homomorphism acts by postcomposition on continuous sections.
Source: blueprint, coefficient convention (blueprint: sk-def-sp-scalar-extension). -/
def scalarExtensionDiscreteMap {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [DiscreteTopology A] (f : A →+* B) :
    scalarExtensionDiscreteRing A ⟶ scalarExtensionDiscreteRing B :=
  CommMon.homMk (@Mon.Hom.mk _ _ _ _ _
    (Profinite.continuousMapRingObjMapOfUniverse.{u, u} f continuous_of_discreteTopology)
    (Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
      (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
        f continuous_of_discreteTopology)))

/-- The normalized coefficient encoding intertwines scalar restriction identically on
underlying sections. HEq only accommodates the equality ordinary_functor in Encoding.
Source: blueprint, coefficient convention and internal/sectionwise equivalence
(blueprint: sk-def-sp-scalar-extension).
Proof: use the normalized constant-function ring maps of encoding_exists. Postcomposition
by f commutes with constant functions, so the square of reconstructed ring maps commutes.
Restriction along this square has the identical section groups and scalar actions. The
section-action equivalence leaves the underlying maps unchanged; identity maps therefore
give a natural isomorphism. Sectionwise faithfulness makes this isomorphism unique. -/
theorem scalarExtensionDiscreteRestriction_existsUnique
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [DiscreteTopology A] [DiscreteTopology B]
    (f : A →+* B) (T : Scheme.{u})
    (EA : FiniteDiscreteOrdinary.Encoding A T) (EB : FiniteDiscreteOrdinary.Encoding B T) :
    ∃! r : Mod.comap (coefficientMap
        (scalarExtensionDiscreteMap f).hom.hom T) ⋙ EA.ordinary.functor ≅
      EB.ordinary.functor ⋙ proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := T) f),
      ∀ (M : FiniteDiscreteOrdinary.Internal B T) (U : T.ProEtᵒᵖ)
        (x : ((Mod.comap (coefficientMap
          (scalarExtensionDiscreteMap f).hom.hom T) ⋙ EA.ordinary.functor).obj M).val.obj U),
        HEq ((r.hom.app M).val.app U x) x := by
  sorry

/-- Canonical restriction comparison, fixed by identity on every section.
Source: blueprint, coefficient convention (blueprint: sk-def-sp-scalar-extension). -/
def scalarExtensionDiscreteRestriction
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [DiscreteTopology A] [DiscreteTopology B]
    (f : A →+* B) (T : Scheme.{u})
    (EA : FiniteDiscreteOrdinary.Encoding A T) (EB : FiniteDiscreteOrdinary.Encoding B T) :
    Mod.comap (coefficientMap (scalarExtensionDiscreteMap f).hom.hom T) ⋙
        EA.ordinary.functor ≅ EB.ordinary.functor ⋙
          proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := T) f) :=
  (scalarExtensionDiscreteRestriction_existsUnique f T EA EB).exists.choose

/-- Termwise localization of the same normalized restriction comparison.
Source: blueprint, coefficient convention (blueprint: sk-def-sp-scalar-extension). -/
def scalarExtensionDiscreteRestrictionDerived
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [DiscreteTopology A] [DiscreteTopology B]
    (f : A →+* B) (T : Scheme.{u})
    (EA : FiniteDiscreteOrdinary.Encoding A T) (EB : FiniteDiscreteOrdinary.Encoding B T) :
    (Mod.comap (coefficientMap
      (scalarExtensionDiscreteMap f).hom.hom T)).mapDerivedCategory ⋙
        EA.ordinaryDerived.functor ≅ EB.ordinaryDerived.functor ⋙ scalarRestriction f T :=
  letI := EA.ordinaryAdditive
  letI := EB.ordinaryAdditive
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (scalarExtensionDiscreteRestriction f T EA EB) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Expose the adjunction already used to define scalarSixChange.
Source: blueprint, coefficient convention (blueprint: sk-def-sp-scalar-extension). -/
def scalarExtensionCondensedAdjunction
    {Λ Λ' : CondensedRing.ScalarSixRing.{u}} (a : Λ ⟶ Λ') (T : Scheme.{u}) :
    CondensedRing.scalarSixChange a T ⊣
      (Mod.comap (coefficientMap a.hom.hom T)).mapDerivedCategory :=
  @Mod.derivedExtendMapDerivedCategoryAdjunction
    (Sheaf (ProEt.topology T) Ab.{u + 1}) _ _ (sheafMonoidalCategory Ab.{u + 1} T)
    _ _ _ _ _ (condensedRingObj Λ.X T) (condensedRingObj Λ'.X T) _ _
    (isCommMonObj_condensedRingObj Λ.X T) (isCommMonObj_condensedRingObj Λ'.X T)
    (coefficientMap a.hom.hom T) _

/-- The published internal derived scalar adjunction for discrete coefficients.
Source: blueprint, coefficient convention (blueprint: sk-def-sp-scalar-extension). -/
def scalarExtensionDiscreteAdjunction
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [DiscreteTopology A] (f : A →+* B) (T : Scheme.{u}) :
    CondensedRing.scalarSixChange (scalarExtensionDiscreteMap f) T ⊣
      (Mod.comap (coefficientMap (scalarExtensionDiscreteMap f).hom.hom T)).mapDerivedCategory :=
  scalarExtensionCondensedAdjunction (scalarExtensionDiscreteMap f) T

/-- The unique comparison of the two derived coefficient tensors, normalized by the
units of their actual extension/restriction adjunctions.
Source: blueprint, final compatibility paragraph (blueprint: sk-def-sp-scalar-extension).
Proof: the sectionwise restriction comparison is exact and extends termwise. Transpose
it under the two derived scalar adjunctions and the two coefficient equivalences. The
result is invertible by uniqueness of left adjoints. The displayed unit equation is the
mate equation and determines the comparison uniquely. On K-flat representatives it is
identity on balanced pure tensors, by internal_section_scalar_adjunction; thus it keeps
the coefficient actions as well as the underlying abelian sheaves. -/
theorem scalarExtensionDiscreteComparison_existsUnique
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [DiscreteTopology A] [DiscreteTopology B]
    (f : A →+* B) (T : Scheme.{u})
    (EA : FiniteDiscreteOrdinary.Encoding A T) (EB : FiniteDiscreteOrdinary.Encoding B T) :
    ∃! e : CondensedRing.scalarSixChange (scalarExtensionDiscreteMap f) T ⋙
        EB.ordinaryDerived.functor ≅ EA.ordinaryDerived.functor ⋙ scalarExtensionFunctor f T,
      ∀ K : DerivedCategory (FiniteDiscreteOrdinary.Internal A T),
        EA.ordinaryDerived.functor.map
          ((scalarExtensionDiscreteAdjunction f T).unit.app K) ≫
          (scalarExtensionDiscreteRestrictionDerived f T EA EB).hom.app
            ((CondensedRing.scalarSixChange (scalarExtensionDiscreteMap f) T).obj K) ≫
          (scalarRestriction f T).map (e.hom.app K) =
        (proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := T) f)).unit.app
            (EA.ordinaryDerived.functor.obj K) := by
  sorry

/-- The derived coefficient comparison selected by its unique adjunction normalization.
Source: blueprint, coefficient convention (blueprint: sk-def-sp-scalar-extension). -/
def scalarExtensionDiscreteComparison
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [DiscreteTopology A] [DiscreteTopology B]
    (f : A →+* B) (T : Scheme.{u})
    (EA : FiniteDiscreteOrdinary.Encoding A T) (EB : FiniteDiscreteOrdinary.Encoding B T) :
    CondensedRing.scalarSixChange (scalarExtensionDiscreteMap f) T ⋙
        EB.ordinaryDerived.functor ≅ EA.ordinaryDerived.functor ⋙ scalarExtensionFunctor f T :=
  (scalarExtensionDiscreteComparison_existsUnique f T EA EB).exists.choose

/-- Postcomposition of continuous functions is functorial in the finite coefficient ring.
Source: blueprint, coefficient convention (blueprint: sk-def-sp-scalar-extension).
Proof: on S every section is a continuous function h, and both composites are g ∘ f ∘ h.
The sheaf maps and their ring-object structures therefore agree, including on empty S. -/
theorem scalarExtensionDiscreteMap_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
    [DiscreteTopology A] [DiscreteTopology B] (f : A →+* B) (g : B →+* C) :
    scalarExtensionDiscreteMap f ≫ scalarExtensionDiscreteMap g =
      scalarExtensionDiscreteMap (g.comp f) := by
  ext S x
  rfl

/-- The existing condensed associator, with its composite ring map identified explicitly.
Source: blueprint, final compatibility paragraph (blueprint: sk-def-sp-scalar-extension). -/
def scalarExtensionDiscreteTower
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
    [DiscreteTopology A] [DiscreteTopology B]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u}) :
    CondensedRing.scalarSixChange (scalarExtensionDiscreteMap f) T ⋙
        CondensedRing.scalarSixChange (scalarExtensionDiscreteMap g) T ≅
      CondensedRing.scalarSixChange (scalarExtensionDiscreteMap (g.comp f)) T :=
  CondensedRing.scalarSixTower (scalarExtensionDiscreteMap f) (scalarExtensionDiscreteMap g) T ≪≫
    eqToIso (congrArg (fun a ↦ CondensedRing.scalarSixChange a T)
      (scalarExtensionDiscreteMap_comp f g))

/-- Under the canonical coefficient identifications the ambient associator is precisely
clause 3 of det-prop-scalar-six-pullback, hence so is its full-subcategory restriction.
Source: blueprint, final compatibility paragraph (blueprint: sk-def-sp-scalar-extension).
Proof: use the finite clopen fibre presentation and strong monoidal point inverse image
in the normalized encodings. The section-module equivalence preserves balanced tensors,
acyclicity and K-flat representatives. Both paths below are therefore computed by
c tensor (b tensor x) ↦ c*g(b) tensor x. Equality on these representatives descends by the
universal derived counits to every derived object. The unique unit normalizations above
exclude any scalar twist, and scalarExtensionCtfComposition uses this very ambient map. -/
theorem scalarExtensionDiscreteComparison_tower
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
    [DiscreteTopology A] [DiscreteTopology B] [DiscreteTopology C]
    (f : A →+* B) (g : B →+* C) (T : Scheme.{u})
    (EA : FiniteDiscreteOrdinary.Encoding A T) (EB : FiniteDiscreteOrdinary.Encoding B T)
    (EC : FiniteDiscreteOrdinary.Encoding C T)
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A T)) :
    EC.ordinaryDerived.functor.map ((scalarExtensionDiscreteTower f g T).hom.app K) ≫
        (scalarExtensionDiscreteComparison (g.comp f) T EA EC).hom.app K =
      (scalarExtensionDiscreteComparison g T EB EC).hom.app
          ((CondensedRing.scalarSixChange (scalarExtensionDiscreteMap f) T).obj K) ≫
        (scalarExtensionFunctor g T).map
          ((scalarExtensionDiscreteComparison f T EA EB).hom.app K) ≫
        (scalarExtensionFunctor_composition f g T).hom.app
          (EA.ordinaryDerived.functor.obj K) := by
  sorry

end AlgebraicGeometry.ProEtale
