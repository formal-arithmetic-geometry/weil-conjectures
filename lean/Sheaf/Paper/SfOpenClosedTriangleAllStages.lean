/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Sheaf.Paper.SfOpenClosedTriangleData
import Mathlib.Algebra.CharP.CharAndCard
import Sheaf.Paper.FiniteKernelConstructibleLocalization
import Sheaf.Paper.ProEtaleFiniteLocalConstancyPullback
import all Sheaf.Paper.OpenFiniteConstructibilityInterval
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.Paper.SfIntegralKernelRealization
import Sheaf.Paper.SfNormalizedRecollementTriangles
import Sheaf.Paper.SfNormalizedCommonStageDescent
import Sheaf.Paper.SfNormalizedRationalWeilSquares
import Sheaf.Paper.SfNormalizedCommonStageWeilSquares
import Sheaf.Paper.AutomorphismConstructibleStageEquivalence

/-!
# The canonical open-closed triangle at all coefficient stages

Source: Weil blueprint, sec-smooth-purity, prop-sf-open-closed-triangle-all-stages,
order 1851 (current main: order 2195)
(blueprint: prop-sf-open-closed-triangle-all-stages).

The integral presentation uses the actual closed inverse-image/direct-image unit.
Its kernel is the open term, with its kernel inclusion as counit. This fixes the
maps before passage to complexes, completion, scalar localization, or common stages.

## Main statements

* `sfOpenClosedTriangle_finite`: canonical finite-coefficient triangle and uniqueness.
* `sfOpenClosedTriangle_integral_rational`: normalized integral and rational triangles.
* `sfOpenClosedTriangle_qbar`: the common-stage triangle.
* `sfOpenClosedTriangle_rational_weil`, `sfOpenClosedTriangle_qbar_weil`: all three
  arrows are equivariant for the recorded fixed-pair Weil structures.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u v w w₁
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem sfRecollementConclusion_of_triangle_orthogonality
    {C : Type w} [Category.{w₁} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : SfRecollementPresentation C)
    (ht : ∀ K, ∃ δ, Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C)
    (ho : ∀ (K L : C) (n : ℤ),
      Subsingleton ((P.openTerm.obj K)⟦n⟧ ⟶ P.closedTerm.obj L)) :
    SfRecollementConclusion P := by
  refine ⟨?_, fun K ↦ ho K K, ?_⟩
  · intro K
    obtain ⟨δ, hδ⟩ := ht K
    refine ⟨δ, hδ, fun δ' hδ' ↦ ?_⟩
    exact (triangle_morphism_extension _ _ hδ hδ (𝟙 K)).2.2 (ho K K 1) δ' hδ'
  · intro K L f δ δ' hδ hδ'
    obtain ⟨τ, _, _, _, hc⟩ :=
      ((triangle_morphism_extension _ _ hδ hδ' f).2.1 (ho K L 1)).2.2
        (P.openTerm.map f) (P.closedTerm.map f)
        (P.counit.naturality f) (P.unit.naturality f).symm
    exact hc.symm

private theorem sfConstantDirectImageEq (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingPushforward A f = proEtaleConstantModuleDirectImage f A := by
  unfold proEtaleConstantRingPushforward proEtaleRingModuleDirectImage
    proEtaleConstantModuleDirectImage proEtaleConstantRingComparison
  rw [proEtaleConstantModulePullback_ring_direct]

private theorem sfFiniteConstructibleIso
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    {K L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)}
    (e : K ≅ L) (h : intrinsicFiniteTorsionConstructible l E n hn X L) :
    intrinsicFiniteTorsionConstructible l E n hn X K := by
  let A := Padic.coefficientExtensionRing l E n
  have : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let H := DerivedCategory.homologyFunctor (proEtaleRingModules X (proEtaleConstantRing X A))
  constructor
  · apply h.1.subset
    intro r hr hz
    exact hr (hz.of_iso ((H r).mapIso e))
  · intro r
    have hr := h.2 r
    rw [proEtaleModuleRestriction_constructible_iff] at hr ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction X A).mapIso ((H r).mapIso e)).symm hr

/-- At positive finite coefficients the specified maps have unique distinguished
completion; the vertices remain constructible, Hom vanishing includes every integer
shift, and the triangle is natural. Source: blueprint proof steps 1--2, 8--9; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: finite type makes X Noetherian and its open complement quasi-compact. The
existing finite support-kernel localization theorem supplies the ambient triangle with
these very counit and unit maps, and constructibility of restriction and closed image.
The canonical pullback-coordinate comparison transports the restriction assertions to
intrinsic pullback. Exact open extension preserves constructibility and cohomological
support. Disjoint support kills closed restriction of open extension, degreewise and
then on the derived category. The closed adjunction gives Hom(j!N[m],i*M)=0 for
independent N,M and all integer m. The triangle-morphism extension theorem gives
uniqueness of the third map and naturality for every map of middle terms. -/
theorem sfOpenClosedTriangle_finite
    (k : Type u) [Field k] (_hk : IsUnit (l : k))
    {Z U X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ)
    (n : ℕ) (hn : 1 ≤ n) :
    SfRecollementConclusionOn
      (sfFiniteRecollementAt l E i j n hn)
      (intrinsicFiniteTorsionConstructible l E n hn X) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let A := Padic.coefficientExtensionRing l E (m + 1)
  have : Finite A := Padic.finite_coefficientExtensionRing l E (m + 1) hn
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U :=
    j.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := inferInstance
  obtain ⟨hcol, a0, _, _, _, _, _, hrestr, hpush, _, htri, _⟩ :=
    finiteKernelConstructibleLocalization l E m k _hk (X ↘ Spec (.of k)) i j _hij
  change PreservesFiniteColimits (proEtaleConstantRingPushforward A i) at hcol
  rw [sfConstantDirectImageEq A i] at hcol
  have : PreservesFiniteColimits (proEtaleConstantModuleDirectImage i A) := hcol
  have : PreservesFiniteLimits (proEtaleConstantModuleDirectImage i A) := by
    rw [← sfConstantDirectImageEq A i]
    let := (proEtaleConstantRingAdjunction A i).rightAdjoint_preservesLimits
    infer_instance
  change ∀ K, intrinsicFiniteTorsionConstructible l E (m + 1) _ X K →
    intrinsicFiniteTorsionConstructible l E (m + 1) _ Z
      ((proEtaleConstantRingDerivedPullback A i).obj K) ∧
    intrinsicFiniteTorsionConstructible l E (m + 1) _ U
      ((proEtaleConstantRingDerivedPullback A j).obj K) at hrestr
  have : PreservesFiniteLimits (proEtaleConstantRingPushforward A i) :=
    let := (proEtaleConstantRingAdjunction A i).rightAdjoint_preservesLimits
    inferInstance
  have hcol' : PreservesFiniteColimits (proEtaleConstantRingPushforward A i) := by
    rw [sfConstantDirectImageEq A i]
    exact hcol
  have : PreservesFiniteColimits (proEtaleConstantRingPushforward A i) := hcol'
  change ∀ K, intrinsicFiniteTorsionConstructible l E (m + 1) _ Z K →
    intrinsicFiniteTorsionConstructible l E (m + 1) _ X
      ((proEtaleConstantRingPushforward A i).mapDerivedCategory.obj K) at hpush
  have hpull (K) (hK : intrinsicFiniteTorsionConstructible l E (m + 1) hn X K) :
      intrinsicFiniteTorsionConstructible l E (m + 1) hn Z
        ((sfIntrinsicDerivedPullback A i).obj K) ∧
      intrinsicFiniteTorsionConstructible l E (m + 1) hn U
        ((sfIntrinsicDerivedPullback A j).obj K) :=
    ⟨sfFiniteConstructibleIso l E _ hn Z
      ((openSquareDerivedPullbackModel A i).app K).symm (hrestr K hK).1,
      sfFiniteConstructibleIso l E _ hn U
        ((openSquareDerivedPullbackModel A j).app K).symm (hrestr K hK).2⟩
  have hopen (N) (hN : intrinsicFiniteTorsionConstructible l E (m + 1) hn U N) :
      intrinsicFiniteTorsionConstructible l E (m + 1) hn X
        ((sfIntrinsicDerivedOpen A j).obj N) := by
    let F := sfIntrinsicExtensionByZero j A
    constructor
    · apply hN.1.subset
      intro r hr hz
      exact hr (F.isZero_homologyFunctor_mapDerivedCategory_obj (X := N) hz)
    · intro r
      rw [proEtaleModuleRestriction_constructible_iff]
      exact ProEtale.isConstructible_of_iso
        ((proEtaleModuleRestriction X A).mapIso
          ((F.mapDerivedCategoryHomologyFunctorIso r).app N))
        ((proEtaleModuleRestriction_constructible_iff X A _).mp
          (extension_constructible j A _ (hN.2 r)))
  let P := sfFiniteRecollementAt l E i j (m + 1) hn
  have horth (K L : proEtaleDerivedCategory X A) (r : ℤ) :
      Subsingleton ((P.openTerm.obj K)⟦r⟧ ⟶ P.closedTerm.obj L) := by
    have hz (N : proEtaleDerivedCategory U A) :
        IsZero ((sfIntrinsicDerivedPullback A i).obj ((sfIntrinsicDerivedOpen A j).obj N)) := by
      apply IsZero.of_iso _
        (((sfIntrinsicExtensionByZero j A).mapDerivedCategoryCompIso
          (sfIntrinsicPullback A i)).app N).symm
      apply Functor.isZero_mapDerivedCategory_obj
      intro t
      exact (AlgebraicGeometry.Scheme.pullback_extension_isZero A j i (by
        rw [_hij]
        exact Set.compl_inter_self _) _).of_iso ((openSquarePullbackModel A i).app _).symm
    have hz' : IsZero ((sfIntrinsicDerivedPullback A i).obj ((P.openTerm.obj K)⟦r⟧)) :=
      ((shiftFunctor _ r).map_isZero (hz _)).of_iso
        (((sfIntrinsicDerivedPullback A i).commShiftIso r).app _)
    have : Subsingleton ((sfIntrinsicDerivedPullback A i).obj
        ((P.openTerm.obj K)⟦r⟧) ⟶ (sfIntrinsicDerivedPullback A i).obj L) :=
      ⟨fun _ _ ↦ hz'.eq_of_src _ _⟩
    exact ((finiteRecollementDerivedAdjunction i A).homEquiv _ _).symm.subsingleton
  have hex (K : proEtaleDerivedCategory X A) :
      ∃ δ, Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang _ := htri K
  constructor
  · intro K hK
    obtain ⟨δ, hδ⟩ := hex K
    refine ⟨hopen _ (hpull K hK).2, ?_, ⟨δ, hδ, ?_⟩, horth K K⟩
    · exact sfFiniteConstructibleIso l E _ hn X
        ((proEtaleConstantModuleDirectImage i A).rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
          (Functor.mapDerivedCategoryNatIso (eqToIso (sfConstantDirectImageEq A i))).symm.app _)
        (hpush _ (hpull K hK).1)
    · intro δ' hδ'
      exact (triangle_morphism_extension _ _ hδ hδ (𝟙 K)).2.2
        (horth K K 1) δ' hδ'
  · intro K L _ _ f δ δ' hδ hδ'
    obtain ⟨τ, _, _, _, hc⟩ :=
      ((triangle_morphism_extension _ _ hδ hδ' f).2.1 (horth K L 1)).2.2
        (P.openTerm.map f) (P.closedTerm.map f)
        (P.counit.naturality f) (P.unit.naturality f).symm
    exact hc.symm

private def scalarLocalizationMapIso
    (R : Type*) [CommRing R] (C : Type*) [Category C] [Preadditive C] [Linear R C]
    (p : R) (T : C ⥤ C) [T.Additive] [T.Linear R] :
    ScalarLocalization.localization R C p ⋙ ScalarLocalization.map R C p T ≅
      T ⋙ ScalarLocalization.localization R C p :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro K L f
    simp [ScalarLocalization.localization, ScalarLocalization.map,
      ScalarLocalization.mapHom])

private def scalarRecollementPresentation
    (R : Type*) [CommRing R] (C : Type*) [Category C] [Preadditive C] [Linear R C]
    (p : R) (P : SfRecollementPresentation C)
    [P.openTerm.Additive] [P.closedTerm.Additive]
    [P.openTerm.Linear R] [P.closedTerm.Linear R] :
    SfRecollementPresentation (ScalarLocalization R C p) where
  openTerm := ScalarLocalization.map R C p P.openTerm
  closedTerm := ScalarLocalization.map R C p P.closedTerm
  counit :=
    { app := fun K ↦ (ScalarLocalization.localization R C p).map (P.counit.app K.obj)
      naturality := by
        intro K L f
        dsimp only [Functor.id_map]
        induction f using TensorProduct.induction_on with
        | zero => simp
        | tmul a f =>
          change ScalarLocalization.composition R C p _ _ _ (1 ⊗ₜ _)
              (ScalarLocalization.mapHom R C p P.openTerm _ _ (a ⊗ₜ f)) =
            ScalarLocalization.composition R C p _ _ _ (a ⊗ₜ f) (1 ⊗ₜ _)
          simp only [ScalarLocalization.mapHom, LinearMap.baseChange_tmul,
            ScalarLocalization.composition_tmul, one_mul, mul_one]
          exact congrArg (fun z ↦ a ⊗ₜ[R] z)
            (P.counit.naturality f)
        | add f g hf hg =>
          change ScalarLocalization.composition R C p _ _ _ (1 ⊗ₜ _)
              (ScalarLocalization.mapHom R C p P.openTerm _ _ (f + g)) =
            ScalarLocalization.composition R C p _ _ _ (f + g) (1 ⊗ₜ _)
          simp only [map_add, LinearMap.add_apply]
          exact congrArg₂ (· + ·) hf hg }
  unit :=
    { app := fun K ↦ (ScalarLocalization.localization R C p).map (P.unit.app K.obj)
      naturality := by
        intro K L f
        dsimp only [Functor.id_map]
        induction f using TensorProduct.induction_on with
        | zero => simp
        | tmul a f =>
          change ScalarLocalization.composition R C p _ _ _ (1 ⊗ₜ _)
              (a ⊗ₜ f) =
            ScalarLocalization.composition R C p _ _ _
              (ScalarLocalization.mapHom R C p P.closedTerm _ _ (a ⊗ₜ f)) (1 ⊗ₜ _)
          simp only [ScalarLocalization.mapHom, LinearMap.baseChange_tmul,
            ScalarLocalization.composition_tmul, one_mul, mul_one]
          exact congrArg (fun z ↦ a ⊗ₜ[R] z)
            (P.unit.naturality f)
        | add f g hf hg =>
          change ScalarLocalization.composition R C p _ _ _ (1 ⊗ₜ _) (f + g) =
            ScalarLocalization.composition R C p _ _ _
              (ScalarLocalization.mapHom R C p P.closedTerm _ _ (f + g)) (1 ⊗ₜ _)
          simp only [map_add, LinearMap.add_apply]
          exact congrArg₂ (· + ·) hf hg }

private def sfRecollementRationalPresentation (X : Scheme.{u})
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X))
    [P.openTerm.Additive] [P.closedTerm.Additive]
    [P.openTerm.Linear (Padic.coefficientExtensionIntegers l E)]
    [P.closedTerm.Linear (Padic.coefficientExtensionIntegers l E)] :
    SfRecollementPresentation (sfRationalConstructibleCategory l E X) :=
  scalarRecollementPresentation (Padic.coefficientExtensionIntegers l E)
    (sfIntegralConstructibleCategory l E X) (Padic.coefficientExtensionUniformizer l E) P

private theorem scalarRecollementPresentation_normalization
    (R : Type*) [CommRing R] (C : Type*) [Category C] [Preadditive C] [Linear R C]
    (p : R) (P : SfRecollementPresentation C)
    [P.openTerm.Additive] [P.closedTerm.Additive]
    [P.openTerm.Linear R] [P.closedTerm.Linear R] :
    let Q := ScalarLocalization.localization R C p
    let T := scalarRecollementPresentation R C p P
    (∀ K, T.openTerm.obj K = ⟨P.openTerm.obj K.obj⟩ ∧
      T.closedTerm.obj K = ⟨P.closedTerm.obj K.obj⟩) ∧
    ∃ (a : Q ⋙ T.openTerm ≅ P.openTerm ⋙ Q)
      (c : Q ⋙ T.closedTerm ≅ P.closedTerm ⋙ Q),
      (∀ K, a.hom.app K ≫ Q.map (P.counit.app K) = T.counit.app (Q.obj K)) ∧
      ∀ K, T.unit.app (Q.obj K) ≫ c.hom.app K = Q.map (P.unit.app K) := by
  refine ⟨fun _ ↦ ⟨rfl, rfl⟩, scalarLocalizationMapIso R C p P.openTerm,
    scalarLocalizationMapIso R C p P.closedTerm, ?_, ?_⟩
  · exact fun _ ↦ Category.id_comp _
  · exact fun _ ↦ Category.comp_id _

private theorem sfRecollementRationalPresentation_normalization (X : Scheme.{u})
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X))
    [P.openTerm.Additive] [P.closedTerm.Additive]
    [P.openTerm.Linear (Padic.coefficientExtensionIntegers l E)]
    [P.closedTerm.Linear (Padic.coefficientExtensionIntegers l E)] :
    SfRationalRecollementNormalization l E X P
      (sfRecollementRationalPresentation l E X P) := by
  dsimp only [SfRationalRecollementNormalization, sfRecollementRationalPresentation,
    sfRationalConstructibleLocalization]
  exact scalarRecollementPresentation_normalization
    (Padic.coefficientExtensionIntegers l E) (sfIntegralConstructibleCategory l E X)
    (Padic.coefficientExtensionUniformizer l E) P

private theorem sfRecollementRationalPresentation_conclusion (X : Scheme.{u})
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X))
    [P.openTerm.Additive] [P.closedTerm.Additive]
    [P.openTerm.Linear (Padic.coefficientExtensionIntegers l E)]
    [P.closedTerm.Linear (Padic.coefficientExtensionIntegers l E)]
    (ht : ∀ K, ∃ δ, Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang _)
    (ho : ∀ (K L : sfIntegralConstructibleCategory l E X) (n : ℤ),
      Subsingleton ((P.openTerm.obj K)⟦n⟧ ⟶ P.closedTerm.obj L)) :
    SfRecollementConclusion (sfRecollementRationalPresentation l E X P) := by
  let Q := sfRationalConstructibleLocalization l E X
  apply sfRecollementConclusion_of_triangle_orthogonality
  · intro K
    obtain ⟨δ, hδ⟩ := ht K.obj
    refine ⟨Q.map δ ≫ (Q.commShiftIso (1 : ℤ)).hom.app (P.openTerm.obj K.obj), ?_⟩
    exact Q.map_distinguished _ hδ
  · intro K L n
    have := ho K.obj L.obj n
    have hQ : Subsingleton (Q.obj ((P.openTerm.obj K.obj)⟦n⟧) ⟶
        Q.obj (P.closedTerm.obj L.obj)) := by
      change Subsingleton (Localization.Away (Padic.coefficientExtensionUniformizer l E) ⊗[
        Padic.coefficientExtensionIntegers l E]
          ((P.openTerm.obj K.obj)⟦n⟧ ⟶ P.closedTerm.obj L.obj))
      infer_instance
    let e := Iso.homCongr ((Q.commShiftIso n).symm.app (P.openTerm.obj K.obj))
      (Iso.refl (Q.obj (P.closedTerm.obj L.obj)))
    exact ⟨fun f g ↦ e.injective (@Subsingleton.elim _ hQ (e f) (e g))⟩

/-- Integral and rational localization triangles, with their actual operation vertices
and specified maps. The Noetherian and induced finite-type hypotheses here are the
properties inherited by the three schemes in the statement.
Source: blueprint proof steps 3--10
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: identify immersion inverse images of completed coefficients with the actual
coefficient sheaves. Exact immersion restriction preserves countable products, hence
Roos triangles, and is the completed pullback. Open extension is the kernel of the
map j* to i*i*j*, so preserves products too. The slice tensor identity on K-flat
complexes identifies its reductions with finite extension, compatibly with transitions.
It is therefore complete with constructible reductions in one common interval, and
is the specified compact-support value. Closed exact direct image commutes with the
reduction tower and has the specified finite reductions. The termwise ringed sheaf
sequence gives the integral triangle in the full triangulated subcategory. The open
adjunction and disjoint support give cross-object vanishing. TR3 and Hom exactness
prove uniqueness and naturality as at finite coefficients. Localize the integral
linear functors and maps: localization is exact, and Hom groups tensor with E, so
vanishing persists. Apply the same TR3 argument to arbitrary rational morphisms. -/
theorem sfOpenClosedTriangle_integral_rational
    (k : Type u) [Field k] (hk : IsUnit (l : k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ) :
    ∃ (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X))
      (Q : SfRecollementPresentation (sfRationalConstructibleCategory l E X)),
      SfIntegralRecollementNormalization l E i (sfRecollementNoetherian k X) P ∧
      SfIntegralRecollementVertices l E k hk i j P ∧
      SfRecollementConclusion P ∧
      SfRationalRecollementNormalization l E X P Q ∧ SfRecollementConclusion Q := by
  classical
  have : IsNoetherian X := sfRecollementNoetherian k X
  let S := sfIntegralConstructible l E X
  let A := sfIntegralKernelAmbient l E i
  obtain ⟨ho, hc, hv, hla, hlb⟩ :=
    sfIntegralKernel_operation_realization l E k hk i j _hij
  let P := sfRecollementRestriction S A ho hc
  have : P.openTerm.Additive := inferInstance
  have : P.closedTerm.Additive := inferInstance
  have : P.openTerm.Linear (Padic.coefficientExtensionIntegers l E) := hla
  have : P.closedTerm.Linear (Padic.coefficientExtensionIntegers l E) := hlb
  let Q := sfRecollementRationalPresentation l E X P
  have ht (K) : ∃ δ, Triangle.mk (A.counit.app K) (A.unit.app K) δ ∈ distTriang _ := by
    have : (kernel (sfRecollementModuleUnit l E i)).Additive :=
      sfRecollementModuleOpen_additive l E i
    have : PreservesFiniteLimits (kernel (sfRecollementModuleUnit l E i)) :=
      sfRecollementModuleOpen_limits l E i
    have : PreservesFiniteColimits (kernel (sfRecollementModuleUnit l E i)) :=
      sfRecollementModuleOpen_colimits l E i
    exact sfExactLocalizationPresentation_distinguished _ _ _ _
      (kernel.condition (sfRecollementModuleUnit l E i))
      (sfRecollementModule_shortExact l E i) K
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let T := completedIntegralCommRingSheafUnrestricted l E Z
  let c := asIso (sfRecollementCoefficientMap l E i)
  let L := proEtaleRingModulePullback i R T c
  let I := proEtaleRingModuleDirectImage i R T c
  have : PreservesFiniteLimits I := (sfRecollementModuleDirect_exact l E i).1
  have : PreservesFiniteColimits I := (sfRecollementModuleDirect_exact l E i).2
  have : ∀ N, IsIso ((sfRecollementModuleAdjunction l E i).counit.app N) :=
    (sfRecollementModule_closed_adjunction l E i).2
  have : IsIso (sfRecollementModuleAdjunction l E i).counit :=
    NatIso.isIso_of_isIso_app _
  have horth (K M) (n : ℤ) :
      Subsingleton ((A.openTerm.obj K)⟦n⟧ ⟶ A.closedTerm.obj M) := by
    have : (kernel (sfRecollementModuleAdjunction l E i).unit).Additive :=
      sfRecollementModuleOpen_additive l E i
    have : PreservesFiniteLimits (kernel (sfRecollementModuleAdjunction l E i).unit) :=
      sfRecollementModuleOpen_limits l E i
    have : PreservesFiniteColimits (kernel (sfRecollementModuleAdjunction l E i).unit) :=
      sfRecollementModuleOpen_colimits l E i
    exact sfExactLocalizationKernel_orthogonality L I
      (sfRecollementModuleAdjunction l E i) K M n
  have htP := sfRecollementRestriction_distinguished S A ho hc ht
  have hoP := sfRecollementRestriction_orthogonality S A ho hc horth
  refine ⟨P, Q, ?_, hv,
    sfRecollementConclusion_of_triangle_orthogonality P htP hoP,
    sfRecollementRationalPresentation_normalization l E X P,
    sfRecollementRationalPresentation_conclusion l E X P htP hoP⟩
  refine ⟨Iso.refl _, Iso.refl _, ?_⟩
  intro B hB
  constructor
  · change 𝟙 _ ≫ A.counit.app (DerivedCategory.Q.obj B) = _
    rw [Category.id_comp]
    exact sfExactLocalizationPresentation_counit
      (sfRecollementModuleOpen l E i) (sfRecollementModuleClosed l E i)
      (sfRecollementModuleCounit l E i) (sfRecollementModuleUnit l E i) B
  · change A.unit.app (DerivedCategory.Q.obj B) ≫ 𝟙 _ ≫
      (sfRecollementModuleClosed l E i).mapDerivedCategoryFactors.hom.app B = _
    rw [Category.id_comp]
    exact sfExactLocalizationPresentation_unit
      (sfRecollementModuleOpen l E i) (sfRecollementModuleClosed l E i)
      (sfRecollementModuleCounit l E i) (sfRecollementModuleUnit l E i) B


variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

set_option linter.unusedVariables false in
/-- The algebraically closed coefficient localization triangle, with all finite-stage
operations retained through the recorded common-stage inclusions.
Source: blueprint proof step 11
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: apply the integral/rational construction at every finite coefficient field.
Tensor balancing and scalar-extension compatibility identify the counit and unit
across each field inclusion. Descend the exact functors and these transformations.
An object and each finite diagram of morphisms have a common coefficient stage.
Exactness of the stage inclusions carries the rational triangle to the common-stage
category. The Hom groups are filtered colimits of the vanishing stage groups.
TR3 and Hom exactness prove uniqueness and naturality for every common-stage map. -/
theorem sfOpenClosedTriangle_qbar
    (k : Type u) [Field k] (hk : IsUnit (l : k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ) :
    ∃ (P : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
        SfRecollementPresentation (sfIntegralConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X))
      (Q : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
        SfRecollementPresentation (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L)),
      (∀ L, SfIntegralRecollementNormalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) i
          (sfRecollementNoetherian k X) (P L) ∧
        SfIntegralRecollementVertices l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) k hk i j (P L) ∧
        SfRecollementConclusion (shiftAdditive := fun n => inferInstance) (P L) ∧
        SfRationalRecollementNormalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X (P L) (Q L) ∧
        SfRecollementConclusion (Q L)) ∧
      ∃ R : SfRecollementPresentation (generalAlgebraicallyClosedConstructibleCategory l Ω X),
        SfCommonStageRecollementNormalization l Ω X Q R ∧ SfRecollementConclusion R := by
  classical
  have hstage (L : AlgebraicallyClosedCoefficients.Index l Ω) :=
    sfOpenClosedTriangle_integral_rational l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) k hk i j _hij
  choose P Q hPQ using hstage
  obtain ⟨R, hR, ht, ho⟩ := sfNormalizedRecollement_commonStage_descent l Ω k hk i j
    _hij P Q (fun L ↦ ⟨(hPQ L).1, (hPQ L).2.2.2.1⟩)
  exact ⟨P, Q, hPQ, R, hR, sfRecollementConclusion_of_triangle_orthogonality R ht ho⟩

private theorem sfRecollement_triangle_transport
    {B : Type*} [Category B] [Preadditive B] [HasZeroObject B]
    [HasShift B ℤ] [shiftAddB : ∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : SfRecollementPresentation B) (R : SfRecollementPresentation C)
    (F : B ⥤ C) [F.CommShift ℤ] [F.IsTriangulated] (N : B)
    (a : R.openTerm.obj (F.obj N) ≅ F.obj (P.openTerm.obj N))
    (c : R.closedTerm.obj (F.obj N) ≅ F.obj (P.closedTerm.obj N))
    (ha : R.counit.app (F.obj N) = a.hom ≫ F.map (P.counit.app N))
    (hc : R.unit.app (F.obj N) ≫ c.hom = F.map (P.unit.app N))
    (ht : ∃ δ, Triangle.mk (P.counit.app N) (P.unit.app N) δ ∈ distTriang B) :
    ∃ δ, Triangle.mk (R.counit.app (F.obj N)) (R.unit.app (F.obj N)) δ ∈ distTriang C := by
  obtain ⟨δ, hδ⟩ := ht
  let δ' := c.hom ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app _ ≫
    (shiftFunctor C (1 : ℤ)).map a.inv
  refine ⟨δ', isomorphic_distinguished _ (F.map_distinguished _ hδ) _
    (Triangle.isoMk _ _ a (Iso.refl _) c ?_ ?_ ?_)⟩
  · change R.counit.app (F.obj N) ≫ 𝟙 _ = a.hom ≫ F.map (P.counit.app N)
    simpa only [Category.comp_id] using ha
  · change R.unit.app (F.obj N) ≫ c.hom = 𝟙 _ ≫ F.map (P.unit.app N)
    simpa only [Category.id_comp] using hc
  · change δ' ≫ (shiftFunctor C (1 : ℤ)).map a.hom =
      c.hom ≫ (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app _)
    simp only [δ', Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    erw [(shiftFunctor C (1 : ℤ)).map_id]
    exact congrArg (fun f ↦ c.hom ≫ F.map δ ≫ f)
      (Category.comp_id ((F.commShiftIso (1 : ℤ)).hom.app (P.openTerm.obj N)))

private theorem sfRecollementWeilEquivariant_of_squares
    {C : Type w} [Category.{w₁} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : SfRecollementPresentation C) (G : C ⥤ C) (s : G.CommShift ℤ)
    (hex : SfRecollementFrobeniusExact G s)
    (ht : ∀ K, ∃ δ, Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C)
    (ho : ∀ K, Subsingleton ((P.openTerm.obj K)⟦(1 : ℤ)⟧ ⟶ P.closedTerm.obj K))
    (hm : ∀ K : CategoryTheory.Endofunctor.IsoAlgebra G,
      ∃ ac : (G.obj (P.openTerm.obj K.carrier) ≅ P.openTerm.obj K.carrier) ×
          (G.obj (P.closedTerm.obj K.carrier) ≅ P.closedTerm.obj K.carrier),
        G.map (P.counit.app K.carrier) ≫ K.str.hom =
          ac.1.hom ≫ P.counit.app K.carrier ∧
        G.map (P.unit.app K.carrier) ≫ ac.2.hom =
          K.str.hom ≫ P.unit.app K.carrier) :
    SfRecollementWeilEquivariant P G s := by
  let := s
  let : G.IsTriangulated := hex
  intro K
  obtain ⟨ac, ha, hc⟩ := hm K
  have hv : Subsingleton ((G.obj (P.openTerm.obj K.carrier))⟦(1 : ℤ)⟧ ⟶
      P.closedTerm.obj K.carrier) := by
    let := ho K.carrier
    let e := Iso.homCongr ((shiftFunctor C (1 : ℤ)).mapIso ac.1)
      (Iso.refl (P.closedTerm.obj K.carrier))
    exact ⟨fun f g ↦ e.injective (Subsingleton.elim (e f) (e g))⟩
  have hext (δ) (hδ : Triangle.mk (P.counit.app K.carrier)
      (P.unit.app K.carrier) δ ∈ distTriang C) :=
    (triangle_morphism_extension _ _ (G.map_distinguished _ hδ) hδ K.str.hom).2.1 hv
  refine ⟨ac, ⟨ha, hc, ?_⟩, ?_⟩
  · intro δ hδ
    obtain ⟨τ, _, _, _, hτ⟩ :=
      (hext δ hδ).2.2 ac.1.hom ac.2.hom ha.symm hc
    change (G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app (P.openTerm.obj K.carrier)) ≫
      (shiftFunctor C (1 : ℤ)).map ac.1.hom = ac.2.hom ≫ δ at hτ
    simpa only [Category.assoc] using hτ
  · rintro bc ⟨hb, hd, _⟩
    obtain ⟨δ, hδ⟩ := ht K.carrier
    apply Prod.ext
    · apply Iso.ext
      exact (hext δ hδ).1 bc.1.hom ac.1.hom hb.symm ha.symm
    · apply Iso.ext
      exact (hext δ hδ).2.1 bc.2.hom ac.2.hom hd hc

attribute [local irreducible] commonStageDerivedPullback

/-- Weil equivariance at a rational coefficient stage, for the prescribed open and
closed terms and every connecting arrow supplied by the localization triangle.
The geometric map is the actual base change of the closed immersion over k₀;
no k-linearity hypothesis is imposed on the semilinear geometric Frobenius.
Source: blueprint proof steps 12--16
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: geometric Frobenius is semilinear on the closure and commutes with the
base-changed closed immersion and its open complement. The inverse automorphism
squares give inverse pullback, closed-image and open-extension comparisons. Their
mates are isomorphisms. The tensor-unit normalizations identify the ordinary maps
with the specified completed maps, and mate pasting makes the counit and unit
squares commute. Combine these comparisons with the middle Weil isomorphism to
obtain the two outer Weil isomorphisms. Pullback of the distinguished triangle is
distinguished. The two squares identify its first two arrows with the original
ones, so uniqueness forces its connecting arrow to be the original one. Shifted
Hom vanishing gives uniqueness of the outer structures with those squares. -/
theorem sfOpenClosedTriangle_rational_weil
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X₀ Z₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (i₀ : Z₀ ⟶ X₀) [IsClosedImmersion i₀.left]
    (i : (D.geometricFiber Z₀).left ⟶ (D.geometricFiber X₀).left)
    [IsClosedImmersion i]
    (_hi : i = ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map i₀).left)
    (P : SfRecollementPresentation
      (sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left))
    (Q : SfRecollementPresentation
      (sfRationalConstructibleCategory l E (D.geometricFiber X₀).left))
    (_hP : SfIntegralRecollementNormalization l E i (sfRecollementGeometricNoetherian D X₀) P)
    (_hQ : SfRationalRecollementNormalization l E (D.geometricFiber X₀).left P Q) :
    ∃ s : (sfWeilFrobeniusPullback D l hl X₀ E).CommShift ℤ,
      SfRecollementFrobeniusExact (sfWeilFrobeniusPullback D l hl X₀ E) s ∧
      SfRecollementWeilEquivariant Q (sfWeilFrobeniusPullback D l hl X₀ E) s := by
  let : Fact (l ≠ D.p) := ⟨hl⟩
  let : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let : IsSeparated (D.geometricFiber X₀).hom := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  let : LocallyOfFiniteType (D.geometricFiber X₀).hom := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  let : QuasiCompact (D.geometricFiber X₀).hom := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  obtain ⟨_, _, _, _, _, _, _, ⟨s, hs⟩, _, _⟩ :=
    automorphismConstructibleStage_integral_rational D l E
      (D.geometricFiber X₀) (D.geometricFrobenius X₀)
  refine ⟨s, hs, ?_⟩
  obtain ⟨ht, ho⟩ := sfNormalizedRationalRecollement_triangle_orthogonality l E i
    (sfRecollementGeometricNoetherian D X₀) P Q _hP _hQ
  exact sfRecollementWeilEquivariant_of_squares Q _ s hs ht (fun K ↦ ho K K 1)
    (sfNormalizedRationalRecollement_weil_squares l E D hl X₀ Z₀ i₀ i _hi P Q _hP _hQ)

/-- Weil equivariance after common-stage descent. This uses precisely the recorded
algebraically closed Weil category of fixed pairs, not a derived category of pairs.
Source: blueprint proof steps 11--16
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: the Frobenius comparisons and their mate unit/counit equations commute with
finite scalar extension. Descend them to common stages, where geometric Frobenius
is the recorded common-stage pullback. Each finite diagram, including the Weil
isomorphism, has a common coefficient stage; its inverse is represented after a
further extension. The rational argument gives the outer Weil structures and the
first two commuting squares there. Exact stage inclusion transports the triangle.
Uniqueness of its third arrow gives the final equivariance equation independently
of the representing stage. Shifted Hom vanishing gives uniqueness of the outer
structures characterized by the first two squares. -/
theorem sfOpenClosedTriangle_qbar_weil
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X₀ Z₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (i₀ : Z₀ ⟶ X₀) [IsClosedImmersion i₀.left]
    (i : (D.geometricFiber Z₀).left ⟶ (D.geometricFiber X₀).left)
    [IsClosedImmersion i]
    (_hi : i = ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map i₀).left)
    (P : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      SfRecollementPresentation (sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (D.geometricFiber X₀).left))
    (Q : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      SfRecollementPresentation
        (GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber X₀).left L))
    (_hPQ : ∀ L, SfIntegralRecollementNormalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) i
        (sfRecollementGeometricNoetherian D X₀) (P L) ∧
      SfRationalRecollementNormalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
        (D.geometricFiber X₀).left (P L) (Q L))
    (R : SfRecollementPresentation
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left))
    (_hR : SfCommonStageRecollementNormalization l Ω (D.geometricFiber X₀).left Q R) :
    ∃ s : (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).CommShift ℤ,
      SfRecollementFrobeniusExact (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω) s ∧
      SfRecollementWeilEquivariant R (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω) s := by
  classical
  let : Fact (l ≠ D.p) := ⟨hl⟩
  let : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let : IsSeparated (D.geometricFiber X₀).hom := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  let : LocallyOfFiniteType (D.geometricFiber X₀).hom := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  let : QuasiCompact (D.geometricFiber X₀).hom := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  have hExact : ∃ s : (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).CommShift ℤ,
      SfRecollementFrobeniusExact (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω) s := by
    simpa only [sfCommonStageWeilFrobeniusPullback, SfRecollementFrobeniusExact] using
      (automorphismConstructibleStage_qbar D l Ω
        (D.geometricFiber X₀) (D.geometricFrobenius X₀)).2.2.1
  obtain ⟨s, hs⟩ := hExact
  refine ⟨s, hs, ?_⟩
  let X := (D.geometricFiber X₀).left
  let : X.Over (Spec (.of D.k)) := ⟨(D.geometricFiber X₀).hom⟩
  let : LocallyOfFiniteType (X ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (D.geometricFiber X₀).hom)
  let : QuasiCompact (X ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (D.geometricFiber X₀).hom)
  let : IsSeparated (X ↘ Spec (.of D.k)) :=
    inferInstanceAs (IsSeparated (D.geometricFiber X₀).hom)
  have hk : IsUnit (l : D.k) := by
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    have : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    have hunit : IsUnit (l : D.k₀) :=
      (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) hl.symm).isUnit
    simpa only [map_natCast] using hunit.map (algebraMap D.k₀ D.k)
  let W : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let : W.toScheme.Over (Spec (.of D.k)) := ⟨W.ι ≫ (D.geometricFiber X₀).hom⟩
  let : W.ι.IsOver (Spec (.of D.k)) := ⟨rfl⟩
  obtain ⟨R₀, hR₀, _, ho₀⟩ := sfNormalizedRecollement_commonStage_descent l Ω
    D.k hk
    i W.ι W.range_ι P Q _hPQ
  have ho (K L : generalAlgebraicallyClosedConstructibleCategory l Ω X) (n : ℤ) :
      Subsingleton ((R.openTerm.obj K)⟦n⟧ ⟶ R.closedTerm.obj L) := by
    rw [(_hR.1 K).1, (_hR.1 L).2]
    rw [← (hR₀.1 K).1, ← (hR₀.1 L).2]
    exact ho₀ K L n
  have ht (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
      ∃ δ, Triangle.mk (R.counit.app K) (R.unit.app K) δ ∈ distTriang _ := by
    let F := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := Ω) (Y := (D.geometricFiber X₀).left) K.stage
    obtain ⟨a, c, ha, hc⟩ := _hR.2 K.stage
    obtain ⟨htQ, _⟩ := sfNormalizedRationalRecollement_triangle_orthogonality l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) i
      (sfRecollementGeometricNoetherian D X₀) (P K.stage) (Q K.stage)
      (_hPQ K.stage).1 (_hPQ K.stage).2
    have hAdd : ∀ n : ℤ,
        (shiftFunctor (GeneralAlgebraicallyClosedCoefficients.Stage l Ω
          (D.geometricFiber X₀).left K.stage) n).Additive :=
      fun n ↦ GeneralAlgebraicallyClosedCoefficients.stageShiftAdditive l Ω
        (D.geometricFiber X₀).left K.stage n
    apply sfRecollement_triangle_transport
      (B := GeneralAlgebraicallyClosedCoefficients.Stage l Ω
        (D.geometricFiber X₀).left K.stage)
      (shiftAddB := hAdd)
      (C := generalAlgebraicallyClosedConstructibleCategory l Ω
        (D.geometricFiber X₀).left) (Q K.stage) R F K.obj
      (a.app K.obj) (c.app K.obj) _ _ (htQ K.obj)
    · change R.counit.app K = a.hom.app K.obj ≫
        (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).map
          ((Q K.stage).counit.app K.obj)
      exact (ha K.obj).symm
    · change R.unit.app K ≫ c.hom.app K.obj =
        (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).map
          ((Q K.stage).unit.app K.obj)
      exact hc K.obj
  exact sfRecollementWeilEquivariant_of_squares R _ s hs ht (fun K ↦ ho K K 1)
    (sfNormalizedCommonStageRecollement_weil_squares l Ω D hl X₀ Z₀ i₀ i _hi P Q _hPQ R _hR)

end WeilConjectures
