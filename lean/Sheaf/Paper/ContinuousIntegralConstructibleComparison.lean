/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R5
-/
module

public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.Paper.IntegralStratifiedPerfectModels
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.PbcUniformCompleteTriangulated
import Sheaf.Paper.ContinuousIntegralSliceModelComparison
import Sheaf.Paper.ContinuousIntegralCoefficientComparison

/-!
# Continuous and completed integral constructibility

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3).
(blueprint: lem-weil-pbc-continuous-integral-constructible-comparison)
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem fp_iso (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {M N : pbcModules T (pbcAdicCompletion T d)} (e : M ≅ N)
    (hM : IsIntegralStratifiedFinitelyPresented T d M) :
    IsIntegralStratifiedFinitelyPresented T d N := by
  obtain ⟨s, hs⟩ := hM
  refine ⟨s, fun i ↦ ?_⟩
  obtain ⟨V, hV, hv⟩ := hs i
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨L, hL, ⟨eL⟩⟩ := hv U f hf
  exact ⟨L, hL, ⟨(SheafOfModules.overFunctor _ U).mapIso
    ((proEtaleModuleInverseImage (s.immersion i) _).mapIso e.symm) ≪≫ eL⟩⟩
private theorem single_complete_iff
    (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [IsNoetherian X]
    (hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n) (hl : IsUnit (l : Γ(X, ⊤)))
    (M : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) :
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((DerivedCategory.singleFunctor _ 0).obj M) ↔
      IsIntegralStratifiedFinitelyPresented X (pbcIntegralDatum l E) M := by
  let d := pbcIntegralDatum l E
  let C := pbcModules X (pbcAdicCompletion X d)
  let P : ObjectProperty (DerivedCategory C) := PbcIsBoundedConstructibleComplete X d
  let Q : ObjectProperty C := IsIntegralStratifiedFinitelyPresented X d
  let : Q.IsClosedUnderIsomorphisms := ⟨fun e h ↦ fp_iso X d e h⟩
  have hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x) := by
    intro x
    simpa only [map_natCast] using
      RingHom.isUnit_map (X.presheaf.germ ⊤ x trivial).hom hl
  have hp := pbcIntegralUniformComplete_isTriangulated l E X hdim hInv
  let : P.IsClosedUnderIsomorphisms := hp.1
  let : P.IsTriangulated := hp.2
  have criterion (K : DerivedCategory C) : P K ↔
      IsIntegralBoundedConstructibleCohomology X d K := by
    have h := integralStratifiedPerfectCharacterization X l E hdim hl K
    exact h.1.trans h.2
  let : Zero (DerivedCategory C) := HasZeroObject.zero' _
  let H := DerivedCategory.homologyFunctor C 0
  let : Q.ContainsZero := ⟨H.obj 0, H.map_isZero (isZero_zero _),
    ((criterion 0).mp (P.prop_zero)).2 0⟩
  let K := (DerivedCategory.singleFunctor C 0).obj M
  let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app M
  constructor
  · intro h
    exact Q.prop_of_iso e (((criterion K).mp h).2 0)
  · intro h
    apply (criterion K).mpr
    refine ⟨⟨0, 0, le_rfl, inferInstance, inferInstance⟩, fun r ↦ ?_⟩
    change Q _
    by_cases hr : r = 0
    · subst r
      exact Q.prop_of_iso e.symm h
    · apply Q.prop_of_isZero
      rcases lt_or_gt_of_ne hr with hr | hr
      · exact DerivedCategory.isZero_of_isGE K 0 r hr
      · exact DerivedCategory.isZero_of_isLE K 0 r hr

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

universe u₁ v₁ w₁ a₁

private theorem localModels_cover_iff_sieve
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    [HasTerminal C] (R : Sheaf J RingCat.{w₁}) {A : Type a₁}
    (P : A → Prop) (G : A → SheafOfModules.{w₁} R) (M : SheafOfModules.{w₁} R) :
    (∃ (I : Type (max u₁ v₁)) (V : I → C), J.CoversTop V ∧
      ∀ i, ∃ a, P a ∧ Nonempty (M.over (V i) ≅ (G a).over (V i))) ↔
    (∃ V : Sieve (⊤_ C), V ∈ J (⊤_ C) ∧
      ∀ (U : C) (f : U ⟶ ⊤_ C), V f →
        ∃ a, P a ∧ Nonempty (M.over U ≅ (G a).over U)) := by
  constructor
  · rintro ⟨I, V, hV, hs⟩
    refine ⟨Sieve.ofObjects V _, hV _, ?_⟩
    rintro U f ⟨i, ⟨g⟩⟩
    obtain ⟨a, ha, ⟨e⟩⟩ := hs i
    exact ⟨a, ha, ⟨((SheafOfModules.overFunctorMap R g).app M).symm ≪≫
      (SheafOfModules.overMap R g).mapIso e ≪≫
        (SheafOfModules.overFunctorMap R g).app (G a)⟩⟩
  · rintro ⟨V, hV, hs⟩
    let I := Σ U : C, {f : U ⟶ ⊤_ C // V f}
    let W : I → C := fun i ↦ i.1
    refine ⟨I, W, ?_, fun i ↦ hs i.1 i.2.val i.2.property⟩
    apply (J.coversTop_iff_of_isTerminal _ terminalIsTerminal W).mpr
    apply J.superset_covering _ hV
    intro U f hf
    exact ⟨⟨U, f, hf⟩, ⟨𝟙 U⟩⟩


/-- Changing from continuous functions to the completed coefficient presentation identifies
continuous constructible sheaves with the degree-zero objects of the complete category.
Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3) and Lemma 6.5.8(1).
(blueprint: lem-weil-pbc-continuous-integral-constructible-comparison).

Proof: use the ring equivalence from the valuation subring in WithAbs E to O_E, and
postcompose continuous functions with it. The normalized residue projections identify
this ring sheaf with the inverse limit of the finite quotient constant sheaves.
The canonical completed-coefficient comparison then gives an equivalence of ambient
module categories by restriction along an isomorphism of rings. On each locally closed
stratum, immersion restriction identifies the actual inverse-image coefficient sheaf
with its continuous-function presentation, compatibly with constant sections. Thus the
equivalence carries the models A_T tensor_A M to the ordinary completed constant models,
with M transported along the lifted valuation-ring equivalence. Finite presentation is
preserved by this ring equivalence. Covering families and covering sieves of the terminal
object give the same local condition. These comparisons identify continuous
constructibility with IsIntegralStratifiedFinitelyPresented. The homology of the degree-zero
single object is the original sheaf in degree zero and zero otherwise, so condition (iii)
of the integral stratified-perfect characterization is precisely this condition. Apply
(iii) iff (i). Zero modules, empty schemes and torsion finitely presented modules are
included; no finite freeness is asserted. -/
theorem continuousIntegralConstructibleComparison
    (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [IsNoetherian X]
    (hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n) (hl : IsUnit (l : Γ(X, ⊤))) :
    ∃ e : SheafOfModules.{u + 1}
        (latticeModuleRing X (latticeCoefficientIntegers l E)) ≌
        Scheme.pbcModules X (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)),
      ∀ M, IsContinuousConstructible X (latticeCoefficientIntegers l E) M ↔
        Scheme.PbcIsBoundedConstructibleComplete X (Scheme.pbcIntegralDatum l E)
          ((DerivedCategory.singleFunctor _ 0).obj (e.functor.obj M)) := by
  obtain ⟨r, c, hsc⟩ := continuousIntegralCoefficientComparison X l E
  let e := CondensedRing.ringModuleEquivalenceOfIso X ((Scheme.adicLisseForget X).mapIso c)
  refine ⟨e, fun M ↦ ?_⟩
  have hc : IsContinuousConstructible X (latticeCoefficientIntegers l E) M ↔
      Scheme.IsIntegralStratifiedFinitelyPresented X (Scheme.pbcIntegralDatum l E)
        (e.functor.obj M) := by
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨s, fun i ↦ ?_⟩
      obtain ⟨V, hV, hv⟩ := (localModels_cover_iff_sieve
        (Scheme.ProEt.topology (s.domain i))
        (latticeModuleRing (s.domain i) (latticeCoefficientIntegers l E))
        (fun P : ModuleCat.{u + 1} (ULift.{u + 1} (latticeCoefficientIntegers l E)) ↦
          Module.FinitePresentation _ P)
        (continuousCoefficientModule (s.domain i) (latticeCoefficientIntegers l E))
        (continuousModulePullback (s.immersion i) (latticeCoefficientIntegers l E) M)).mp
          (hs i)
      exact ⟨V, hV, fun U f hf ↦
        (continuousIntegralSliceModelComparison X l E r c hsc (s.immersion i) M U).mp
          (hv U f hf)⟩
    · rintro ⟨s, hs⟩
      refine ⟨s, fun i ↦ ?_⟩
      obtain ⟨V, hV, hv⟩ := hs i
      apply (localModels_cover_iff_sieve
        (Scheme.ProEt.topology (s.domain i))
        (latticeModuleRing (s.domain i) (latticeCoefficientIntegers l E))
        (fun P : ModuleCat.{u + 1} (ULift.{u + 1} (latticeCoefficientIntegers l E)) ↦
          Module.FinitePresentation _ P)
        (continuousCoefficientModule (s.domain i) (latticeCoefficientIntegers l E))
        (continuousModulePullback (s.immersion i) (latticeCoefficientIntegers l E) M)).mpr
      exact ⟨V, hV, fun U f hf ↦
        (continuousIntegralSliceModelComparison X l E r c hsc (s.immersion i) M U).mpr
          (hv U f hf)⟩
  exact hc.trans (Scheme.single_complete_iff X l E hdim hl (e.functor.obj M)).symm

end AlgebraicGeometry.ProEtale
