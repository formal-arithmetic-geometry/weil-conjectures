/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryFunctor
import Sheaf.Paper.QcqsProperConstructibleClosedBaseChange
import Sheaf.Paper.QcqsFiniteValuedAlgClClosedBaseChange
import Sheaf.Paper.QcOpenExtensionConstantModelFiniteTor
import Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Sheaf.CategoryTheory.Triangulated.LocalizingSubcategoryUniverse

/-!
# Boundary vanishing for a proper refinement over a qcqs base

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md`, (2),
closed-complement calculation and its ambient localizing extension
(blueprint: lem-sfb-qcqs-proper-open-boundary-vanishing).

All three functors act on the ordinary unbounded derived categories of module objects
for the coefficient rings pulled back from the point. The closed immersion is specified
only by its underlying image; its source need not be the reduced closed complement.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem map_shift_isZero
    {C : Type v₁} {D : Type v₂} [Category.{w₁} C] [Category.{w₂} D]
    [HasZeroMorphisms D] [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).PreservesZeroMorphisms]
    (F : C ⥤ D) [F.CommShift ℤ] (n : ℤ) (M : C)
    (hM : IsZero (F.obj M)) : IsZero (F.obj ((shiftFunctor C n).obj M)) :=
  ((shiftFunctor D n).map_isZero hM).of_iso ((F.commShiftIso n).app M)

private theorem map_triangle_isZero₂
    {C : Type v₁} {D : Type v₂} [Category.{w₁} C] [Category.{w₂} D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsZero (F.obj T.obj₁)) (h₃ : IsZero (F.obj T.obj₃)) :
    IsZero (F.obj T.obj₂) :=
  (F.mapTriangle.obj T).isZero₂_of_isZero₁₃ (F.map_distinguished T hT) h₁ h₃

private theorem admissible_coefficient_cases
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    IsNormTopologicalLocalizingAdmissibleCoefficient ℓ Λ ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
  rcases hΛ with h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact Or.inr h

/-- Restriction to the boundary of a proper direct image of open extension by zero
vanishes on the ambient localizing closure of bounded constructible finite-Tor objects.

Source: blueprint main-20261015, sec-six-functors-basics,
`det-sf-comp-coherence-refinement.proof.md`, (2), closed-complement calculation
(blueprint: lem-sfb-qcqs-proper-open-boundary-vanishing).

Proof in words:
1. Properness gives qcqs total spaces. The given image equality identifies the closed
   pullback B' with the complement of j'. The quasi-compact open gives the compact
   boundary complement required by `qcqs_proper_open_boundary_functor`.
2. For a bounded constructible finite-Tor generator M, open extension J M is again
   bounded constructible finite-Tor by `qcOpenExtension_constantModelConstructible_finiteTor`.
   Apply closed proper base change. The existing norm-topological theorem handles the
   first five admissible coefficient cases; `qcqs_finiteValuedAlgCl_closed_baseChange`
   handles the sixth. Mixed open/closed restriction vanishes, and derived direct
   image preserves zero, so the boundary composite F vanishes on every generator.
3. Intersect the hom-universe localizing hull L with the zero locus of F. Repleteness
   follows from functoriality. The supplied triangulated structures and the commutation
   with shifts make this intersection triangulated, by the two-out-of-three property
   for zero objects in a distinguished triangle.
4. The boundary-functor theorem makes F preserve ambient coproducts of L-objects.
   Thus a coproduct of objects of the intersection stays in L and has zero image under F.
   The indexing-universe lemma extends this closure to every existing coproduct in the
   object universe: nonzero summands inject into endomorphisms of the coproduct vertex,
   hence form a small family; omitting zero summands leaves the same colimit vertex.
5. The resulting object-universe localizing subcategory contains the generators.
   Minimality in `localizingClosureProEtale` puts K in it, proving the claimed vanishing.
   No density or dimension assumption is used. -/
theorem qcqs_proper_open_boundary_vanishing
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {S Z Z' U B : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (q : Z ⟶ S) (q' : Z' ⟶ S) [IsProper q] [IsProper q']
    (h : Z' ⟶ Z) [IsProper h] (hh : h ≫ q = q')
    (j : U ⟶ Z) (j' : U ⟶ Z')
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion j'] [QuasiCompact j']
    (hj : j' ≫ h = j) (hU : h ⁻¹' Set.range j = Set.range j')
    (i : B ⟶ Z) [IsClosedImmersion i] (hi : Set.range i = (Set.range j)ᶜ)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
    (hK : localizingClosureProEtale Λ U K) :
    IsZero ((upperStar Λ i).mapDerivedCategory.obj
      ((moduleObjectDerivedPushforward Λ h).obj
        ((openImmersionLowerShriek Λ j').mapDerivedCategory.obj K))) := by
  have _ := hh
  have _ := hj
  let A (T : Scheme.{u}) :=
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)
  let G : ObjectProperty (DerivedCategory (A U)) :=
    constantModelBoundedConstructible Λ U ⊓ fun L ↦ DerivedCategory.finiteTorAmplitude _ L
  let L := localizingClosureOfSize.{u + 1} G
  let J := (openImmersionLowerShriek Λ j').mapDerivedCategory
  let F := J ⋙ moduleObjectDerivedPushforward Λ h ⋙ (upperStar Λ i).mapDerivedCategory
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated q
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  have hc : IsCompact (Set.range i)ᶜ := by
    rw [hi, compl_compl]
    exact isCompact_range j.continuous
  obtain ⟨_, _, hJ, hB, _, _, _, ⟨hL, _⟩, hcop⟩ :=
    qcqs_proper_open_boundary_functor ℓ Λ hΛ q h j' i hc
  have : J.IsTriangulated := hJ
  have : (upperStar Λ i).mapDerivedCategory.IsTriangulated := hB
  have : L.IsTriangulated := hL
  let : F.CommShift ℤ := by
    dsimp [F, moduleObjectDerivedPushforward]
    infer_instance
  have : F.IsTriangulated := by
    dsimp [F, moduleObjectDerivedPushforward]
    infer_instance
  have : F.Additive := by
    dsimp [F, moduleObjectDerivedPushforward]
    infer_instance
  have : L.IsClosedUnderIsomorphisms := ⟨by
    intro M N e hM P hP hgen
    have := hP.2.1
    exact P.prop_of_iso e (hM P hP hgen)⟩
  have hgen (M : DerivedCategory (A U)) (hM : G M) : IsZero (F.obj M) := by
    have ha : Set.range (pullback.fst h i) = (Set.range j')ᶜ := by
      rw [Scheme.Pullback.range_fst, hi, Set.preimage_compl, hU]
    have hz := (condensedSupportDerivedLocalization Λ (pullback.fst h i) j' ha).2.2.2.1 M
    have hz' : IsZero ((upperStar Λ (pullback.fst h i)).leftDerivedFunctor.obj
        (J.obj M)) := by
      exact hz.of_iso (((leftDerivedUpperStarIsoMapDerivedCategory Λ (pullback.fst h i)) ≪≫
        (Functor.mapDerivedCategoryNatIso
          (supportPullbackIsoUpperStar Λ (pullback.fst h i))).symm).app (J.obj M))
    have : QuasiCompact (Scheme.Opens.ι (X := Z)
        ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩) := by
      have : CompactSpace (Scheme.Opens.toScheme (X := Z)
          ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩) :=
        isCompact_iff_compactSpace.mp hc
      exact quasiCompact_of_compactSpace _
    let N : ConstantModelConstructibleFiniteTor Λ Z' :=
      ⟨J.obj M, (qcOpenExtension_constantModelConstructible_finiteTor
        ℓ Λ hΛ j').2.2.2.2 M hM⟩
    have he : IsIso ((condensedAmbientExchange Λ
        (g' := pullback.fst h i) (f' := pullback.snd h i) (f := h) (g := i)
        { w := pullback.condition
          isoPullback := Iso.refl _
          hom_fst := Category.id_comp _
          hom_snd := Category.id_comp _ }).app N.obj) := by
      rcases admissible_coefficient_cases ℓ Λ hΛ with hnorm | hfin
      · exact qcqs_proper_constructible_closed_baseChange ℓ Λ hnorm q h i N
      · exact qcqs_finiteValuedAlgCl_closed_baseChange ℓ Λ hfin q h i N
    have hz'' := (lowerStar Λ (pullback.snd h i)).rightDerivedFunctor.map_isZero hz'
    exact (hz''.of_iso (asIso ((condensedAmbientExchange Λ
      (g' := pullback.fst h i) (f' := pullback.snd h i) (f := h) (g := i)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app N.obj))).of_iso
          ((leftDerivedUpperStarIsoMapDerivedCategory Λ i).symm.app
            ((moduleObjectDerivedPushforward Λ h).obj (J.obj M)))
  let P : ObjectProperty (DerivedCategory (A U)) := L ⊓ F.kernel
  have : P.IsClosedUnderIsomorphisms := inferInstance
  have : P.IsTriangulated := by
    refine {
      exists_zero := ⟨0, isZero_zero _, ?_⟩
      isStableUnderShiftBy := fun n ↦ ⟨?_⟩
      ext₂' := ?_ }
    · exact ⟨L.prop_zero, F.map_isZero (isZero_zero _)⟩
    · intro M hM
      change L ((shiftFunctor _ n).obj M) ∧ IsZero (F.obj ((shiftFunctor _ n).obj M))
      refine ⟨L.le_shift n M hM.1, ?_⟩
      exact map_shift_isZero F n M hM.2
    · intro T hT h₁ h₃
      exact ⟨T.obj₂, ⟨L.ext_of_isTriangulatedClosed₂ T hT h₁.1 h₃.1,
        map_triangle_isZero₂ F T hT h₁.2 h₃.2⟩, ⟨Iso.refl _⟩⟩
  have hP : IsLocalizingSubcategoryOfSize.{u + 1} P := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I E hE hobj
    have : HasColimit E := hE
    have hsum : L (colimit E) := by
      intro Q hQ hgen
      exact hQ.2.2 E hE (fun t ↦ (hobj t).1 Q hQ hgen)
    have hpres : PreservesColimit E F := by
      have : PreservesColimit (Discrete.functor (E.obj ∘ Discrete.mk)) F :=
        hcop I (fun t ↦ E.obj (Discrete.mk t)) (fun t ↦ (hobj t).1)
      exact preservesColimit_of_iso_diagram F (Discrete.natIsoFunctor (F := E)).symm
    have hzero : IsZero (E ⋙ F) :=
      (E ⋙ F).isZero_iff.2 (fun t ↦ (hobj t.as).2)
    exact ⟨hsum, (isColimitOfPreserves F (colimit.isColimit E)).isZero_pt hzero⟩
  have hP' : IsLocalizingSubcategory P := isLocalizingSubcategory_of_locallySmall P hP
  exact (hK P hP' (fun M hM ↦ ⟨fun Q hQ hgen ↦ hgen M hM, hgen M hM⟩)).2

end AlgebraicGeometry.ProEtale.CondensedRing
