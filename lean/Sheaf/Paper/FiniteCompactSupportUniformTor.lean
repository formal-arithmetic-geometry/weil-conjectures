/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.Compactification.BoundaryPreparation
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.Paper.RefinementComparisonIsomorphism
public import Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange
import Sheaf.AlgebraicGeometry.DimensionExtension
import Sheaf.Paper.OpenExtensionFiniteTor
import Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin

/-!
# Uniform finite-coefficient Tor bounds for compact support

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
lem-coef-integral-compact-support, proof paragraph 1, dense closure through the
finite compact-support comparison (blueprint: lem-coef-finite-compact-support-uniform-tor).

The compactification is the specified dense refinement. The comparison below transports
its canonical refinement comparison through the existing coefficient realization, using
an explicit etale-origin witness. No arbitrary comparison map is introduced.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The refinement arrow from the specified dense scheme image to the original
compactification. Its ambient map is the scheme-image closed immersion.
Source: blueprint, lem-coef-integral-compact-support, proof paragraph 1
(blueprint: lem-coef-finite-compact-support-uniform-tor). -/
def compactSupportDenseRefinementArrow {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c : Compactification f) : c.denseRefinement.Refinement c where
  hom := c.i.imageι
  i_hom := c.i.toImage_imageι
  hom_g := rfl

/-- The canonical compactification comparison at an actual intrinsic object. First
transport its given origin identification backwards, then use the normalized realization
comparison, the proper-composition/proper-open refinement comparison, and the inverse
realization comparison. Finally transport the input identification forwards.
Source: blueprint, lem-coef-integral-compact-support, proof paragraph 1, finite support
comparison (blueprint: lem-coef-finite-compact-support-uniform-tor). -/
def finiteCompactSupportDenseComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f)
    (L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n))
    (O : RefinementFiniteLevelOrigin l E n hn X)
    (w : (@sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n hn)).functor.obj
        (refinementFiniteLevelFixedObject l E n hn X O) ≅ L) :
    (@sfIntrinsicCompactSupport X Y f c.denseRefinement
      (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n hn)).obj L ≅
      (@sfIntrinsicCompactSupport X Y f c
        (Padic.coefficientExtensionRing l E n) _
        (Padic.finite_coefficientExtensionRing l E n hn)).obj L :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  letI : TopologicalSpace (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) := ⊥
  letI := discreteTopology_bot (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
  (@sfIntrinsicCompactSupport X Y f c.denseRefinement
    (Padic.coefficientExtensionRing l E n) _
    (Padic.finite_coefficientExtensionRing l E n hn)).mapIso w.symm ≪≫
    (sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing l E n)
      c.denseRefinement).app (refinementFiniteLevelFixedObject l E n hn X O) ≪≫
    (sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E n)).functor.mapIso
      (refinementComparisonAtWitness (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
        (compactSupportDenseRefinementArrow c) O) ≪≫
    ((sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing l E n) c).app
      (refinementFiniteLevelFixedObject l E n hn X O)).symm ≪≫
    (@sfIntrinsicCompactSupport X Y f c
      (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n hn)).mapIso w

/-- Dense refinement controls the dimension of the compactifying scheme and gives
one finite-level compact-support Tor estimate, for every level and every original
compactification. The existential witness supplies the domain of the canonical
comparison; the displayed equality fixes its value, not just its isomorphism class.
Source: Weil blueprint, lem-coef-integral-compact-support, proof paragraph 1
(blueprint: lem-coef-finite-compact-support-uniform-tor).

Proof plan, following the seven DAG steps:
1. Finite type makes f quasi-compact. Properness makes c.g separated and hence
quasi-separated. QuasiCompact.of_comp gives quasi-compactness of c.i
(lemma-nagata-open-immersion-qc-over-separated-target).
2. def-nagata-dense-refinement and prop-nagata-dense-refinement identify the refined
ambient scheme with c.i.image, its open map with c.i.toImage, and its proper map with
c.i.imageι followed by c.g. lemma-nagata-immersion-open-in-scheme-image gives density.
3. The proper map of the refinement is finite type. Composing with the finite-type
structure map of Y proves both finite-type conditions on the refined ambient scheme.
4. lem-kun-dimension-extension applied to this dense open immersion gives equality
of dimensions; the assumed bound for X therefore bounds this ambient scheme.
5. lem-trf-open-ctf preserves intrinsic bounded constructibility and [a,b] under j_!.
Apply cor-sf-direct-image-ctf-proetale to the refined proper map and the dimension
bound to get intrinsic bounded constructibility and [a,b+2d].
6. The finite-ring constructible derived origin criterion gives a bounded constructible
etale origin for L. Retain its comparison image with the identity origin witness and use
refinementFixedWitnessIso to identify its fixed realization with L. The specified
finiteCompactSupportDenseComparison then compares the two candidates.
7. Transport cohomology constructibility and finite support across this isomorphism.
Tensoring the isomorphism with every degree-zero module transports Tor vanishing.
Neither the refinement nor d depends on n. The original compactification is arbitrary.
-/
theorem finiteCompactSupport_uniformTor_after_denseRefinement
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₀ : Compactification f) (d : ℕ)
    (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    LocallyOfFiniteType (c₀.denseRefinement.g ≫ (Y ↘ Spec (.of D.k))) ∧
      QuasiCompact (c₀.denseRefinement.g ≫ (Y ↘ Spec (.of D.k))) ∧
      DenseRange c₀.denseRefinement.i ∧
      topologicalKrullDim c₀.denseRefinement.Z = topologicalKrullDim X ∧
      topologicalKrullDim c₀.denseRefinement.Z ≤ (d : WithBot ℕ∞) ∧
      ∀ (n : ℕ) (hn : 1 ≤ n) (a b : ℤ) (_hab : a ≤ b)
        (L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n))
        (_hL : intrinsicFiniteTorsionConstructible l E n hn X L)
        (_hTor : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n) L a b),
        intrinsicFiniteTorsionConstructible l E n hn Y
            ((@sfIntrinsicCompactSupport X Y f c₀.denseRefinement
              (Padic.coefficientExtensionRing l E n) _
              (Padic.finite_coefficientExtensionRing l E n hn)).obj L) ∧
          HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n)
            ((@sfIntrinsicCompactSupport X Y f c₀.denseRefinement
              (Padic.coefficientExtensionRing l E n) _
              (Padic.finite_coefficientExtensionRing l E n hn)).obj L)
              a (b + 2 * (d : ℤ)) ∧
          intrinsicFiniteTorsionConstructible l E n hn Y
            ((@sfIntrinsicCompactSupport X Y f c₀
              (Padic.coefficientExtensionRing l E n) _
              (Padic.finite_coefficientExtensionRing l E n hn)).obj L) ∧
          HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n)
            ((@sfIntrinsicCompactSupport X Y f c₀
              (Padic.coefficientExtensionRing l E n) _
              (Padic.finite_coefficientExtensionRing l E n hn)).obj L) a (b + 2 * (d : ℤ)) ∧
          ∃ (O : RefinementFiniteLevelOrigin l E n hn X)
            (w : (@sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E n) _
              (Padic.finite_coefficientExtensionRing l E n hn)).functor.obj
                (refinementFiniteLevelFixedObject l E n hn X O) ≅ L)
            (α : (@sfIntrinsicCompactSupport X Y f c₀.denseRefinement
              (Padic.coefficientExtensionRing l E n) _
              (Padic.finite_coefficientExtensionRing l E n hn)).obj L ≅
              (@sfIntrinsicCompactSupport X Y f c₀
                (Padic.coefficientExtensionRing l E n) _
                (Padic.finite_coefficientExtensionRing l E n hn)).obj L),
            α = finiteCompactSupportDenseComparison l E n hn c₀ L O w := by
  classical
  let c := c₀.denseRefinement
  let S := Spec (CommRingCat.of D.k)
  let : c.Z.Over S := ⟨c.g ≫ (Y ↘ S)⟩
  have hft : LocallyOfFiniteType (c.g ≫ (Y ↘ S)) := inferInstance
  have hqc : QuasiCompact (c.g ≫ (Y ↘ S)) := inferInstance
  have : IsSchemeTheoreticallyDominant c.i :=
    c₀.isSchemeTheoreticallyDominant_denseRefinement_i
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have : LocallyOfFiniteType (c.Z ↘ S) := hft
  have : QuasiCompact (c.Z ↘ S) := hqc
  have hdense : DenseRange c.i := c.i.denseRange
  have hdim : topologicalKrullDim c.Z = topologicalKrullDim X :=
    (topologicalKrullDim_fieldExtension_and_denseOpen (K := D.k) (X := c.Z)).2
      X c.i hdense |>.symm
  have hbound : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞) := hdim.trans_le _hd
  refine ⟨hft, hqc, hdense, hdim, hbound, ?_⟩
  intro n hn a b _hab L hL hTor
  let A := Padic.coefficientExtensionRing l E n
  have : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  have : c.i.IsOver S := ⟨by
    change c.i ≫ (c.g ≫ (Y ↘ S)) = (X ↘ S)
    rw [← Category.assoc, ← c.comm]
    simp⟩
  have hopen := finiteStageDerivedExtensionByZero_constructibleFiniteTor
    D l _hl E n hn c.i L hL ⟨a, b, hTor⟩
  let p : Over.mk (c.g ≫ (Y ↘ S)) ⟶ Over.mk (Y ↘ S) := Over.homMk c.g rfl
  have : LocallyOfFiniteType (Over.mk (c.g ≫ (Y ↘ S))).hom := hft
  have : QuasiCompact (Over.mk (c.g ≫ (Y ↘ S))).hom := hqc
  have : LocallyOfFiniteType (Over.mk (Y ↘ S)).hom :=
    inferInstanceAs (LocallyOfFiniteType (Y ↘ S))
  have : QuasiCompact (Over.mk (Y ↘ S)).hom :=
    inferInstanceAs (QuasiCompact (Y ↘ S))
  have : IsSeparated p.left := inferInstanceAs (IsSeparated c.g)
  have : LocallyOfFiniteType p.left := inferInstanceAs (LocallyOfFiniteType c.g)
  have : QuasiCompact p.left := inferInstanceAs (QuasiCompact c.g)
  have hproper := finiteCoefficientDirectImage_boundedConstructible_torAmplitude
    D l _hl E n hn _ _ p d hbound a b hopen.1 (hopen.2.2 a b hTor)
  have hc : intrinsicFiniteTorsionConstructible l E n hn Y
      ((sfIntrinsicCompactSupport c A).obj L) := hproper.1
  have ht : HasProEtaleTorAmplitude Y A
      ((sfIntrinsicCompactSupport c A).obj L) a (b + 2 * (d : ℤ)) := hproper.2
  obtain ⟨lo, hlo⟩ := hL.1.bddBelow
  obtain ⟨hi, hhi⟩ := hL.1.bddAbove
  have hvan (i : ℤ) (hi' : i < min lo hi ∨ max lo hi < i) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj L) := by
    by_contra hz
    rcases hi' with hi' | hi'
    · exact (not_lt_of_ge (hlo hz)) (hi'.trans_le (min_le_left _ _))
    · exact (not_lt_of_ge (hhi hz)) ((le_max_right _ _).trans_lt hi')
  obtain ⟨G, ⟨eG⟩⟩ := ((finiteRing_constructibleDerived_origin X A).2.2.1 L).mpr
    ⟨hL.2, min lo hi, max lo hi, min_le_max, hvan⟩
  obtain ⟨r, s, _, hv⟩ := G.property.2
  let Gplus : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
    ⟨G.obj, r, (DerivedCategory.isGE_iff G.obj r).mpr (fun i hi ↦ hv i (Or.inl hi))⟩
  let : TopologicalSpace (ULift.{u + 1, u} A) := ⊥
  let : DiscreteTopology (ULift.{u + 1, u} A) := discreteTopology_bot _
  let O : RefinementFiniteLevelOrigin l E n hn X :=
    ⟨(finiteCoefficientComparison X (ULift.{u + 1, u} A)).mapDerivedCategoryPlus.obj Gplus,
      ⟨Gplus, Iso.refl _⟩⟩
  let w : (sfIntrinsicDerivedEquivalence X A).functor.obj
      (refinementFiniteLevelFixedObject l E n hn X O) ≅ L :=
    (sfIntrinsicDerivedEquivalence X A).functor.mapIso
      (refinementFixedWitnessIso X (ULift.{u + 1, u} A) O).symm ≪≫
    ((Functor.mapDerivedCategoryCompIso
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X)
      (sfIntrinsicModuleEquivalence X A).functor).app G.obj).symm ≪≫ eG
  let α := finiteCompactSupportDenseComparison l E n hn c₀ L O w
  have hc' : intrinsicFiniteTorsionConstructible l E n hn Y
      ((sfIntrinsicCompactSupport c₀ A).obj L) := by
    exact (finiteTorsionConstructible D l _hl E n hn Y).prop_of_iso α hc
  have ht' : HasProEtaleTorAmplitude Y A
      ((sfIntrinsicCompactSupport c₀ A).obj L) a (b + 2 * (d : ℤ)) := by
    refine ⟨ht.1, ?_⟩
    intro C P hC t htP hP M i hi
    obtain ⟨eC⟩ := hC
    exact ht.2 C P ⟨eC ≪≫ α.symm⟩ t htP hP M i hi
  exact ⟨hc, ht, hc', ht', O, w, α, rfl⟩

end AlgebraicGeometry.ProEtale
