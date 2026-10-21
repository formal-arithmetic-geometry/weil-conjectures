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
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.DimensionExtension
import Sheaf.Paper.OpenExtensionFiniteTor
import Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.CompactificationCoherence

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
6. lem-sf-proetale-constructible-origin gives an etale-origin witness for L.
prop-compactification-coherence-detailed identifies the two candidates by the canonical
refinement comparison, realized by finiteCompactSupportDenseComparison below.
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
  sorry

end AlgebraicGeometry.ProEtale
