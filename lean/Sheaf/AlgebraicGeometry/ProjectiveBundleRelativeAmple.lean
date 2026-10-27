/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.TraceFormula.GradedImmersionAmpleCriterion
import Sheaf.TraceFormula.ProjectiveBundleProper
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
import Sheaf.TraceFormula.LineQuotientHomogeneousFractionMap
import Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback

/-!
# Finite type and relative ampleness for projective-bundle morphisms

Source: Stacks Project, Morphisms, Lemma 07RL (lemma-projective-quasi-projective),
Definition 01VW(1) (definition-quasi-projective), and Definition 01VH
(definition-relatively-ample)
(blueprint: lem-sfb-projective-bundle-relative-ample).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A projective-bundle morphism is of finite type and admits a relatively ample
invertible module. Relative ampleness is written out: quasi-compactness of the morphism
and absolute ampleness of the restriction over every affine open of the target.

Source: Stacks Project, Morphisms, Lemma 07RL, Definitions 01VW(1) and 01VH.

Proof:
1. Apply `lem-trf-projective-bundle-proper` to obtain properness. By
`def-weil-proper-morphism` and `def-weil-finite-type-morphism`, this gives local finite
type and quasi-compactness, hence finite type.
2. Unpack `def-trf-projective-bundle-morphism`: take a finite-type quasi-coherent E,
its projective bundle P, and a closed immersion i : X -> P over S. Put L = i^* O_P(1),
using `def-pc-module-pullback`. By `lem-trf-projective-bundle-quotient-geometry`, O_P(1)
is invertible, even when E is not locally free. By
`lem-weil-pbc-invertible-pullback-invertible`, L is invertible.
3. The normalized quotient of `lem-trf-projective-bundle-quotient-geometry` gives
h^* E ->> L and identifies i with its canonical relative-Proj map for the graded
symmetric algebra of `def-trf-canonical-symmetric-graded-algebra`. Its degree-one
surjectivity makes the generation locus all of X. A closed immersion is an immersion
by `def-weil-closed-immersion`, taking the open factor to be the identity. Apply
`lem-trf-graded-immersion-ample-criterion` with h, L, that algebra, and this quotient.
Quasi-compactness comes from step 1, invertibility from step 2, and the canonical-map
and generation conditions from the quotient geometry. It gives absolute ampleness of
L restricted over every affine target open. Together with quasi-compactness, this is
exactly relative ampleness. The L of step 2 is the required witness.
(blueprint: lem-sfb-projective-bundle-relative-ample). -/
theorem projectiveBundle_finiteType_relativeAmple {X S : Scheme.{u}}
    (h : X ⟶ S) (hh : IsProjectiveBundle h) :
    (LocallyOfFiniteType h ∧ QuasiCompact h) ∧
      ∃ L : X.Modules, L.IsInvertible ∧
        ∀ V : S.Opens, IsAffineOpen V →
          ∃ hL : ((Scheme.Modules.tensorPullback (h ⁻¹ᵁ V).ι).obj L).IsInvertible,
            @Scheme.Modules.IsAmple (h ⁻¹ᵁ V).toScheme
              ((Scheme.Modules.tensorPullback (h ⁻¹ᵁ V).ι).obj L) hL := by
  let : IsProper h := projectiveBundle_proper h hh
  refine ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  obtain ⟨E, hE, _, i, hi, hih⟩ := hh
  let := hE
  let := hi
  obtain ⟨D, _⟩ :=
    ProjectiveBundleQuotientGeometry.projective_bundle_quotient_geometry S E
  obtain ⟨hL, hq, _, hinverse⟩ :=
    (ProjectiveBundleQuotientGeometry.line_quotient_chart_inverse_pullback E D).1
      X h i hih
  let L := (Scheme.Modules.tensorPullback i).obj D.line
  let q := ProjectiveBundleQuotientGeometry.pulledQuotient D h i hih
  let : L.IsInvertible := hL
  let : Epi q := hq
  obtain ⟨ψ, hψ, _, hgen, F, hF, _, hcanonical, _⟩ :=
    Scheme.Modules.line_quotient_homogeneous_fraction_map h E L q
  have hFi : F = i := (hinverse ψ F hψ hF).1
  subst F
  exact ⟨L, hL, Scheme.Modules.graded_immersion_ample_criterion h L
    (SymmetricAlgebraSheaf.gradedAlgebraData E) ψ hgen i hcanonical⟩

end AlgebraicGeometry
