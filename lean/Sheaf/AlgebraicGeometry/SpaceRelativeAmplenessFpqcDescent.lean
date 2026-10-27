/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.SchemeSpaceZariskiRestriction
import Sheaf.TraceFormula.GradedEvaluationZariskiEtaleComparison
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcQCSeparatedDescent
import Sheaf.TraceFormula.SpaceLineModuleProjMap
import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
import WeilConjectures.AlgebraicGeometry.RelativeProj.Universal
import Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction
import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Relative ampleness of algebraic spaces descends fpqc locally

Source: Stacks Project, Descent on Spaces, Tag 0D3C; Divisors on Spaces, Tags 0D31
and 0D32 (blueprint: lem-sfb-space-relative-ampleness-fpqc-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Relative ampleness, including schematicity, is equivalent before and after an fpqc
scheme cover. A representing scheme is supplied together with its actual map to `X`.
The local pullback squares identify these schemes with `X ×_T Tᵢ`; no schematicity is
assumed. The module on each representing scheme is the canonical tensor pullback of
`L`, followed by the Zariski restriction in the small étale comparison. The existential
invertibility witnesses only provide the proof argument required by absolute `IsAmple`.

Source: Stacks Project, Descent on Spaces, Tag 0D3C, scheme-base case; Divisors on
Spaces, Tags 0D31 and 0D32
(blueprint: lem-sfb-space-relative-ampleness-fpqc-descent).

Proof, following the six steps of the node:
1. If `X` is a scheme with the indicated ampleness, apply
   lem-trf-scheme-relative-ample-base-change to each `Tᵢ → T`. The equivalence
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence identifies ordinary and
   étale tensor pullbacks, proving the forward direction.
2. Conversely, the local ampleness gives quasi-compactness and separatedness by
   def-weil-pbc-ample-invertible-module, def-weil-finite-type-morphism and
   lem-trf-scheme-ample-canonical-proj-criterion. Scheme base change of quasi-compact
   maps and closed immersions gives the scheme-test properties. Descend them by
   lem-sfb-space-fpqc-qc-separated-descent, without absolute quasi-compactness.
3. Form the graded section algebra and its evaluation using
   lem-trf-graded-qc-section-algebra-construction and
   lem-trf-graded-evaluation-zariski-etale-comparison. The canonical map on its open
   generation locus is supplied by lem-trf-space-line-module-proj-map into the scheme
   relative Proj of lemma-nagata-relative-proj-exists.
4. Apply lem-sfb-space-flat-direct-image-base-change in every degree. On local tensors
   products map to the products of their images, and the unit maps to the unit. Thus
   the comparisons form a graded algebra isomorphism. The adjunction counit identifies
   its pulled-back evaluation with the local evaluation, and the scheme-site comparison
   identifies it with the ordinary scheme construction.
5. By lem-trf-scheme-ample-canonical-proj-criterion the local generation opens are all
   of the local schemes and their canonical maps are open immersions. The arbitrary
   pullback clause of lem-trf-space-line-module-proj-map identifies these opens with
   inverse images of the global generation open. Every field-valued point of `X` lifts
   after field extension to a member, using lem-weil-pbc-fpqc-covering-axioms and
   lem-trf-space-fibre-products-etale-covers. Thus every point lies in the generation
   open; its scheme tests are surjective open immersions, so this open is all of `X`.
6. The induced family over relative Proj is fpqc. Descend the local open immersions by
   lem-sfb-space-fpqc-open-immersion-descent. Hence `X` is an open subscheme of a
   scheme. The scheme-site evaluation comparison identifies the ordinary canonical
   map. Quasi-compactness and separatedness in scheme-test form become the scheme
   properties (the diagonal is closed, hence quasi-compact and quasi-separated).
   Apply the reverse canonical-Proj criterion to obtain ampleness on every affine
   base open. This proves the reverse implication and its schematicity clause. -/
theorem relative_ampleness_iff_fpqc_scheme_cover
    {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Over S) (f : X ⟶ schemeSpace T)
    (L : X.Modules) (hL : X.IsLineModule L) {I : Type v}
    (Tᵢ : I → Over S) (g : ∀ i : I, Tᵢ i ⟶ T)
    (hg : Presieve.ofArrows (fun i ↦ (Tᵢ i).left) (fun i ↦ (g i).left) ∈
      Scheme.fpqcPrecoverage T.left) :
    (∃ (Z : Over S) (a : schemeSpace Z ⟶ X) (p : Z ⟶ T),
      IsIso a ∧ a.hom.hom ≫ f.hom.hom = yoneda.map p ∧
      ∀ V : T.left.Opens, IsAffineOpen V →
        ∃ h : ((Scheme.Modules.tensorPullback (p.left ⁻¹ᵁ V).ι).obj
          ((schemeSpaceZariskiRestriction Z).obj ((moduleTensorPullback a).obj L))).IsInvertible,
          @Scheme.Modules.IsAmple (p.left ⁻¹ᵁ V).toScheme
            ((Scheme.Modules.tensorPullback (p.left ⁻¹ᵁ V).ι).obj
              ((schemeSpaceZariskiRestriction Z).obj ((moduleTensorPullback a).obj L))) h) ↔
    ∀ i : I, ∃ (Z : Over S) (a : schemeSpace Z ⟶ X) (p : Z ⟶ Tᵢ i),
      IsPullback a.hom.hom (yoneda.map p) f.hom.hom (yoneda.map (g i)) ∧
      ∀ V : (Tᵢ i).left.Opens, IsAffineOpen V →
        ∃ h : ((Scheme.Modules.tensorPullback (p.left ⁻¹ᵁ V).ι).obj
          ((schemeSpaceZariskiRestriction Z).obj ((moduleTensorPullback a).obj L))).IsInvertible,
          @Scheme.Modules.IsAmple (p.left ⁻¹ᵁ V).toScheme
            ((Scheme.Modules.tensorPullback (p.left ⁻¹ᵁ V).ι).obj
              ((schemeSpaceZariskiRestriction Z).obj ((moduleTensorPullback a).obj L))) h := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
