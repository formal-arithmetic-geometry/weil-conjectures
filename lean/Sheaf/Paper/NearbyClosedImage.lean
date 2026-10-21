/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.OrgogozoInductionData
public import Sheaf.Paper.OrientedNearbyCycles
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.TraceFormula.OrientedPointCohomology
import Sheaf.Paper.OrientedProductPointsConservative
import Sheaf.AlgebraicGeometry.CohomologyPullbackCanonicalArrows
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Sheaf.Paper.StrictHenselizationFunctoriality

/-!
# Nearby-cycle comparison through a closed image

Source: Orgogozo, Modifications et cycles proches sur une base générale, Lemma 3.2.2,
pp. 7--8 (blueprint: lem-trf-nearby-closed-image).

The constructibility of the cohomology sheaves of `K` is tested, as in
`lem-trf-orgogozo-good-modification`, on their sections with the canonical constant
scalars (the sheafification unit of the constant ring presheaf), compared with a recorded
constructible small-etale module sheaf over the `AsSmall` site equivalence. That
construction is written out in the hypothesis rather than imported from
`Sheaf.Paper.OrgogozoGoodModification`, whose node uses this lemma in its proof.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Orgogozo AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.Orgogozo

/-- If a proper morphism factors through a closed subscheme of a Noetherian base, the
universal truncated nearby-cycle comparison `P_r` and full Ψ-goodness descend from the
closed subscheme to the ambient base. Source: Orgogozo, Lemma 3.2.2, pp. 7--8, with the
coefficient extension of Illusie, Theorem 1.6.1 (blueprint: lem-trf-nearby-closed-image).

Proof (the DAG proof, step by step):
1. If `nΛ = 0`, `ℤ/n → Λ` is unital; the tube and sections formulas used below allow any
commutative ring, and the faithful exact forgetful functor of
[lem-weil-pbc-module-sheaves-colimits-forgetful] detects cone-cohomology vanishing. Fix
`B → S`, `u : B' → B`; put `E = F ×_S B`, `E' = F ×_S B'`, `Y = X ×_S B`, `Y' = X ×_S B'`,
`L = K|_Y`. The maps `E → B`, `E' → B'` are closed immersions
[lem-weil-pbc-closed-immersion-base-change], and `Y = X ×_F E`, `Y' = X ×_F E'`
[def-pc-fibre-product], compatibly with all projections.
2. For a closed immersion `Z → W` and a geometric point `a` of `Z`,
[lem-trf-closed-immersion-strict-localization-cartesian] gives the canonical Cartesian
identification `Z_(a) ≅ Z ×_W W_(a)` through the local map of
[lem-weil-pbc-strict-henselization-functoriality](3); composites of these local maps are
the local maps of the composites, and a specialization `B_(b) → B_(a)` with `b ∈ E`
restricts to `E_(b) → E_(a)`.
3. For an oriented point `(x', b', c')` of `V_{g'}` with image `(x, b, c)`, the stalks of
the comparison are `RΓ(M, L|_M)` and `RΓ(M', L|_{M'})`, `M = Y_(x) ×_{B_(a)} B_(b)`,
`M' = Y'_(x') ×_{B'_(a')} B'_(b')` [lem-trf-oriented-point-cohomology]; these points are
jointly conservative [lem-trf-oriented-product-points-conservative], so it suffices to
show the cone vanishing at them.
4. If `b' ∉ E'`, then `b ∉ E`, `E ×_B B_(b)` and `E' ×_{B'} B'_(b')` are empty, so
`M = M' = ∅` and the stalk comparison is `0 → 0`.
5. If `b' ∈ E'`, then `b ∈ E`; with `N = Y_(x) ×_{E_(a)} E_(b)` and
`N' = Y'_(x') ×_{E'_(a')} E'_(b')`, step 2 and reassociation give `M ≅ N`, `M' ≅ N'`,
compatibly with the projections to `Y` and with `M' → M`, `N' → N`.
6. These identifications identify the comparison arrows: by [def-trf-oriented-nearby-cycles]
`β` is the mate followed by the counit, and [lem-weil-pbc-mate-pasting](1),(2),
[lem-weil-pbc-cohomology-pullback-derived-unit](2) and
[lem-pe-left-module-derived-evaluation-forget] identify both stalk arrows with the
cohomology pullback along `M' → M ≅ N' → N`.
7. Assume `P_r(f_F, K)` [def-trf-orgogozo-induction-data], applied to `E → F` and
`E' → E`: the cone for `Y → E` has `H^i = 0` for `i ≤ r`. By steps 4--6 the ambient stalk
cones vanish in these degrees at every oriented point; conservativity gives
`H^i Cone(β_{g,u,L}) = 0` for `i ≤ r`. As `B → S` and `B' → B` were arbitrary, `P_r(f, K)`.
8. If `(f_F, K)` is Ψ-good, apply steps 1--6 with `B = S`, `E = F`, `E' = F ×_S B'` for
any `B' → S`: the ambient comparison is an isomorphism at the points over `E'` and `0 → 0`
elsewhere, hence an isomorphism; so `(f, K)` is Ψ-good.
-/
theorem nearbyClosedImage
    {X S F : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [IsProper f]
    (i : F ⟶ S) [IsClosedImmersion i]
    (fF : X ⟶ F) (hfac : fF ≫ i = f)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasInvertibleExponent Λ S]
    (K : EtaleDerived X Λ)
    (hKb : IsBounded (etaleDatum X) (Coeff Λ) K)
    (hKc : ∀ q : ℤ,
      ∃ Fq : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ)),
        Scheme.IsConstructibleEtaleModuleSheaf Fq ∧
        Nonempty ((PresheafOfModules.forgetToPresheafModuleCat
            (op (⊤_ (EtaleSite.{u, u + 1} X))) terminalIsTerminal.op).obj
          ((PresheafOfModules.restrictScalars
            (Functor.whiskerRight
              (toSheafify (etaleTopology.{u, u + 1} X)
                ((Functor.const (EtaleSite.{u, u + 1} X)ᵒᵖ).obj
                  (CommRingCat.of (Coeff.{u, u + 1} Λ))))
              (forget₂ CommRingCat RingCat))).obj
            ((DerivedCategory.homologyFunctor
              ((etaleDatum.{u, u + 1} X).modules (Coeff Λ)) q).obj K).val) ≅
          (AsSmall.down : EtaleSite.{u, u + 1} X ⥤ X.Etale).op ⋙ Fq.obj)) :
    (∀ r : ℤ,
      UniversalTruncatedComparison fF Λ ⟨K, hKb⟩ r →
        UniversalTruncatedComparison f Λ ⟨K, hKb⟩ r) ∧
      (IsPsiGood fF Λ K → IsPsiGood f Λ K) := by
  sorry

end AlgebraicGeometry.Orgogozo
