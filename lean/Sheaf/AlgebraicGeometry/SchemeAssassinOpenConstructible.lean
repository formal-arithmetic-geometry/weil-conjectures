/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.AlgebraicGeometry.RelativeAssassin
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.Topology.Constructible
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.FiniteType
import Sheaf.AlgebraicGeometry.FinitePresentationFamilyDescent
import Sheaf.AlgebraicGeometry.FibreProductLimit
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.FinitePresentationModuleMapDescent
import Sheaf.AlgebraicGeometry.FibreAssassinContainmentBaseChange
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import Sheaf.AlgebraicGeometry.GenericFibreAssassinContainmentSpreads
import Sheaf.AlgebraicGeometry.NoetherianConstructibleSubsetCriterion

/-! # Constructibility of fibre-assassin containment over an affine base

Source: Stacks Project, More on Morphisms, Tag 05KR,
`lemma-relative-assassin-constructible`, its affine-base reduction
(blueprint: lem-sfb-scheme-assassin-open-constructible).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- For a finitely presented morphism to an affine base and a finitely presented
quasi-coherent module, containment of the fibre assassin in an open subscheme
quasi-compact over the base is a constructible condition on base points.
`F.IsFinitePresentation` includes quasi-coherence and precisely means locally having
an exact presentation by two finite free modules. The fibre of the open subscheme
is the inverse image of `H` under the scheme-theoretic fibre projection.

Source: Stacks Project, More on Morphisms, Tag 05KR,
`lemma-relative-assassin-constructible`, its affine-base reduction
(blueprint: lem-sfb-scheme-assassin-open-constructible).

Proof:
1. Write B = Spec A and approximate A by its finitely generated integer subalgebras
   [lemma-nagata-noetherian-inverse-system-affine]. Their spectra are qcqs
   [lem-weil-pbc-affine-scheme-qcqs], and the rings are Noetherian by
   [lem-trf-mvpolynomial-noetherian] and [lem-weil-pbc-finite-type-algebra-noetherian].
2. Descend T to a finitely presented model over one such ring
   [lem-weil-pbc-finite-presentation-family-descent]. Its later base changes are qcqs
   and finitely presented [lem-weil-pbc-qcqs-morphism-permanence], with affine
   transitions [lem-weil-pbc-affine-morphism-permanence], and have limit T by
   [lem-kun-fibre-product-limits].
3. Since B is affine and H -> B is quasi-compact, H is quasi-compact
   [def-weil-finite-type-morphism]. Descend H by [pqf-lem-limit-qc-open-descends],
   then descend F by clause (1) of [lem-pc-fp-module-map-descent]. Increasing the
   index gives a common model (T_i, F_i, H_i) over a Noetherian affine B_i.
4. The containment locus E is exactly the inverse image of the model locus E_i,
   point by point, by [lem-sfb-fibre-assassin-containment-base-change]. Finite
   presentation gives the locally finite type and finite type hypotheses there.
5. An irreducible closed subset of B_i is V(p) for a prime p by
   [lem-weil-pbc-spec-irreducible-closed-subsets-primes]. Give it its reduced
   induced structure [lem-weil-pbc-reduced-induced-closed-subscheme]. Base change
   the model triple to it. Finite presentation persists by
   [lem-weil-pbc-qcqs-morphism-permanence], quasi-coherence by
   [lem-weil-pbc-module-pullback-quasi-coherent], and module finite presentation by
   [lem-pc-tensor-pullback-finite-presentation]. The locus restricts to E_i intersect
   V(p) by [lem-sfb-fibre-assassin-containment-base-change].
6. At the generic point of each such irreducible closed subscheme, use
   [lem-sfb-generic-fibre-assassin-containment-spreads] in the containment case and
   [lem-sfb-generic-fibre-assassin-noncontainment-spreads] in the other case. These
   give a nonempty relative open wholly inside or outside E_i. The criterion
   [lem-trf-noetherian-constructible-subset-criterion], with the single Noetherian
   affine chart B_i, proves E_i constructible.
7. Pull back E_i along B -> B_i by [lem-pur-scheme-constructible-preimage] and use
   Step 4. For empty B the locus is empty and hence constructible. -/
theorem isConstructible_fiber_associatedPoints_subset_open
    {T B : Scheme.{u}} (g : T ⟶ B) [LocallyOfFinitePresentation g]
    [QuasiCompact g] [QuasiSeparated g] [IsAffine B]
    (F : T.Modules) [F.IsFinitePresentation]
    (H : T.Opens) [QuasiCompact (H.ι ≫ g)] :
    Topology.IsConstructible
      {b : B | associatedPoints ((tensorPullback (g.fiberι b)).obj F) ⊆
        (g.fiberι b) ⁻¹' (H : Set T)} := by
  sorry

end AlgebraicGeometry.Scheme.Modules
