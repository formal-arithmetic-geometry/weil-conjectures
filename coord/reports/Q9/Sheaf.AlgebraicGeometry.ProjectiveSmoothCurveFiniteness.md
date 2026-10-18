## What changed

Repaired the returned import cycle in the retained delivery at head `8a9794dec`.
The assigned theorem now has a complete proof from proper base change, curve Betti
cardinalities, and the finite-stalk constructibility criterion. Its signature,
public imports, visibility, and definitions are unchanged. Only the assigned Lean
module and its proof-plan node are changed; no other module needs adaptation.

The proved private helper `AlgebraicGeometry.constant_prime_stalk_equiv` composes
the geometric-fibre base-change isomorphism with constant-sheaf pullback and the
module/abelian cohomology comparison. In the main proof, invertibility passes to
residue fields through global evaluation. The Betti lemma identifies the actual
cardinal of each canonical geometric stalk with a natural number, proving both
finiteness and the required cardinality-locus identity. Comparing geometric points
over the same base point extends finiteness to every separably closed point.

The final step uses the existing module-valued realization of
`fin4-lem-stalk-constructibility-criterion`, namely
`Scheme.isConstructibleSheaf_iff_isConstructible_card` in
`WeilConjectures.ConstructibleSheaf.Noetherian`. This directly produces module
constructibility, avoiding a separate conversion of abelian trivializations.
The proved comparison `isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`
then gives exactly the assigned conclusion.

The single-file remote compile passed cleanly within the 60-second limit. All proof imports
were checked for reverse reachability with `tools/import_direction.py may`;
the forbidden source projective-curve finiteness module is absent. The unit
`sk-prop-sf-cbc` has empty `realized.statement` and `realized.steps`, and this
implementation follows the assigned node's mathematical route.

## Proved and sorry left

Closed 1 of the assigned module's 1 original holes:
`AlgebraicGeometry.isConstructibleEtaleModuleSheaf_higherDirectImage_constant_of_projective_smooth_curve`
(node `thm-fin-projective-smooth-curve-finiteness`). The private helper is also
proved. Zero `sorry` remains in the delivered Lean module; zero holes are added,
and zero statements are split off. The existing imported theorem
`AlgebraicGeometry.projective_curve_betti_cardinalities` still has its pre-existing
hole; this delivery proves the assigned theorem from that stated dependency.
It does not claim a proof free of all transitive sorry dependencies.

No nonempty-base or nonempty-fibre assumption is introduced. The Betti lemma's
Cardinal.mk equality handles empty fibres (cohomology of cardinality one), and
all geometric-stalk arguments are quantified over existing points. The empty
base therefore requires no chosen point. All natural degrees and the original
universes are preserved. Data from existential comparison theorems is used only
inside proofs, and no new object is chosen in a definition.

## No longer needed

Relative to current main, removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.StalkConstructibilityCriterion`: use the existing
  module-valued realization of the same criterion in
  `WeilConjectures.ConstructibleSheaf.Noetherian`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: the unchanged statement
  import `WeilConjectures.AlgebraicGeometry.Morphisms.Projective` already supplies
  the projective-implies-proper instance used here.

Relative to the returned delivery, removed:

- `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve`, whose
  import closure returns to the assigned module. The proof no longer applies
  `Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_of_smooth`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`:
  the proof uses the stated bounded-below geometric-fibre formula directly.
- `WeilConjectures.ConstructibleSheaf.Pullback`: no transport of constructibility
  along the old derived-functor comparison is used.

The original proper-base-change and Betti-cardinality dependencies are retained.
The stalk-criterion node remains needed through its existing module-valued source
realization. No mathematical dependency of the original argument is pruned, and
no global unreachability is claimed for these removed direct imports. The node's
`proof`, `proof_deps`, and `proof_origin` now describe the actual proof, and its
original accepted `tool_uses` are preserved.

## Where the brief, the DAG or earlier work was wrong

The retained proof reused the existing source theorem without checking its full
import closure. That closure passes through general proper/projective finiteness,
projective-line constructibility, and projective-curve reductions back to the
assigned theorem, exactly the cycle identified in the return. This repair removes
that theorem and proves the actual argument instead; it is not an unchanged push
or a rebase alone.

The original DAG proof is mathematically usable. The source library already
proves its stalk criterion directly for module sheaves over a finite ring; using
that realization avoids extra coefficient-structure glue. The geometric-fibre
formula and Betti lemma use different coefficient categories, resolved here by the
already proved `nonempty_etaleModuleCohomology_forgetIso` and constants comparison.
No definition or statement repair is required. The existing namespace commands
are preserved; proof names from `CategoryTheory.Limits` are qualified explicitly.

Searches were repeated through leanfinder, loogle and Mathlib grep, and project
`rg` located the existing module-valued criterion and cohomology comparison.
There are no new nodes, no change records, and no forced consumer adaptations.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
