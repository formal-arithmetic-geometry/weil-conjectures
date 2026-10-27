## What changed

Replaced `AlgebraicGeometry.Scheme.lisseNormalizedTower_local_models`'s single
`sorry` by a complete assembly proof. Its signature and original public imports
are unchanged. The proof obtains an algebraic pseudo-coherent derived object on
a covering sieve, chooses an exact relative completed module realization,
truncates a finite-free representative to finite terms in precisely `[a,b]`,
and realizes it termwise. One derived isomorphism induces all finite reduction
isomorphisms. Naturality of the scalar-extension adjunct proves every forward
semilinear transition square. A private helper transports relative finite lissity
through module-sheaf isomorphisms.

Extracted the already proved finite truncation argument as the public theorem
`AlgebraicGeometry.Scheme.exists_boundedFinite_model` in
`Sheaf.Paper.BoundedFinitePseudoCoherentModel`. It permits arbitrary integer
endpoints, including an empty interval, and does not assert that the first term
is projective. The previously proved normalization transport, Roos, algebraic
reconstruction and completion-quotient helpers remain private in the new
geometric subproblem module; their proofs were retained.

Added two strictly separate outstanding obligations: exact relative realization
of modules over the completion, and a geometric algebraic-derived presentation
of the lisse normalized tower. The former has no input tower or complex. The
latter produces an object in the algebraic derived category with compatible
derived reductions, and produces no bounded sheaf complex or termwise lissity.
The assembly uses both, the proved finite truncation, exact-functor localization,
and an explicit naturality argument. No object is defined by choosing an
arbitrary witness from an unproved existence theorem.

## Proved and sorry left

One original hole closed:
`AlgebraicGeometry.Scheme.lisseNormalizedTower_local_models`
(node `lem-weil-pbc-lisse-normalized-tower-local-models`).

Two holes added, each with its complete source-based proof in its docstring:

- `AlgebraicGeometry.Scheme.relative_completed_module_realization_exact`
  (`lem-weil-pbc-relative-completed-module-realization-exact`).
- `AlgebraicGeometry.Scheme.lisse_tower_algebraic_derived_presentation`
  (`lem-weil-pbc-lisse-tower-algebraic-derived-presentation`).

This is a decomposition, not a completed foundational proof: one original hole
closed, two lower holes added, net -1 before any change in the target closure.
The item module has zero `sorry`; the packet has exactly these two. The extracted
`exists_boundedFinite_model` and all retained private helpers are proved.

The new statements include the zero coefficient ring and ideals zero and top.
The exact realization statement permits any scheme morphism and handles the
zero module. In the geometric statement the empty scheme uses the empty covering
sieve; no nonempty geometric point is requested on an empty component. The
algebraic interval argument uses finite Mittag--Leffler to retain the lower bound,
with no finite Tor assumption. The scalar projection equations fix both scalar
maps uniquely; the universal quantification over exact realizations does not
permit an arbitrary unrelated coefficient functor.

## No longer needed

No mathematical DAG dependency or library module is claimed globally prunable:
the original geometric dependencies remain on the new geometric obligation.
The item itself now imports only its three assembly dependencies and the
Noetherian completion theorem for its proof. Algebraic-helper imports are retained
where their proved helper bodies now live.

The following original proof imports are absent from the packet because no
current Lean proof body uses them (their mathematical nodes remain where needed
in the geometric presentation's proof plan):

- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy`
- `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.Paper.CompletedConstantFiniteComplexRealization`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.FiniteCoefficientDerivedOriginPresentation`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient`

No library file is withdrawn. In particular the quarantined source is retained;
the current `lean/` source was present and byte-identical to its archive when read.

## Where the brief, the DAG or earlier work was wrong

The module had extensive proved algebraic helpers but its sole public theorem
still had no assembly proof. The old proof paragraph combined geometric derived
origin, simultaneous trivialization, algebraic effectivity, finite truncation,
relative coefficient realization and transition naturality without a Lean
interface between those steps. This packet records the missing interfaces and
implements truncation and the assembly. The existing finite-complex realization
only states exactness on finite modules; inducing an unbounded derived functor
requires exactness on all modules. The new module-level exactness obligation
states this explicitly using the completed-constant flatness theorem (093M)
applied to the Noetherian completed ring.

The `coord/rework.tsv` row names the earlier transitive
`Sheaf.AlgebraicGeometry.SfP1ChartExchange` build failure. The original item has
since been restored in the shared source, so there is no deletion or empty-module
replacement in this packet. No shared definition or existing consumer interface
is changed, and no forced adaptations are needed.

## New nodes

`lem-weil-pbc-bounded-finite-pseudocoherent-model` attaches the proved
Noetherian finite truncation argument in its own module.

`lem-weil-pbc-relative-completed-module-realization-exact` states the missing
exact relative module realization with the actual evaluation/projection scalar
maps, and finite-module relative adic lissity.

`lem-weil-pbc-lisse-tower-algebraic-derived-presentation` isolates the derived
algebraic effectivity and compatible finite reductions. It retains the old
geometric proof dependencies and the already proved algebraic helpers.

All three inherit the proper-base-change unit and amplification (c) blueprint
ancestor. Mathlib searches were run through `msearch.py`; the whole-blueprint
searches found no matching bounded finite representative or completed flatness
node. No change record is required: only the item, its node and new modules/nodes
are changed.

Validation: all four modules compile with `lcompile.py --all`; the proved finite
model, module realization, geometric presentation and main assembly respectively
took 2.5 s, 6.5 s, 16.0 s and 10.7 s in the initial successful run.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
