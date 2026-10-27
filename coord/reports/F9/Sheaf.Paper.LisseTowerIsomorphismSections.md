## What changed

Kept the statement of AlgebraicGeometry.Scheme.lisse_tower_isomorphism_sections unchanged.
Its proof constructs the actual derived Isom sheaves from etale finite-level data, applies
finiteRing_derived_local_constancy, constructs universal structured arrows from the supplied
Hom-set bijections, and constructs reduction on each etale generator by the unique universal factorizations.
Both inverse identities and naturality are proved by universality; the latter uses the
raw restriction-square coherence. Sheafification gives r_n, and the existing
sourceIsomorphism_normalized_presheaf_evaluation supplies its evaluation equation.
The evaluation is sourceDerivedIsoEvaluation conjugated by the quotient-linear model and
actual level comparisons. A proved private categorical lemma transports the raw square by
naturality and the two specified normalization identities, yielding exactly the required
constant-completion scalar square. No arbitrary choice of evaluation is made.

The proof also proves the finiteness of the completion quotients using the existing actual
quotient-map bijectivity, preserves the source cohomological bounds by exact constants,
and proves finite local constancy of their homology using the exact homology comparison.

Added Sheaf.Paper.LisseTowerEtaleDescent for the earlier raw descent step. Its theorem
has no supplied source transition or universal-source hypothesis. It asserts local
universality and coefficient restriction coherence for every algebraic source arrow. It supplies actual etale levels,
their normalization arrows and universality, and coefficient comparisons that respect
every algebraic source arrow. It constructs neither reduction on Isom sheaves nor
evaluation on weakly contractible objects. The raw datum is a structure with explicit
objects, functors and equations; its definitions contain no sorry and no existence witness
is chosen in a definition. Its use is existential elimination inside the item proof.

All added imports of the item are private proof imports. No other existing module,
statement, definition, visibility or public import changes.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.Scheme.lisse_tower_isomorphism_sections
(node lem-weil-pbc-lisse-tower-isomorphism-sections) with a complete assembly proof.

Added one hole: AlgebraicGeometry.Scheme.lisse_tower_etale_descent
(node lem-weil-pbc-lisse-tower-etale-descent). Its proof is exactly `by sorry` with
its source and full natural-language proof in its docstring. There are no other holes
in the delivery. This is a decomposition, with one upper hole closed and one earlier
descent hole added; it is not a net unconditional proof. The new statement is not the
original conclusion renamed: it omits all reduction maps and evaluated section squares,
and does not even take the supplied source transition maps. The Lean proof implements
the passage from etale levels to finite Isom sheaves, reduction, section evaluation and
the final specified scalar square using existing declarations.

Validation: clean server compilations passed for LisseTowerEtaleDescent in
31.6 seconds and LisseTowerIsomorphismSections in 21.5 seconds, with no warnings.
The original theorem signature was compared verbatim and is unchanged. Both node
proof-dependency lists equal the unions of their proof-step dependencies, and the
new theorem attachment matches its Lean source. Generated injectivity, size and
constructor-index helpers for the new record are disabled to avoid expensive
unused generated declarations; local irreducibility keeps derived coefficient
functors from unfolding during elaboration. All profiling options are removed.

## No longer needed

No existing public import was removed and no module is withdrawn. No global pruning
is claimed. The original direct dependencies
prop-weil-pbc-site-comparison-finite-level, def-weil-pbc-proetale-modules,
lem-weil-pbc-comparison-pullback and def-weil-pbc-bounded-constructible-tower
are now confined to the strictly earlier etale descent step; they remain needed there.

The proof uses the already stated source-isomorphism-normalized-presheaf-evaluation.
The generic NormalizedDerivedIsomorphismSectionReduction module could not be imported:
it reaches this item through DerivedScalarExtensionLocalSystems, EtaleProEtaleScalarMate
and the integral projection-formula branch. The delivery constructs the required presheaf
reduction directly instead of changing any shared module. It does not use
Sheaf.Paper.CompatibleFiniteDerivedTrivializations or the perfect-object-specific
FinitePerfectAdicIsomorphismPresentation; none is withdrawn.

The original ringed-topoi-derived-tensor-pullback dependency is unnecessary for this
route: the raw descent uses coefficient-restriction mates and scalar adjunctions,
while the existing normalized presheaf evaluation supplies the required section square. No monoidal tensor-pullback theorem is applied here. Its node is removed from
the item's direct proof dependencies, with no claim that all other consumers disappear.

## Where the brief, the DAG or earlier work was wrong

The original named dependencies did not directly state descent of the actual finite
ringed-coefficient levels with their normalization arrows and the specified completed
scalar comparisons. The new descent theorem states this exact earlier step, independently
of the supplied source transition system. The remaining two original proof steps are
implemented by universal factorizations and the existing presheaf evaluation API, not
restated as new holes. The import cycle in the generic reduction API is recorded above. No target or intermediate statement is weakened or disputed.

Edge cases checked mathematically: an empty base uses the empty cover and has no
geometric points; zero complexes have their identity local isomorphisms. The zero ideal
makes consecutive quotient maps identities and the construction reduces to ordinary
locally constant derived objects. No finite Tor amplitude or perfectness of K_n is
assumed: these are not consequences of bounded finite cohomology over a finite ring.
No surjectivity of the reduction maps on Isom sheaves is assumed or asserted.

## New nodes

lem-weil-pbc-lisse-tower-etale-descent records the raw etale finite-level descent,
actual normalization arrows, their local universality and restriction coherence, and
comparison naturality for all algebraic arrows.
It also attaches the completion quotient abbreviations and the explicit algebraic
scalar-compositor arrow used in its statement. The node names the classical descent,
coefficient comparison and derived Isom comparison tools. Its blueprint source remains
the existing proper-base-change amplification route; no unit statement or step changes.

The item node's proof, proof_deps and proof_origin now follow the actual Lean proof.
No change record is required because no existing interface changes.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
