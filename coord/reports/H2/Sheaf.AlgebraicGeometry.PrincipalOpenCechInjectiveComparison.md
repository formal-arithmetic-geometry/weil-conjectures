## What changed

Proved `AlgebraicGeometry.principalOpenCech_injective_comparison` from the existing
functorial degreewise-injective resolution, Mathlib's K-injective homotopy-equivalence
criterion, and one new coordinate-construction theorem. The main module explicitly
constructs additive section evaluation, the section complex of the replacement,
the isomorphism determined by σ, and its comparison map. It proves the augmentation
square directly in Lean by cancelling τ₁ and using restriction naturality after
coefficient-degree transport. It proves the section comparison map is a
quasi-isomorphism by applying section evaluation to the homotopy equivalence.

Added proof-only imports of `PrincipalOpenCechCoordinateMap`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`,
and `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`.
All existing signatures and public imports are unchanged. No forced adaptations.
Updated the item's proof route and dependencies in its node.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.principalOpenCech_injective_comparison`
(node `lem-sc-principal-open-cech-injective-comparison`). The item has no direct sorry.

Added one hole: `AlgebraicGeometry.principalOpenCech_coordinate_map_exists`, in
`Sheaf.AlgebraicGeometry.PrincipalOpenCechCoordinateMap`
(node `lem-sc-principal-open-cech-coordinate-map`). This is a decomposition: one hole
closed, one added, net zero. Its statement fixes the coefficient complex I and map g,
and takes the target section complex K₁ as input. It asserts only the Čech
coordinate construction and component formula for b. It neither takes a source
section complex, source augmentation or section comparison map as input nor
asserts the comparison square, injectivity or a quasi-isomorphism.
Thus it is strictly the second part of the original argument, not a renamed copy.
The new theorem's proof is exactly `by sorry`, with the full coordinate argument in
its docstring and node.

Both modules compile together through lcompile.py without warnings. Edge cases
checked against the formulas: for r=0 there are no nonempty subset coordinates and
T₁ is zero; singletons have no nonempty deletion; pairs have equal restrictions with
opposite signs; larger subsets have zero augmentation coordinates. Repeated opens,
empty intersections, unbounded complexes, and the zero coefficient map require no
extra hypotheses. No definition selects data from an unproved existence theorem;
the existential witnesses are used only inside the public theorem proof.

## No longer needed

No existing imports were removed. The item no longer needs the full proposition
`prop-pur-kinjective-resolutions-exist` or its wrapper module
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`: the two existing underlying
results provide exactly the needed resolution without the unrelated generator
conclusion. The DAG now cites `lem-pur-ringed-site-grothendieck-abelian` and
`lem-pur-kinjective-degreewise-existence` directly. These nodes are retained.
`lem-weil-pbc-kinjective-hom-derived` is retained for the Mathlib equivalence criterion.
No unit statement or unit proof step is bypassed. This is only local pruning; other
users may still need the wrapper proposition and module.

## Where the brief, the DAG or earlier work was wrong

Step 2 of the original node contains substantial total-complex construction and
naturality glue but no named dependency for it. The new coordinate node isolates it.
The existing `PrincipalOpenCechTotal` does have proved construction results, but it
imports `PrincipalOpenCechHomologyInjective`, which imports this item. It cannot be
imported here without a cycle. Moving that interface would require coordination or
an authorized interface change; this delivery makes neither. The new theorem is a
coordinate bridge for that eventual restructuring, not a second public definition
of the total functor. Source Tag 08C1 explicitly omits the compatibility verification;
the new node marks its expanded coordinate proof as written by an agent.
The local copy lacks the downloaded literature source; the cited Stacks Tag 08C1 was
read online, and equation (the project server) (Tag 08C0).

## New nodes

`lem-sc-principal-open-cech-coordinate-map`, at
`dag/nodes/sec-picard-framework/lem-sc-principal-open-cech-coordinate-map.json`, states
the arbitrary-coefficient signed subset-total, its singleton augmentation, and
the coefficient-map coordinates.
Its single module is `lean/Sheaf/AlgebraicGeometry/PrincipalOpenCechCoordinateMap.lean`.
It inherits the item's chapter, unit and blueprint ancestor. LeanSearch was unavailable;
LeanFinder, Mathlib grep, the library search and the blueprint search found no directly
usable statement. The remaining work is the finite signed coordinate construction,
not the comparison square, existence of an injective replacement or preservation
of its section homotopies.
There are no statement changes and no change records.

## Second reading by H2

1. **Interface unchanged — pass.** Read the complete diff of each delivered
   module against the repository. The sole existing public theorem signature is
   byte-for-byte identical, checked from `theorem` through the final conclusion
   before `:= by`. Its docstring, visibility and original public imports are
   unchanged. The three added imports are proof-only. No existing definitions or
   other modules are modified; the section functor and its helpers are private.
   The new coordinate statement is in its own new module and has its own node.

2. **Proof and axioms — pass as a decomposition.** Both modules compiled together
   using `lcompile.py --all`, without errors or warnings. Scanned both complete
   sources: the only `sorry` is the named coordinate theorem with exactly `by
   sorry`; there is no forbidden declaration or hollow definition. A scratch copy
   with `#print axioms` compiled successfully. The private section functor,
   additivity instance and restriction-naturality theorem use only `propext`,
   `Classical.choice`, and `Quot.sound`. Both public theorems additionally use
   `sorryAx`, consistently with the one reported open coordinate theorem. The
   resolution is the existing constructed functor, and the section complex is
   constructed explicitly. Existential coordinate witnesses are eliminated only
   within the theorem proof; no definition chooses arbitrary data from the new
   unproved existence statement. This closes one upper hole and adds one lower
   hole, net zero, and is not an axiom-free proof of the original theorem.

3. **Split statement — pass.** Independently checked the coefficient degrees,
   restriction directions, deletion signs, augmentation and coefficient-map
   formula. For vertical-horizontal cross terms the signs are
   `(-1)^(card S - 1)` and `(-1)^(card S - 2)`; for two horizontal deletions the
   larger index changes position by one upon deleting the smaller. Singleton
   augmentation has no horizontal term, and the two restrictions into a pair
   cancel. Exhaustively checked these sign and integer-degree identities for
   subsets of `Fin r`, `0 <= r <= 6`, with total degrees from -3 through 3.
   For `r=0` the subset product is zero; zero coefficient morphisms, repeated
   opens, empty intersections and unbounded complexes require no new assumption.
   The lemma does not restate the original: it constructs only the target total,
   its augmentation and the coordinate map for fixed arbitrary `I,g,K₁,σ₁`.
   The injective replacement, section quasi-isomorphism and commutative square
   are separate proved steps. Its docstring and node explain all parts of the
   remaining construction. Independently searched LeanFinder, Loogle and Mathlib
   grep with double-complex/totalization and coefficient-morphism queries, and
   searched the library with functoriality/naturality and subset signs. Generic
   `HomologicalComplex₂.total.map` presupposes the bicomplex; it does not discharge
   this coordinate construction. The existing concrete `PrincipalOpenCechTotal`
   contains relevant constructions but imports `PrincipalOpenCechHomologyInjective`,
   which imports this item, so using it here creates a cycle. Other subset
   comparison statements identify an already supplied total and do not construct
   the required A-linear target total and coefficient map. The coordinate hole
   cannot be closed in a few minutes from a directly applicable existing lemma.
   Read Stacks [Tag 08C1](https://stacks.math.columbia.edu/tag/08C1) and
   [Tag 08C0](https://stacks.math.columbia.edu/tag/08C0); the expanded coordinate
   argument is correctly attributed to an agent, since the source omits the
   compatibility verification.

4. **Route and pruning — pass.** Read the original proof dependencies, their Lean
   records and the unit `sk-thm-picard-duality`. The existing source-library
   Grothendieck and degreewise-injective resolution results are used directly;
   Mathlib's K-injective quasi-isomorphism criterion supplies the homotopy
   equivalence, and additive section evaluation preserves its homotopies.
   Naturality proves the augmentation square directly. No shorter usable route
   was found. Every added import serves these proofs, and the public imports
   supply `moduleRings`, affine module sections, and the K-injectivity statement.
   The only removed old proof dependency is
   `prop-pur-kinjective-resolutions-exist`, fully listed under No longer needed;
   `lem-weil-pbc-kinjective-hom-derived` is retained. No existing import is
   removed, and no globally unreachable module is claimed. The unit's realized
   statement and step lists are empty; none of its recorded nodes or steps is
   bypassed or changed.

5. **DAG agreement — pass.** The existing node changes only `proof`, `proof_deps`
   and `proof_origin`, and its three proof steps describe the Lean reduction.
   The new node supplies all required source, statement-dependency, creation,
   blueprint, chapter, unit, search and Lean fields. Checked its Lean statement
   verbatim against the new theorem signature. Its proof steps describe the
   remaining coordinate construction, with no fictitious proved dependency.

Second-reading changes: added the independent successful Loogle total-map search
and its limitations to the new node, and this complete review to the report.
The Lean proofs and statements required no repair. Removed the scratch axiom copy
before delivery. Holes closed/added and local dependency pruning remain exactly as
reported above.
