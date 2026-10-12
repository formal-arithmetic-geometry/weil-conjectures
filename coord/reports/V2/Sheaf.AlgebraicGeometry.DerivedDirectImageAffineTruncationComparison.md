## What changed

Proved `AlgebraicGeometry.exists_isIso_schemeHigherDirectImage_truncGE_over_affine`
in `Sheaf.AlgebraicGeometry.DerivedDirectImageAffineTruncationComparison`, preserving
its complete statement and existing docstring. The proof follows Tag 08D5: restrict to
an affine open, apply the existing uniform bound, and transport the canonical projection
through natural comparisons for restriction, truncation and homology. A proved private
helper transports quasi-coherent presentations through `Scheme.Modules.overEquiv`; its
argument is the existing private helper of `CoherentFiniteTypeLocallyNoetherian`.
The local derived categories use `HasDerivedCategory.standard`; the original two
localization choices and universes are untouched. Updated the node's proof and direct
proof dependencies to describe the Lean argument. The heartbeat settings account for
elaboration through the exact restriction and site equivalences; compilation stays under
60 seconds.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.exists_isIso_schemeHigherDirectImage_truncGE_over_affine`
(node `lem-pc-derived-direct-image-affine-truncation-comparison`).
No `sorry` remains in the delivered module. No new hole or public intermediate statement
was added; the new private quasi-coherence helper is fully proved. The proof uses the existing uniform bound and open-restriction theorems; their
remaining transitive holes remain the responsibility of their own items. This is a proof
from existing declarations, not a decomposition into new holes.

## No longer needed

Removed direct proof imports `Sheaf.Algebra.Homology.KInjectiveRestrictOpen` and
`Sheaf.AlgebraicGeometry.DerivedCategory`. The latter is already supplied by the public
statement imports. Removed the direct proof dependency
`lem-sc-derived-k-injective-restrict-open`: the open-restriction theorem supplies the
whole natural comparison, including its K-injective justification. That node and module
are still needed transitively by open restriction; no entire module is claimed to have
left the targets' closure. All other planned dependencies remain used, and the unit
route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The local `literature/stacks-project/perfect.tex`
is absent on this machine; I checked the source argument on the official
[Stacks Project Tag 08D5](https://stacks.math.columbia.edu/tag/08D5) page instead. The DAG explicitly requested the K-injective
restriction lemma although its consequence is already packaged in the natural
open-restriction theorem; the direct dependency was redundant. In Lean, the exact-functor
truncation isomorphism runs from D(RX)(τ_GE E) to τ_GE(D(RX) E), so its inverse component
is the factorization in `π_descTruncGE`. Recording that orientation makes transport of
the actual canonical projection explicit.


## Second reading by V2

1. PASS — Compared the complete module against the repository with `diff` and checked
   the existing theorem signature byte for byte by a string comparison. Its hypotheses,
   conclusion, universes, and docstring are unchanged. There are no new definitions or
   statement changes, and no change record is required. Only this module and the existing
   node's proof fields are delivered.
2. PASS — Independently compiled the module with `lcompile.py`: no errors or warnings,
   25.5 seconds. A scratch copy with `#print axioms` compiled in 23.1 seconds. The public
   theorem uses only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from existing
   open dependencies. The private helper uses only the three permitted standard axioms.
   No `sorry`, forbidden axiom declaration, unsafe code, or hollow definition appears in
   this module. Local standard derived categories are actual constructions. The chosen
   open-restriction isomorphism is used solely inside a proof to transport `IsIso` by
   naturality; no data definition or assertion depending on an arbitrary witness is
   exported. The uniform bound is eliminated directly to prove an existential proposition.
3. PASS — No statements were split off and no new holes or nodes were added. Read the
   private helper against the identical proved helper in
   `CoherentFiniteTypeLocallyNoetherian` and the general Mathlib preservation theorem.
   That existing helper is private, so it cannot be imported and applied. The local proof
   uses preservation along a site equivalence, without nonemptiness or finite-presentation
   assumptions; it also covers a zero module and an empty open.
4. PASS — Read the argument from the target down through the uniform-bound and
   open-restriction declarations. Checked the inverse orientation of the exact-functor
   truncation comparison and its defining `π_descTruncGE` equation, both natural-isomorphism
   transports, and reflection of isomorphisms by `eY`. The canonical projection is the one
   in the unchanged statement, for arbitrary integer q and arbitrary original localization
   universes. Reviewed Stacks [Tag 08D5](https://stacks.math.columbia.edu/tag/08D5), final
   paragraph. Independent searches by `rg` for truncation/isomorphism and quasi-coherence/site
   equivalence, and Loogle for the truncation comparison, found no shorter public result;
   the Loogle index does not contain that upstream declaration. All remaining proof imports
   provide declarations used here; proof-only imports are plain `import`. The removed
   direct imports and the sole removed old proof dependency are fully listed above.
   The unit `sk-thm-picard-duality` has empty realization lists and is unchanged; this
   below-unit reduction bypasses no realized unit step.
5. PASS — Parsed and compared both node JSON files: only `proof`, `proof_deps`, and
   `proof_origin` differ. The union of the steps' `uses` is exactly `proof_deps`. Read the
   old dependency records and their Lean declarations. The revised steps describe the
   implemented restriction, quasi-coherence, threshold, and canonical-map transports;
   their source attribution and the unchanged Lean statement are correct. No new-node
   requirements apply.

Changes by the second reader: clarified that the delivery adds a proved private helper
but no public intermediate statement or hole; appended this independent review. No Lean
or DAG repair was needed. Closed 1 existing hole, added 0 holes, split off 0 statements;
no whole module is claimed pruned from the targets' import closure.
