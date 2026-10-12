## What changed

Proved `AlgebraicGeometry.zariski_to_etale_core` in
`lean/Sheaf/Paper/ZariskiEtaleCore.lean`, with its original signature unchanged.
Four private, fully implemented helpers lift `X.restrictFunctor`, take the open
image of an étale X-scheme, construct the hom equivalence, and prove the adjunction.
The inclusion is a right adjoint, so Mathlib supplies finite-limit preservation.
The covering-sieve argument proves joint surjectivity directly; Mathlib then gives
continuity and representable flatness. Added proof-only imports
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` and
`Mathlib.CategoryTheory.Adjunction.Limits`. All original public imports remain
needed by the statement. Updated the core node's proof, proof_deps and proof_origin.

The search ran through msearch LeanFinder (open-subscheme inclusion preserving
finite limits), Loogle (`"restrictFunctor"`), and grep
(`restrictFunctor|etale.*Image|etaleImage`), plus local searches in both library
roots and Mathlib. No preexisting exact theorem or open-image adjunction was found.
The relevant Mathlib tools are Comma.lift, IsOpenImmersion.lift/lift_fac,
Scheme.Hom.isOpenMap, the right-adjoint limit-preservation instance,
ofArrows_mem_smallEtaleTopology_iff, isContinuous_iff_coverPreserving, and
flat_of_preservesFiniteLimits.

## Proved and sorry left

Proved `AlgebraicGeometry.zariski_to_etale_core`
(node `lem-weil-pbc-zariski-etale-core`). No sorry remains in the module, and no
new sorry or axiom was added. Every private definition has explicit data and all
its proof fields are proved. The module compiles locally without warnings.

## No longer needed

No original import was removed. No Sheaf proof dependency had been imported in
the original module. The following planned dependencies are unnecessary for this
proof and are removed from the core node's proof_deps:

- `lem-weil-pbc-etale-base-change-finite-limits` (Mathlib finite-limit/base-change
  interfaces), because right-adjoint preservation gives the inclusion's limits.
- `lem-weil-pbc-open-preimage-fibre-product` (Mathlib.Restrict's
  isPullback_morphismRestrict), because explicit pullback comparison is unnecessary.
- `def-pc-fibre-product` (Mathlib pullback interface), because no chosen fibre
  product enters the implementation.

These are pruned edges of this node; they may still be needed elsewhere. There
are no Sheaf modules to remove from the target closure from these edges alone.
The temporary extra import
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal` was tested and removed;
its terminal-preservation interface is already available through the retained
imports. The new dependency `lem-weil-pbc-etale-morphism-open-map` is an existing
Mathlib leaf in the same unit. No unit statement or realized unit step is bypassed:
the core node is below the unit level and the inclusion/morphism-of-sites route stays.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original plan's finite-limit proof can be replaced
by the shorter open-image adjunction. Étale morphisms are open (existing leaf,
Mathlib UniversallyOpen.of_flat and Scheme.Hom.isOpenMap), so this needs no
additional unproved theory. The existing docstring describes a valid direct
pullback argument; the implemented alternative is recorded in the node and here.

Edge cases: the image functor sends an empty étale scheme to the empty open;
open-immersion factorization still applies, including empty opens. The covering
proof quantifies over points, so the empty cover of the empty open is accepted
without a nonempty-index assumption. There is no finiteness restriction on cover
indices and no new hypothesis on X. The original universes and all public
signatures are unchanged.

## Second reading by U2

1. PASS: compared every delivered Lean module (one) and node (one) with the
repository using diff. The existing theorem signature is byte-for-byte identical,
as verified separately by extracting its complete text through `:= by`.
Its docstring and all original public imports are unchanged. Only four private
helper definitions, two proof-only imports and the theorem proof were added.
No existing definition, target statement or hypothesis was changed; no change
record is required.

2. PASS: independently compiled the module through lcompile.py without errors
or warnings (2.1 seconds). A scratch copy with `#print axioms` for the theorem
and all four helpers compiles. The theorem uses exactly propext,
Classical.choice and Quot.sound; the helpers use no other axioms. No sorry,
axiom, unsafe, opaque, implemented_by or extern occurs in the delivered code.
The inclusion, image functor, hom equivalence and adjunction have actual data
and fully proved fields. Read the inverse and naturality proofs: cancellation
by the open immersion identifies maps over X, while the other hom-set is thin.

3. PASS: there are no split-off statements, new nodes or new sorries. The four
private helpers are fully implemented, rather than restatements left open.
Checked empty images, the empty open and its empty cover, arbitrary covering
indices and an arbitrary scheme X. The factorization requires only image
containment; no quasi-compactness, nonemptiness or finiteness is introduced.

4. PASS: searched the library roots and Mathlib using image/inclusion,
restrictFunctor, adjunction, IsOpenImmersion.lift, continuity and finite-limit
preservation terminology, plus an independent msearch grep query. No existing
exact theorem or ready-made adjunction was found. Read Mathlib's open-immersion
universal property, small-etale covering criterion, flatness criterion and
continuity equivalence. The adjunction is a direct shorter finite-limit route.
Each retained public import supplies a notion in the unchanged signature;
the two added imports serve only the proof and are plain imports. Compared
old and new proof_deps: the report lists all three removed nodes. Inspected
sk-thm-p1.json realized: none of the removed nodes realizes a unit statement
or step; the unit's route and its realizations remain unchanged.

5. PASS: the node's five proof steps match the lift, image adjunction,
limit/terminal/flatness instances, covering-sieve proof and continuity/package
in Lean. proof_deps is exactly the union of the steps' uses. The newly used
open-map node is an existing verified Mathlib leaf, with the Etale to Smooth
to Flat/LocallyOfFinitePresentation to UniversallyOpen instances recorded.
The only modified node fields are proof, proof_deps and proof_origin.

Second reading changed only this report by recording the independent checks;
no repair of the Lean proof or node was necessary. The existing theorem
docstring describes the original valid pullback route; the implemented
adjunction alternative is accurately documented in the node and report.
