## What changed

Proved `CategoryTheory.Functor.exists_rightDerived_exact_comp_iso` in
`Sheaf.CategoryTheory.RightDerivedExactComposite`, preserving its full signature and
its formula for every choice of resolutions and lift. The proof constructs the
isomorphism using mapped augmentations, `descOfQuasiIso`, and the already proved
`quasiIso_map_of_rightAcyclic_nat`. A proved private helper
`CategoryTheory.Functor.homotopy_of_resolution` extends Mathlib's coinductive
`InjectiveResolution.descHomotopyZero` argument to a resolution with arbitrary terms.
Its application, together with the naturality of the resolution and composition
isomorphisms, establishes the universal comparison formula. Updated the existing
node's proof to describe these actual Lean steps; its dependencies and statement stay
unchanged. No new public declarations, statement changes, or adaptations.

The module compiles cleanly through `lcompile.py` (about 3 seconds).
`#print axioms CategoryTheory.Functor.exists_rightDerived_exact_comp_iso` gives exactly
`[propext, Classical.choice, Quot.sound]`. All lines meet the 100-column bound.
The construction covers degree zero, zero objects and functors, and identity functors
without extra case assumptions. The homotopy helper requires only a genuine resolution
and injectivity of target terms, and does not assume injective source terms.

## Proved and sorry left

Closed: `CategoryTheory.Functor.exists_rightDerived_exact_comp_iso`
(node `lem-sc-ext-derived-composite`): 1 of 1 original holes proved.
Added holes: none. Sorries left in the delivered module: none.
The private helper `CategoryTheory.Functor.homotopy_of_resolution` is fully proved.
This is a proof, not a decomposition; its axiom check has no `sorryAx`.

## No longer needed

Removed the redundant direct proof import
`WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`.
The required public import of `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`
already imports it. No DAG dependency or transitively reached module is eliminated:
all four planned dependencies are still used. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The plan is implemented entirely from already proved
library results and elementary homotopy/naturality glue, so no intermediate holes were
necessary. The explicit comparison formula requires a homotopy argument for arbitrary
source resolutions; Mathlib's bundled `descHomotopy` requires injective sources, so its
coinductive construction was extended locally rather than applied with a false premise.
The recorded multi-clause Leray node names LongExactSequence as its main module,
but its acyclic-resolution API is in Acyclic, which was already publicly imported.

Searches run through `msearch.py`: LeanFinder for composition with an exact functor
sending injectives to acyclics, Loogle for `InjectiveResolution.isoRightDerivedObj`,
and grep for `isoRightDerivedObj|descOfQuasiIso`. Read the matching library signatures.
The local literature checkout lacks `derived.tex`; verified the existing cited sources
online: [Stacks 015M](https://stacks.math.columbia.edu/tag/015M) and
[Stacks 015E](https://stacks.math.columbia.edu/tag/015E). The proof follows their route.

## Second reading by P1

1. **Interface preservation — PASS.** Read the full module and compared it with the
   repository using `diff -u`. Compared the existing theorem's text from `theorem`
   through its signature terminator programmatically: byte-for-byte identical.
   Its original docstring and public import are unchanged. The only additions are
   a private proved helper and the proof; the only removed import is private.
   No definitions, public signatures, target statements, or adapted modules change.
2. **Proof and axioms — PASS.** Independently compiled the delivered file with
   `lcompile.py` (3.5 seconds), with no warnings or errors. A scratch copy containing
   `#print axioms` for both declarations compiled and showed exactly `propext`,
   `Classical.choice`, and `Quot.sound` for each. No `sorry`, forbidden declaration,
   kernel-check bypass, or hollow definition occurs. Read the coinductive base
   cases and successor step against Mathlib's `descHomotopyZero`: source exactness
   and target injectivity suffice. Read the comparison proof through its final
   naturality and reassociation equalities, including the augmentation condition
   for all arbitrary lifts. The isomorphism's data comes from proved constructions.
3. **Split statements and edge cases — PASS.** No split-off statement, new node,
   or added hole exists. The private helper is fully proved, strictly a homotopy
   subargument, and introduces no additional premise into the public theorem.
   Degree zero, zero objects/functors, and identity functors require no extra
   cases or assumptions. Searched with the independent Loogle query
   `"rightDerived", "comp"` and grep query
   `homotopy_of_comp_quasiIso|exists_rightDerived_exact_comp_iso|rightDerived.*[Cc]omp`,
   and searched the project sources. The hits concern localization comparisons
   or composition of natural transformations, not this degreewise comparison
   with its universal lift formula. The existing public lift-uniqueness theorem
   works over integer-indexed complexes and needs extension/restriction; the
   natural-indexed helper in `AcyclicComparisonNatural` is private. Neither gives
   a shorter directly applicable replacement for the local coinductive argument.
4. **Route and pruning — PASS.** The proof constructs mapped augmentations, uses
   the proved acyclic quasi-isomorphism API, then proves independence by homotopy
   and resolution naturality. Checked all four old dependency nodes and their
   recorded declarations: all remain used. `Acyclic` publicly imports
   `LongExactSequence`, so the removed private direct import is redundant and
   removes no module from the transitive closure. `## No longer needed` is complete.
   Read `dag/units/sk-thm-picard-duality.json`: this helper is not a realized unit
   statement or step, and the proof does not change or bypass the unit's route.
5. **DAG agreement — PASS.** Compared the node JSON with the repository. Only
   `proof` and `proof_origin` differ; the statement, `lean` record, and four
   `proof_deps` remain unchanged. The three rewritten steps correctly describe
   the actual mapped augmentation, acyclic comparison, and homotopy/naturality
   argument. There are no new nodes requiring additional fields or change records.

**Second-reader changes:** appended this independent review to the report only;
no Lean or DAG repair was necessary. Confirmed one original hole closed and zero
holes added; no modules pruned.
