## What changed

Completed both remaining proofs in
`Sheaf.AlgebraicGeometry.SupportedOpenPushforwardLocalComparisons` without changing
any existing declaration signature, visibility, or docstring. The combined theorem
retains its original pairing proof.

On U, full faithfulness of derived open direct image gives an invertible counit.
The triangle identity proves the first comparison; the adjoint triple and the
specified adjunct equation prove the second. The derived over-site equivalence
reflects invertibility. On V, exact restriction and homology-stalk comparisons
propagate support through open base change and concrete extension by zero; both
endpoints restrict to zero. Uniqueness of left adjoints transfers the latter
calculation to the given S. All helpers are private and fully proved.

Added proof imports for exact open extension/restriction, exterior extension stalks,
supported derived restriction, scheme open restriction maps, adjoint triples,
abelian presheaves, and the source library's derived additivity, adjunction,
composition, and full-faithfulness APIs. Updated the two component nodes' proof
steps, proof dependencies, and proof origins. No new modules or nodes were needed.

The same arguments cover empty U, empty T, and T = X. No boundedness, affineness,
compactness, or quasi-coherence assumptions were introduced. The original
perfectness and closed-support-containment hypotheses remain in the signatures.

Local compilation is clean (no errors or warnings), with the default heartbeat
limit. The import-cycle and downstream import-pruning checks pass. The delivery
script performs the final axiom probe and mechanical preflight.

## Proved and sorry left

Closed 2 original holes:

- `AlgebraicGeometry.Scheme.supported_open_pushforward_local_comparisons_first`
  (`lem-pc-supported-open-pushforward-local-comparisons-first`).
- `AlgebraicGeometry.Scheme.supported_open_pushforward_local_comparisons_second`
  (`lem-pc-supported-open-pushforward-local-comparisons-second`).

No sorry remains in the delivered module. No holes were added, split off, or moved.
After the second-reading simplification, explicit `#print axioms` checks of both
component declarations and the combined declaration show only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The already proved `supported_open_pushforward_local_comparisons` is unchanged.
These are complete proofs from existing library declarations; they do not assert
that every transitive dependency elsewhere in the project is already sorry-free.

## No longer needed

No original dependency node or module is pruned. All original planned dependencies
are used, and the original proof import of
`Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact` is retained.

The second reading removed the first worker's added proof import of
`Sheaf.Algebra.Homology.OpenExtensionRestrictionIso` and the corresponding added
node dependency `lem-pc-open-extension-restriction-iso`. Mathlib's adjoint-triple
unit/counit lemma supplies the restriction isomorphism directly. Thus this delivery
never adds that module to the item's import closure. No perfect-generation,
supported-global-pushforward, QCoh, or compactness lemma is imported to obtain
these local comparisons. Each remaining proof import was checked by removing it
from a scratch copy: compilation fails at an ingredient actually used by the proof.

## Where the brief, the DAG or earlier work was wrong

No statement or unit-level mathematical route was wrong. The old component nodes named
only open base change (and, for the second, exact adjunction), but their described
proofs also need support detection and extension-by-zero stalk calculations.
Their updated dependency lists now record those existing nodes explicitly.

The local literature checkout lacks the cited Stacks TeX files, so the source
was checked directly at [08DF](https://stacks.math.columbia.edu/tag/08DF),
[08FE](https://stacks.math.columbia.edu/tag/08FE),
[08BS](https://stacks.math.columbia.edu/tag/08BS), and
[00A7](https://stacks.math.columbia.edu/tag/00A7). The implemented route is their
local restriction/zero-object argument, with categorical transport to arbitrary
adjunctions. The assigned unit's realized statement/steps impose no additional
route here; no unit or chapter record was changed.

Searches: LeanFinder found the underived `Modules.restrictAdjunction` and
restriction comparisons. Loogle for `Adjunction.left_triangle_components`
returned unknown identifier/no hits. Mathlib grep for
`isIso_of_comp_hom_eq_id` found the exact invertibility tool in Iso and
Adjunction.FullyFaithful. Repository searches found the already proved supported
restriction theorem and reusable private support/stalk calculations in
`SupportedOpenUnitImageProperties`; these were generalized to the universes
of this module rather than importing that theorem's compactness/QCoh route.

## Second reading by X3

1. **Interfaces — pass.** Read the full repository/sandbox diff and used the
   declaration parser to compare every existing declaration. Existing signatures,
   visibility, docstrings, and public imports are byte for byte unchanged. Only
   the two component proof bodies, private proved helpers, and proof imports
   differ; the combined theorem's proof is unchanged. No change record is needed.
   Only the two component node files are delivered, and only their `proof`,
   `proof_deps`, and `proof_origin` fields change.

2. **Proofs and data — pass after repair.** Compiled the module locally without
   errors or warnings. There is no local sorry, forbidden declaration, or hollow
   definition. The stalk isomorphism is explicitly composed from existing
   isomorphisms; full faithfulness is explicitly built from proved instances.
   Extension by zero is the concrete presheaf/sheafification construction,
   not a witness selected from an existence theorem. Choices of adjunctions and
   comparison isomorphisms occur only inside proofs. The initial axiom probe
   exposed `sorryAx` through `nonempty_openExtensionRestrictionIso`; the repair
   described below removes that dependency. Final explicit axiom probes of both
   components and the combined theorem show only the three permitted axioms.

3. **Split statements and reuse — pass.** No statement is split off and no new
   public statement or node is added. Read all six private helpers and the
   supplied adjunctions; the triangle identities and isomorphism directions
   match the required maps. Checked empty U, empty T, and T = X: the stalk
   arguments are vacuous on empty spaces and maps between zero objects remain
   invertible. Perfectness and containment are retained even though not needed
   locally. Independent LeanFinder, Loogle, Mathlib grep, and repository searches
   found the existing restriction-stalk and adjoint-triple tools used here.
   The similar support helpers in SupportedOpenUnitImageProperties are private,
   so they cannot be imported as declarations; importing its stronger global
   theorem would add irrelevant hypotheses and dependencies.

4. **Route and pruning — pass after simplification.** Checked the local argument
   against [08DF](https://stacks.math.columbia.edu/tag/08DF), open base change
   [08FE](https://stacks.math.columbia.edu/tag/08FE), exact extension/restriction
   [08BS](https://stacks.math.columbia.edu/tag/08BS), and extension stalks
   [00A7](https://stacks.math.columbia.edu/tag/00A7). The support calculation and
   zero-object comparison implement those local computations. The assigned unit
   `sk-thm-picard-duality` has empty realized statement and step lists, imposing
   no additional node here; its record and route stay untouched. No original
   proof dependency is unused. All proof-only imports are plain imports and
   removal checks establish their use. No baseline module is pruned.

5. **DAG agreement — pass after repair.** Read both component nodes and their
   existing dependencies. The first records full faithfulness, stalk transport,
   open base change, and zero restriction. The second records concrete exact
   extension, adjoint uniqueness, inside/outside stalks, adjoint-triple
   invertibility, and zero restriction. Updated its second step, dependency
   union, and proof origin to reflect the simpler proof. No new nodes require
   metadata checks.

**Changed in the second reading:** Replaced the chosen extension/restriction
isomorphism with the inverse of the underived extension/restriction unit. Its
invertibility follows immediately from the adjoint triple and the fully faithful
underived open direct image. Removed the now-unused local restriction abbreviation,
restored the original exact-adjunction import, removed the added isomorphism
module/node dependency, and corrected this report. The repair eliminates the
upstream `sorryAx` while preserving every existing statement. Two original holes
are closed, zero are added, and zero are split off: this is a proof, not a
hole decomposition.
