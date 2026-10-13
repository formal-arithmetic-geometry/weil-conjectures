## What changed

Proved `AlgebraicGeometry.Scheme.Modules.moduleCup_godement_stalk_contraction`
in `Sheaf.Paper.ModuleCupGodementStalkContraction`, with its signature and existing
public imports unchanged. Added the proof-only import `Mathlib.Topology.Sheaves.Abelian`
for additivity of the abelian-group stalk functor.

All supporting maps and lemmas are private in the assigned module. Evaluation is the
stalk of the product projection followed by `skyscraperStalkEval`. Its unit identity
and naturality follow from `skyscraperHomEquiv.left_inv`. Separating the zeroth term
of the alternating coface sum proves the contraction equation. The model equalities
transport this calculation to the extended complex. The retraction is explicitly
constructed in degree zero and zero elsewhere; its chain-map equations and both
homotopies are proved. No witness is chosen from an unproved existence theorem.

Updated the existing node's proof and proof origin to describe these Lean steps;
its statement, source, unit, and proof dependencies are unchanged. The source read
was Stacks Tag 0FKR, Lemma 20.30.1 (0FKS). The existing unit realization has no
additional step nodes to retain, and the Godement evaluation route is retained.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.moduleCup_godement_stalk_contraction`
(node `lem-sc-module-cup-godement-stalk-contraction`). Added no holes; no `sorry`
remains in the delivered module. This is a proof, not a decomposition. Every
supporting private lemma is also proved.

The combined assigned module compiles through `lcompile.py` without warnings.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None of the original imports, nodes, or modules was removed. Both original proof
nodes remain needed: `def-sc-module-cup-godement-model` and
`def-pc-module-stalk-functor`. Mathlib's simplicial extra-degeneracy API was searched
but was not imported: the direct alternating-coface calculation avoids dualizing
and transporting a simplicial homotopy. No new statement module is needed.

## Where the brief, the DAG or earlier work was wrong

The previous cached-dependency failure has cleared: the unchanged assigned module
compiled at the start of this attempt. No mathematical statement or definition
needed correction. The DAG's two original steps were expanded into the explicit
construction and calculations, without changing their route.

Searches used `msearch.py` leanfinder (augmented cosimplicial contraction), loogle
(`HomotopyEquiv`), and grep (`godement|Godement`), together with direct searches in
Mathlib, `WeilConjectures`, and `Sheaf`. Mathlib supplies the homotopy packaging and
finite-sum algebra; the source library supplies the stalk-skyscraper adjunction.
Edge cases are handled in the Lean proof: all negative degrees vanish, degree zero
uses the given augmentation equality, zero sheaves satisfy the same identities,
and an empty scheme has no point at which a stalk contraction must be constructed.

## Second reading by K2

1. Compared the complete delivered module with the repository version using `diff`.
   The sole existing declaration's signature is byte for byte identical, as is
   its docstring. No existing definition or visibility changed. The only added
   import is proof-only; all added supporting declarations are private. PASS.
2. Independently compiled the delivered module with `lcompile.py`, without errors
   or warnings. Generated a fresh scratch copy with `#print axioms` for all 17
   declarations, including the private definitions, instance and lemmas: each
   reports only `propext`, `Classical.choice`, and `Quot.sound`. There is no
   `sorry`, forbidden axiom mechanism, or data chosen from an unproved theorem.
   Read the evaluation, retraction, term transport and homotopy constructions;
   the signs and orientations agree with the required forward augmentation. PASS.
3. No statements were split off and no holes or nodes were added. The proved
   private identities are strict parts of the argument, not restatements of the
   target. Checked the zero-coface identity and successor signs, degree-zero
   augmentation, positive-degree cancellation, and negative-degree zero objects.
   These also handle the zero sheaf; the empty scheme has no point argument. PASS.
4. Read the imported model and stalk-functor modules and the upstream
   stalk-skyscraper adjunction. Independently searched the library for Godement
   and contraction results, and inspected Mathlib's ExtraDegeneracy homotopy API.
   That API concerns augmented simplicial objects and would require dualization
   and additional transport here; no shorter existing theorem applies directly.
   All three original public imports serve the statement; the new ordinary
   Abelian import supplies additivity for the proof. Both old proof dependencies
   are used, so `No longer needed` is complete. Read `sk-prop-av-cube.json`:
   its realization contains no additional required step nodes, and the proof
   retains the existing evaluation route below that unit. Checked the cited
   Stacks Tag 0FKR, Lemma 20.30.1, against the stalk homotopy assertion. PASS.
5. Compared the node JSON with its repository version. Only `proof` and
   `proof_origin` differ; the unchanged `proof_deps` equal the union of step
   dependencies and agree with the Lean construction. The statement, Lean
   signature record, source, chapter and unit are unchanged. No new-node
   requirements apply. PASS.

Changes by the second reader: appended this independent review and generated
scratch-only axiom checks. No Lean proof, import, declaration or node repair was
needed. One original hole is closed and zero holes are added.
