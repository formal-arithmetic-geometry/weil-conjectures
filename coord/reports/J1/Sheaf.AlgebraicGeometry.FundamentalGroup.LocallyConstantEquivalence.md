## What changed

Proved both declarations in `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence` without changing either signature. The equivalence lifts Yoneda through FLC, obtains full faithfulness from Yoneda and essential surjectivity from the existing representability theorem, and composes existing natural isomorphisms for stalks and base change. The torsor action equation is the naturality equation evaluated on a section.

Added the proved module `Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison`. It converts finiteness at algebraically closed stalks to the source library's predicate testing separably closed stalks. Its private helper proves the natural bijection on lifts under a field extension by an explicit section-and-open-immersion argument. Updated the original node's proof and dependencies to match the Lean.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.exists_finiteEtale_flc_equivalence` and `AlgebraicGeometry.Scheme.finiteEtale_flc_preserves_torsors` (node `thm-galois-lc-etale`): 2 of 2 original sorries removed.

Also proved `AlgebraicGeometry.Scheme.isFiniteSheaf_of_finite_algClosed_stalks` and its private helper `bijective_geometric_lifts` (new node `lem-galois-finite-stalks-comparison`). No sorry remains in either delivered module; none was split off. The main equivalence still relies on the existing representability and inverse-image declarations, whose downstream proofs are separate items.

## No longer needed

Removed redundant proof-only imports `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor` and `WeilConjectures.CategoryTheory.Sites.Torsor`; the required torsor declarations are already provided by the unchanged public import of EtaleTorsorDescent. The original public imports are retained because they expose the existing interface.

Removed `def-weil-pbc-etale-site`, `def-weil-pbc-finite-torsors`, and `def-sc-gm-torsor` from this node's direct proof dependencies: the site and torsor constructions are already carried by the retained representability, inverse-image, and torsor nodes. This is only direct-edge pruning, not a claim that these nodes are globally unused. The original substantive representability, Yoneda, base-change, stalk, and torsor nodes remain needed. Added the point-universe-lift node because the Lean uses that compatibility explicitly. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan omitted a convention mismatch: FLC tests finite stalks at algebraically closed fields, whereas IsFiniteLocallyConstantSheafOfTypes uses IsFiniteSheaf and therefore tests all separably closed fields. The new proved comparison closes that gap without changing any definition or statement.

The unit `sk-prop-h2` has empty realized arrays; this auxiliary node realizes none of its own statement or steps. The existing five-part route of the node is preserved. Searches found no pre-existing comparison theorem. LeanSearch was unavailable (HTTP 500), recorded as unavailable rather than as no match. The local checkout lacks the literature source tree, so Stacks Tag 04FN was read at its official website. The node records that source.

During initial setup I accidentally wrote the evolving scratch module into the read-only clone. I restored its original contents immediately; all proof work and delivery artifacts are in the designated sandbox. No direct git command, push, or library build was run.

## New nodes

`lem-galois-finite-stalks-comparison`: a proved finiteness comparison for arbitrary sheaves of sets, strictly smaller than the equivalence statement. Its proof handles empty stalks and the empty scheme; no local constancy, connectedness or nonemptiness is assumed. Source: Stacks Tag 04FN, with the separably closed variant proved explicitly using Mathlib's lifting theorem. Blueprint searches for “stalk extension”, “finite stalk” and “geometric point” found no existing blueprint statement of this comparison. No change records are needed: existing statements, definitions and public imports are unchanged.

## Second reading by J1

1. Compared the delivered equivalence module with the repository version. Existing declaration signatures are byte-for-byte unchanged; the added module is new and is recorded by its node.
2. Compiled both delivered modules with `lcompile.py --all`; both compile without errors or warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations in either file. The proofs use only imported declarations whose open obligations are documented in the DAG.
3. Checked the new finiteness comparison statement and its private lift-bijection helper. The comparison is strictly smaller than the item, handles arbitrary sheaves including empty stalks, and searches found no existing theorem of this form. Its source and proof are documented in node `lem-galois-finite-stalks-comparison`.
4. Checked the proof route from the top downward. It follows the unit's five-step route: finite local constancy, equivalence, stalk compatibility, base change, and torsor naturality. Proof-only imports removed from the item are recorded above, and the direct proof dependencies in `thm-galois-lc-etale` match the declarations used.
5. Checked the DAG/Lean agreement. The item node records both declarations and the new comparison node records its module, declaration, statement, source, proof, and dependencies. No unit statement or realized step is bypassed.

Changed during second reading: added this review record only; no Lean proof or statement required repair.
