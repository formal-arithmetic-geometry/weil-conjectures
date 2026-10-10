Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-locnoeth-components-locally-finite.json`: statement split into four proof steps.
- `dag/nodes/sec-abelian-varieties/lem-sc-components-open-injection.json`: new statement-only node; Mathlib searches found no exact match.
- `dag/nodes/sec-abelian-varieties/lem-sc-affine-noetherian-underlying-space.json`: new Mathlib leaf, `AlgebraicGeometry.noetherianSpace_of_isAffine` at `Mathlib/AlgebraicGeometry/Noetherian.lean:181`.
- `citations.json`: verbatim citations for every non-elementary step use.

Attachments: none.

WANTED: none.

What was wrong in the imported item: it had no proof, despite citing Tag 0052. The missing mathematical bridge is that components meeting an open subset restrict injectively to components of that open subset; this is isolated as `lem-sc-components-open-injection` rather than hidden in an item step. The affine Noetherian-space fact is a Mathlib leaf and is recorded separately.

## Not duplicates

`lem-sc-components-open-injection` vs `lem-sc-noetherian-finite-irreducible-components`: the new node concerns restriction and injectivity of components across an open subset, while the existing node only asserts finiteness for a Noetherian topological space.

`lem-sc-affine-noetherian-underlying-space` vs `lem-sc-noetherian-finite-irreducible-components`: the new node establishes the Noetherian-space hypothesis for an affine scheme with Noetherian global ring; the existing node derives finite components once that hypothesis is available.

`lem-sc-affine-noetherian-underlying-space` vs `lem-sc-locnoeth-components-locally-finite`: the new node is the affine Noetherian underlying-space lemma, while the item is local finiteness of components for an arbitrary locally Noetherian scheme.

`lem-sc-affine-noetherian-underlying-space` vs `lem-weil-pbc-noetherian-open-subscheme-noetherian`: the new node concerns an affine scheme with Noetherian global ring and its Noetherian topology; the existing node concerns arbitrary open subschemes of a Noetherian scheme and includes quasi-compactness.

`lem-sc-components-open-injection` vs `lem-sc-locnoeth-components-locally-finite`: the new node is the restriction/injectivity lemma for components and an open subset; the item concludes local finiteness under local Noetherian hypotheses.

`lem-sc-components-open-injection` vs `def-weil-irreducible-components`: the new node compares components under passage to an open subspace; the existing node only defines irreducibility and irreducible components.

`lem-sc-components-open-injection` vs `lem-pc-irreducible-space-connected`: the new node concerns restriction of maximal irreducible subsets to opens; the existing node relates irreducibility and connectedness of a single space.

`lem-sc-components-open-injection` vs `lem-weil-pbc-noetherian-open-subscheme-noetherian`: the new node proves the component restriction injection; the existing node proves that an open subscheme of a Noetherian scheme is Noetherian.

## Review by E1

I read the item source reference, Stacks Tag 0052 (Topology, `topology-lemma-Noetherian`), and checked the statement against the existing definition node `pqf-def-locnoeth` and `def-weil-irreducible-components`. Step 1 uses exactly the affine Noetherian open-cover clause of `pqf-def-locnoeth`; its hypothesis is the item's locally Noetherian assumption. Step 2 uses the new Mathlib leaf, whose theorem has precisely the affine and Noetherian-global-sections hypotheses, and the existing Mathlib leaf `lem-sc-noetherian-finite-irreducible-components`, whose statement is exactly finite irreducible components for a Noetherian topological space. Step 3 uses the new component-restriction statement and again the existing finite-component statement; the injection is what converts finiteness on U into finiteness of components of X meeting U. Step 4 is elementary: the chosen U is a neighbourhood of the arbitrary point x.

For the new component node I checked the definitions: an irreducible component meeting an open U has irreducible nonempty intersection with U; maximality follows by taking closures in X, and equal intersections force equal closures, hence injectivity. For the Mathlib leaf I read `Noetherian.lean:181`, confirming `noetherianSpace_of_isAffine` has exactly the stated conclusion. I searched the entire DAG and blueprint for component/open-intersection and affine-Noetherian-underlying-space statements; no duplicate was found. I tested the component claim on an irreducible space, a disjoint union of two irreducibles, and an open meeting only one component. The item and both new nodes retain the required blueprint ancestry from `lem-sc-hilbert-polynomial`; the item’s `from.place` was already the imported induction-step place and its `same_as` search was empty.

## Second reading by E1

- Item statement: checked against Stacks Topology Tag 0052 and the locally Noetherian definition; the affine-neighbourhood and local-finiteness quantifiers agree.
- Step 1: checked against `pqf-def-locnoeth`; it uses exactly the affine open neighbourhood clause, with no extra hypothesis.
- Step 2: checked against `lem-sc-affine-noetherian-underlying-space` and `lem-sc-noetherian-finite-irreducible-components`; both cited statements supply the asserted Noetherianity and finiteness.
- Step 3: checked against `lem-sc-components-open-injection` and the finite-components node; the restriction map has the needed domain and codomain and injectivity gives finiteness.
- Step 4: checked directly from the definition of local finiteness; the chosen affine open is a neighbourhood of the arbitrary point.
- `lem-sc-components-open-injection`: statement-only, self-contained, and checked on an irreducible space, a two-component disjoint union, and an open meeting one component; its closure argument proves maximality and injectivity.
- `lem-sc-affine-noetherian-underlying-space`: Mathlib leaf checked against `AlgebraicGeometry.noetherianSpace_of_isAffine` at `Mathlib/AlgebraicGeometry/Noetherian.lean:181`; hypotheses and conclusion match exactly.

Changes: corrected the item node’s `created.item` metadata from the unrelated downstream lemma to this delivered item, because delivery preflight requires ownership to match. No mathematical statements or proof steps required alteration.
