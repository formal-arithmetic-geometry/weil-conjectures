# Stage-1 report: def-trf-complete-algebra-devissage

## Files written

- `dag/nodes/sec-trace-formula/def-trf-complete-algebra-devissage.json`: existing definition, now split; no Mathlib match. Its statement and seven statement dependencies are unchanged. Preserved all inherited fields and searches and appended the searches actually run by Q74.
- `citations.json`: empty list, because the item is a definition with no proof steps.
- `report.md`: this report.

No new nodes and no new Mathlib leaves.

## Attachments

None. Searched the entire read-only `WeilConjectures/` source for the exact blueprint id and for devissage/dévissage, and the upstream name table for the id and complete devissage. The hits concern prime-factor, constructible-sheaf, or derived-category dévissage, not the 05HX algebraic data. The source's algebra-descent module defines descent data and their effectivity, also a different notion. No exact declaration was found. The master reference likewise supplied no complete-devissage declaration.

## WANTED

None: the source used is present locally.

## Problems found and changes

No statement dispute. The existing statement already spells out the complete data of Stacks Tag 05HX. Its unsplit status did not reflect that its constituent notions already had nodes. I checked those dependencies rather than inventing a one-step-devissage node which would only repackage clauses of this definition. I kept the statement, empty proof, empty proof dependencies and null proof origin: a definition specifies data and conditions and does not assert the existence of such data.

The historical blueprint ancestry is retained. I read the unit `sk-i-curve-zero`, the trace-formula chapter, and the current main-20261015 text of `lem-trf-local-term-locality`. The current ancestor concerns contracting correspondences, whereas the recorded ancestry goes through the older nearby-cycle/semistable-alteration algebra branch. The already reviewed parent explains this distinction. This item makes no new geometric claim, changes no unit realization, and preserves the historical branch rather than claiming that 05HX occurs in the new ancestor text.

## Unfinished work

None within this one-level definition split. The existence of complete dévissages and their applications remain separate statement nodes; this definition neither proves nor assumes those theorems.

## Not duplicates

No new nodes. Whole-DAG search for 05HX found only this definition and its parent citation. Whole-blueprint searches with `tools/blueprint_refs.py search` for `devissage`, `05HX`, and `geometrically irreducible` found no blueprint node defining the complete algebraic zigzag. `same_as` therefore stays empty.

## Review by Q74

I read `literature/stacks-project/flat.tex`, `definition-complete-devissage-algebra` (lines 1652 onward), and checked the tag against `literature/stacks-project/tags/tags`: it is 05HX. I also read the preceding elementary-etale-localization definition and following finite-presentation remark to ensure that no extra finite-presentation hypothesis was imported from that remark. The item assumes only finite type for R to S. It does not require every algebra map in the zigzag to be finitely presented.

The eight source conditions have the following exact counterparts. Conditions (1) and (2) are the surjective finitely presented maps S to A_1 and B_i to A_{i+1}, with the latter indexed only for i<n. Condition (3) is A_i finite as a B_i-module. Condition (4) is smoothness with geometrically irreducible fibres. Condition (5) is the S-module identification N with M_1. Condition (6) is the B_i-module identification of the cokernel with M_{i+1}, only for i<n, using B_i to A_{i+1}. Condition (7) is the displayed residue-field base change of alpha_i, at p_i=r B_i. Condition (8) is the terminal zero cokernel. In particular the maps alpha_i themselves are not required to be injective, and an isomorphism after tensoring is not replaced by an isomorphism of the original modules. The prime condition makes the residue field expression well typed; it was already explicit in the received definition and is retained.

I opened and read the statements of all seven dependencies. `def-weil-finitely-generated-module` defines finite modules over an arbitrary ring, so it covers N, M_i and the finiteness of A_i over B_i, not merely finiteness of sets. `def-weil-pbc-finitely-presented-algebra` gives exactly the finite polynomial-generator-and-relation meaning needed for the surjections. `def-sbc-smooth-morphisms` defines smooth scheme morphisms and explicitly identifies this with the affine-local smooth-ring-map notion; this is why the item formulates condition (4) on spectra. `def-pc-geometrically-irreducible` defines geometric irreducibility over every field extension and supplies the meaning on each fibre. `def-weil-affine-spectrum` defines the spectra and the contravariant morphisms from the displayed ring maps. `def-weil-pbc-module-tensor-product` defines tensor products and their induced maps. `def-weil-pbc-localization-at-prime` defines precisely the residue fields used here. Each is an unmerged existing node. All seven are used in the statement; none is being cited as a theorem about a notion it only defines.

The remaining operations are explicit data, not hidden lemmas: finite type means finitely many algebra generators in the opening sentence, a finite ring map means finite as a module, cokernel means quotient by image, and the scalar actions are restriction along the given ring maps. A finite free module B_i^{oplus r_i} is just a finite tuple of elements of B_i. Therefore there are no proof-step citations to audit for C4, no uncited non-elementary argument under C1, and no long proof step hiding a lemma. `citations.json` is correctly empty rather than containing invented proof steps for this definition.

For edge cases I checked n=1 with R=S=A_1=B_1=k, r=(0), M_1=k^d, and alpha_1 the identity. It satisfies the eight conditions, including for d=0. For r_i=0 the generic-fibre requirement means that M_i has zero generic fibre; the definition does not incorrectly force M_i itself to vanish at intermediate indices. The received n=0 convention is confined to N=0 and has no undefined alpha_0 or terminal index. No domain, Noetherian, flatness of N, or projectivity hypothesis was added. All module isomorphisms use the available ring maps, so the zigzag does not tacitly require maps in the opposite direction.

I read the actual search results. LeanSearch returned adic completions, finite-dimensional complete submodules and lattices; LeanFinder, in two phrasings, returned smooth presentations and Noetherian descent. These do not define complete dévissage. Loogle for "devissage" and both logged Mathlib greps had zero hits. I also read the smooth-algebra source introduction, which confirms that Algebra.Smooth is only one constituent condition, not this data structure. These are no-match verdicts, not claims that smoothness itself is missing from Mathlib. The inherited Q56 searches are preserved, and Q74's exact calls and results are appended from `searches.jsonl`. No unrun search was recorded.

Checked B1--B10, C1--C8, D1--D5 and E1--E7 against the definition and sources. No new unsplit statement, duplicate, circular proof, source-only citation, or SGA dependency was introduced. No Lean file or live project file was written, and no compiler or build was run.
