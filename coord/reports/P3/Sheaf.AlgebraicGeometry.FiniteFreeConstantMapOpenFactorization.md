## What changed

Added `Sheaf.AlgebraicGeometry.FiniteFreeConstantMapEtaleFactorization` with the finite
étale-local lifting statement, left as a named intermediate `sorry`. Completed
`AlgebraicGeometry.Scheme.exists_open_factorization_of_finite_free_constant_map`: it forms
the open image of the étale neighbourhood, transports the factorization across upper-star
composition, reflects the cokernel equation along faithful pullback, and applies abelian
mono-lifting. Updated the target node's proof and dependencies to match this route.

## Proved and sorry left

This is a decomposition, with one original hole closed and one new hole added; it is
not a net reduction of sorry count. Both modules compile with lcompile.py --all (about five seconds per file).
The target signature is unchanged; the proof adds only private imports.
The new statement was checked at n = 0, for the zero ring, and without monicity: it
asserts only étale-local lifting, so finite generation and germ equality suffice.

The target theorem `AlgebraicGeometry.Scheme.exists_open_factorization_of_finite_free_constant_map`
is proved. The only remaining hole is
`AlgebraicGeometry.Scheme.exists_etale_factorization_of_finite_free_constant_map`, in node
`lem-weil-pbc-finite-free-constant-map-etale-factorization`.

## No longer needed

No original public import was removed. The target's direct use of the constant-sheaf
adjunction and pointed-neighbourhood construction is now through the intermediate node;
the following old direct `proof_deps` are no longer direct dependencies of the target:
`def-constructible-constant`, `def-weil-pbc-geometric-stalks`,
`lem-weil-pbc-constant-sheaf-maps-global-sections`, and
`lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`. They are retained as dependencies of
`lem-weil-pbc-finite-free-constant-map-etale-factorization`, so no module is pruned from the
import closure. `lem-weil-pbc-flat-lfp-open` and `def-weil-pbc-etale-site` remain direct
proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The original node bundled finite generator lifting and open-image descent. The Lean proof
shows that the first part is a genuine independent intermediate theorem; splitting it is
used here to keep the remaining target proof complete. No mathematical error in the original statement or unit route was found. The generic faithful-upper-star
lemma is available in the existing sorry-free source module `Surjective`.

## New nodes

`lem-weil-pbc-finite-free-constant-map-etale-factorization` records the unresolved finite
étale-local lifting theorem and its source proof plan. Its Lean module is
`Sheaf.AlgebraicGeometry.FiniteFreeConstantMapEtaleFactorization`.

`lem-weil-pbc-surjective-module-pullback-faithful` attaches the existing proved declaration
`AlgebraicGeometry.Etale.faithful_upperStar_of_surjective`; it adds no Lean module and no hole.

## Second reading by P3

1. **Statements and interfaces.** Compared the delivered target module with the repository and verified the existing
Lean signature and existing node statement are byte-identical; checked the new node
signature against its new Lean declaration.
The new étale-local statement is strictly weaker than the target: it removes monicity and
only asks for an étale neighbourhood. Verdict: pass.

2. **Proof and axioms.** Compiled both modules with `lcompile.py --all`; the target proof
closes the original theorem and the only remaining `sorry` is the named étale-local theorem.
The proof uses the faithful upper-star declaration and abelian mono-lifting, with no
forbidden commands or hollow definitions. Independent scratch `#print axioms` checks of
both declarations showed exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`;
the last is expected from the remaining helper hole. Verdict: pass.

3. **New statements and search.** Checked the finite-free étale-local statement at the
zero rank and zero ring edge cases and confirmed the source and docstring give the filtered
colimit lifting argument. Searched the local library and Mathlib; no duplicate declaration
was found. Verdict: pass.

4. **Pruning and route.** The open-image construction, upper-star composition transport,
faithful pullback, and cokernel mono-lifting are all present in the target proof. The
unit route remains represented by `sk-thm-p1`; no public import could be removed without
losing declarations used by the proof. Verdict: pass.

5. **DAG agreement.** Updated the faithfulness node's proof dependency from the unrelated
abelian inverse-image germ node to `lemma-openclosed-stalk-upperstar`, which is the stalk
comparison used by its source declaration. The target node's proof and dependencies match
the written reduction and the split node records the remaining hole. Verdict: pass.

I changed the faithfulness dependency record, completed the list of old direct dependencies
moved behind the helper, and removed an accidental extra space before the target proof's
`:=` so that its signature is byte-identical. No mathematical statement or proof was altered.

Independent searches: leanfinder on a finitely presented free-module homomorphism into a
sheaf stalk returned sheaf generators and quasi-coherent results, not the required local
lifting; loogle on `Point.toPresheafFiber` returned the representation API; grep on
finite stalks and neighbourhoods found no replacement. Read the source-library
`ConstructibleSheaf.FreeLifting` too: its lifting statements assume an epimorphism over a
quasi-compact object and do not directly supply the prescribed-stalk local lifting here.
Closing the split theorem requires combining finite representatives, their germ equalities,
and the constant pullback comparison; it is not a few-minute application of an existing lemma.
Source checked directly at https://stacks.math.columbia.edu/tag/09BH, proof of (3): finite
generator representatives and descent to the open image. The specialization here uses free
source generators and does not require the proposition's Noetherian hypotheses.
