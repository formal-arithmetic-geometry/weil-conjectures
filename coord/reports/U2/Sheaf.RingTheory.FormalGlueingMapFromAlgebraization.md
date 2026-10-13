## What changed

Proved `FormalGlueing.exists_map_from_algebraization` without changing its signature.
Added the fully proved module `Sheaf.RingTheory.FormalGlueingReplacePrime`, with
`FormalGlueing.exists_replace_prime`. It constructs the modified datum for an arbitrary
starting datum and checks its square, scalar action, and morphism equations. This is the
datum-construction portion of Stacks 0ALK (2), rather than an algebraization theorem.

The main proof applies the existing canonical equivalence: essential surjectivity gives
an algebraization, fullness lifts the morphism, and the explicit component formulas prove
the factorization and chartwise bijectivity. Private proved helpers verify both directions
of the torsion/localization criterion directly on fractions. The finite-generation step
uses `Ideal.exists_pow_le_of_le_radical_of_fg`, the existing Mathlib leaf
`lem-weil-pbc-fg-ideal-radical-power`. Both modules compile with no warnings under
`lcompile.py --all`; neither contains `sorry`. The unit's realized statements and steps
are unchanged.

Sources read: https://stacks.math.columbia.edu/tag/0ALK and
https://stacks.math.columbia.edu/tag/05EL (the local literature checkout has no TeX files).
The existing canonical-map module supplies the fraction formula for interchange.
Edge cases are covered without extra assumptions: empty chart families, zero generators,
I = 0, I = R, exponent zero, and zero modules. All chosen algebraizations occur inside
existential proofs; no definition selects an arbitrary unproved witness.

## Proved and sorry left

Closed the sole original hole: `FormalGlueing.exists_map_from_algebraization`
(node `lem-weil-pbc-formal-glueing-map-from-algebraization`).
Added zero holes. `FormalGlueing.exists_replace_prime`
(node `lem-weil-pbc-formal-glueing-replace-prime`) is fully proved.
No `sorry` remains in either delivered module. This is one hole closed, zero split off,
not a decomposition. The imported `FormalGlueing.exists_canonical_equivalence`
remains an existing dependency; it is not changed by this delivery.

## No longer needed

Removed no original imports: all four public Mathlib imports support the unchanged
signature, and `Sheaf.RingTheory.FormalGlueingEquivalence` is used in the proof.
The direct fraction arguments eliminate the proof dependency
`lem-weil-pbc-localization-module-exact` (`Mathlib.RingTheory.Localization.Module`);
that module need not be imported by this item. This makes no claim about its use by
other targets or modules. The other original dependencies remain: formal glueing data,
module localization away, and the canonical equivalence. Added only the used proof
imports `Sheaf.RingTheory.FormalGlueingReplacePrime` and
`Mathlib.RingTheory.Finiteness.Ideal` in the item, and the used proof import
`Sheaf.Paper.FormalGlueingCanonicalMaps` in the new module.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The existing node's monomial
argument is valid; its implementation is shortened using the existing finitely generated
ideal/radical Mathlib leaf. Exact localization is unnecessary because direct fraction
arguments prove the kernel and cokernel criteria. The `extend` and `piece` interfaces
use reconstructed scalar actions, requiring proved scalar-action transports to match
the original theorem's supplied actions; no interface adaptation was needed.

## New nodes

`lem-weil-pbc-formal-glueing-replace-prime` records the fully proved generic replacement
construction in `Sheaf.RingTheory.FormalGlueingReplacePrime`. It is strictly the
construction of a datum and its morphism: it assumes no flatness or quotient isomorphism
and asserts no algebraization or torsion conclusion. The main theorem performs the
descent and torsion arguments itself. Blueprint searches for "formal glueing" and
"05EL" found no matching imported node. Three actual Mathlib searches are recorded:
LeanSearch was unavailable; LeanFinder and grep returned unrelated glueing APIs.
No change records or forced adaptations are needed.

## Second reading by U2

1. PASS: compared both delivered modules with the repository. The only existing
   declaration is `FormalGlueing.exists_map_from_algebraization`; its entire signature
   is byte-for-byte identical. Its proof docstring was updated to describe the implemented
   argument. There are no changed definitions, target signatures, or forced adaptations.
   The additional public theorem has its own new module and node. Existing node changes
   are confined to `proof`, `proof_deps`, and `proof_origin`.
2. PASS: independently compiled both modules in import order, with no errors or warnings.
   Scanned both for forbidden declarations and holes: none occur. Scratch-copy
   `#print axioms` gives only `propext`, `Classical.choice`, and `Quot.sound` for
   `FormalGlueing.exists_replace_prime`. The main theorem additionally has `sorryAx`
   from the existing open canonical-equivalence dependency; its local hole is closed,
   but it is not yet an axiom-free theorem of the completed library. The private functors
   are explicit component projections, and all algebraization witnesses are confined
   to this existential proof; no definition selects an arbitrary unproved witness.
3. PASS: there are no split-off holes. Read the fully proved replacement construction
   against [Stacks 0ALK](https://stacks.math.columbia.edu/tag/0ALK), part (2), and
   [Stacks 05EL](https://stacks.math.columbia.edu/tag/05EL). Its localized inverse
   preserves the S-action, the square follows by surjective precomposition and swap
   naturality, and the unchanged overlaps retain the cocycle. Its conclusion is strictly
   the datum construction, with no algebraization or torsion assertion. Checked empty
   charts, zero generators and zero modules: no invertibility outside the stated
   localized-map hypothesis is needed. Repeated searches with the different LeanFinder
   query "transport descent module datum by a component morphism invertible on each
   localized chart", Loogle `IsLocalizedModule.map, Function.Bijective`, and source
   searches in Sheaf, upstream descent/localization modules, and Mathlib localization.
   Hits concern pseudofunctor descent or finite presentation, not this datum construction;
   no existing replacement theorem or shorter complete descent argument was found.
4. PASS: reviewed the fraction injectivity/surjectivity arguments, the annihilator-radical
   criterion, the scalar-action transports, and the prime/chart component equations.
   The main proof uses the existing canonical equivalence, not a restatement of the item.
   For I = 0 the empty generating family gives a killing positive power; for I = R the
   radical argument remains valid, including exponent zero when the element is zero.
   Public imports serve the unchanged signature (or the new datum signature); additions
   used only in proofs are plain imports. `## No longer needed` lists the entire removed
   old proof dependency, `lem-weil-pbc-localization-module-exact`. No original module
   import was removed, and the existing `sk-thm-p1` realized statement and steps stay
   untouched: this is a reduction below the unit level.
5. PASS: matched the two nodes to their Lean statements and each proof step. Their
   `proof_deps` equal the unions of their step uses; sources and `proof_origin` describe
   the actual fraction, replacement, descent, and radical-power arguments. The new node
   contains its source, complete proof, searches, creation/blueprint/unit/chapter fields,
   and Lean attachment. No statement field of the existing node changed.

Second reading changed only this report: added the independent checks and explicitly
recorded the main theorem's remaining dependency on `sorryAx`. No Lean or node repair
was necessary. Closed one original local hole, added zero holes; zero statements left
split off. Global progress and actual unreachable modules remain for the pinned ledger
and the maintainer's import-closure calculation.
