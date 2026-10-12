## What changed

Proved `AlgebraicGeometry.quotient_firstFactor_equiv_of_restrict_iso` in
`lean/Sheaf/AlgebraicGeometry/QuotientFirstFactorIso.lean`, without changing its
signature or public imports. Added proof-only imports of
`Mathlib.AlgebraicGeometry.Morphisms.IsIso` and `Mathlib.RingTheory.Idempotents`.

The CRT factors are the actual quotients by `(1-c)` and `(c)`. Both factor maps
are constructed with `Ideal.Quotient.lift`. The proof constructs a lift `g` of
`c` with `D(g) ⊆ U` by separating the first-factor kernel from the complement
of `U`. Mathlib's restriction and basic-open comparison isomorphisms then give
bijectivity of `Localization.awayMap i g`.

Two proved private helpers compute the first-factor kernels and descend the
inverse localization map along the target factor surjection. This proves
bijectivity of the first factor map, and `RingEquiv.ofBijective` completes the
construction. No arbitrary data is chosen from an unproved existence theorem.

Updated steps 1 and 4 of the existing DAG node to describe the exact CRT and
inverse-descent implementation. The source, statement, proof dependencies,
proof origin, and unit route remain the same. Read the final product and
localization paragraphs of Stacks Tag 09XH at
https://stacks.math.columbia.edu/tag/09XH; the local literature copy is absent.
The proved `IntegralClosureFiniteFibreChooseG` module supplied the reusable
pattern for separating the closed support and restricting the isomorphism;
it is not imported because its specialized statement is unnecessary here.

Validation: the complete file compiles cleanly through `lcompile.py`.
`#print axioms AlgebraicGeometry.quotient_firstFactor_equiv_of_restrict_iso`
reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The proof permits zero rings, `c = 0`, `c = 1`, and empty or full `U`;
no nontriviality or finite-type assumption is introduced. The CRT and
localization universal properties also apply to the zero-ring factors.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.quotient_firstFactor_equiv_of_restrict_iso`
(node `lem-weil-pbc-quotient-first-factor-iso`).

No `sorry` remains in the delivered module. No holes or new modules were added.
This is a complete proof, not a decomposition.

## No longer needed

No original imports, proof-dependency nodes, or modules are pruned.
An initially added proof import of
`Mathlib.RingTheory.Ideal.Quotient.Operations` was removed after a clean
compilation confirmed that the retained imports already provide its lemmas.
The specialized `Sheaf.AlgebraicGeometry.IntegralClosureFiniteFibreChooseG`
module is not needed or imported. All original proof dependencies are Mathlib
leaves and their relevant ingredients remain in the proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The final quotient transport can be expressed
more directly in Lean by descending the inverse localization homomorphism,
rather than constructing equivalences of localized quotient rings explicitly.
The existing DAG now records this implementation. No statement, definition,
visibility, or target was changed, and no forced adaptations are required.

## Second reading by J3

1. **Interface and statement.** I compared the delivered module with the repository
version. The theorem signature and all existing public declarations are unchanged;
only proof-only imports, private helpers, and the theorem proof were added. The
hypotheses and conclusion match node `lem-weil-pbc-quotient-first-factor-iso`,
including zero rings, arbitrary universes for the two factors, the open restriction
isomorphism, and the image containment condition.

2. **Proof.** The file compiles cleanly with `lcompile.py`. There are no `sorry`,
`axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. The target's
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. The CRT product,
choice of a denominator in the open locus, localization bijectivity, kernel
calculation, and quotient descent are implemented in the proof rather than hidden
behind an unproved definition.

3. **Statements and nodes.** No new public statement or split-off theorem was added.
The two private helper theorems are proof-local reductions and introduce no DAG holes.
The existing node's statement is unchanged. Its updated proof steps describe the
actual `RingHom.prod_bijective_of_isIdempotentElem` and localization/descent route.

4. **Pruning and route.** The retained imports are used by the proof; the previously
tested `Mathlib.RingTheory.Ideal.Quotient.Operations` import is absent. No proof
dependency node is removed, and the unit route remains represented by the existing
node and its four steps.

5. **DAG agreement and changes.** The node's `proof` text and `proof_deps` agree with
the delivered proof, and no statement-change record or forced adaptation is needed.
The only change made in this second reading is this report section.
