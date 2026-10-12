## What changed

Closed both original holes in `Sheaf.RingTheory.ReducedNoetherianTotalRingFractions`.
Four proved private helpers identify the primes of the fraction ring with the minimal
primes of R, prove that its spectrum is finite and discrete, and identify the component
maps with the canonical localization maps. Mathlib's
`PrimeSpectrum.toPiLocalization_bijective` then proves both halves. Surjectivity transports
the prescribed tuple through the indexing and factor equivalences; injectivity compares
all prime-localization components. All existing public signatures and visibility stay
identical. Removed the unused proof import `Mathlib.Algebra.Algebra.Pi`.

The node copies now record this proof and remove the previous circular dependency from
each half back to the bijectivity theorem. The main node records its actual calls to the
finite enumeration, field/residue-field arguments, localization maps and bijectivity.
No new public declaration, instance, node or remaining hole is introduced.

## Proved and sorry left

Holes closed: `fractionRing_pi_injective_of_compatible`
(node `lem-weil-pbc-fraction-ring-pi-injective`) and
`fractionRing_pi_surjective_of_compatible`
(node `lem-weil-pbc-fraction-ring-pi-surjective`). Both are proved without holed dependencies.
Holes added: none. Sorries left in the delivery: none.
`fractionRing_pi_bijective_of_compatible` and
`reduced_noetherian_total_ring_fractions` retain their complete existing proofs and now
rest on fully proved halves. This is a proof, not a decomposition.

The argument needs no Nontrivial instance on R: a trivial ring has empty spectrum, and
the same finite-spectrum product theorem handles it. The Fin t equivalence ensures that
all minimal primes occur exactly once, also when t is zero.

## No longer needed

Removed import: `Mathlib.Algebra.Algebra.Pi`.
The old nilradical-intersection detour, node
`lem-weil-pbc-zero-locus-eq-iff-radical-eq`, is not needed on this route: finite spectrum
and maximality give discreteness directly. No corresponding Sheaf module was imported.
The bundled module `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` is not needed:
its prime-correspondence and local-factor conclusions are used directly from Mathlib.
Its mathematical node remains cited for those steps.
The bijectivity node is no longer a dependency of either of its own halves; it remains
needed by the main theorem. No unit statement or realized unit step is bypassed.

Deleted the abandoned attempt's unsubmitted modules/nodes
`FractionRingPiZero`, `lem-weil-pbc-fraction-ring-pi-zero`, and
`lem-weil-pbc-fraction-ring-pi-exists`; no such intermediate holes are needed.
No claim that these removals prune a module from every other target route is made.

## Where the brief, the DAG or earlier work was wrong

The abandoned attempt used equivalent elementwise reformulations of injectivity and
surjectivity, which did not reduce the mathematical work. It also put two holed statements
in one new module and pre-filled the second reader's section; these files are replaced.
The existing nodes of the two halves referred back to the theorem that combines them,
creating a circular proof plan; the delivered node copies remove that cycle.
The Stacks TeX source is absent in this read-only checkout. Checked the source proofs at
https://stacks.math.columbia.edu/tag/02LX,
https://stacks.math.columbia.edu/tag/00EW, and
https://stacks.math.columbia.edu/tag/00EU. The formal proof follows their finite discrete
spectrum route and uses the corresponding Mathlib constructions.

## Second reading by P2

1. I compared the delivered module against the repository version. Existing public declarations and signatures are byte-for-byte unchanged; only proof bodies, imports, and DAG proof metadata changed. Verdict: pass.

2. I compiled the module with `lcompile.py`; it compiles cleanly with no errors or warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. The new private helpers are constructive apart from permitted classical choice, and the proof introduces no hollow definition. Verdict: pass.

3. The two split-off statements are exactly the original injectivity and surjectivity halves, with no added hypotheses or weakened conclusions. Both are true consequences of the finite product decomposition, and no duplicate declaration exists in Mathlib or the library. Verdict: pass.

4. The proof follows the unit route through prime correspondence, finite discrete spectrum, local factor equivalences, and the product decomposition theorem. The old circular dependency of each half on the combining bijectivity theorem is removed; the proof uses a shared private lemma instead. The unused `Mathlib.Algebra.Algebra.Pi` import and the old nilradical detour are pruned. Verdict: pass.

5. The DAG proof steps, dependencies, origins, and Lean declaration records agree with the delivered code. The unit statement and realized route are preserved. Verdict: pass.

I changed only the report by adding this second-reading record; no Lean proof or statement changes were needed after compilation.
