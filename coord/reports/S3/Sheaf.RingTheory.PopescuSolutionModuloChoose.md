## What changed

Reduced `Algebra.exists_popescu_admissible_differential_basis` without changing its
signature, visibility, or definitions. Added the proof-only imports
`Sheaf.RingTheory.PopescuQuotientBasisEnlargement` and
`Mathlib.RingTheory.LocalRing.Module`.

The main module now proves the maximal-ideal contraction identity, constructs the
compatible injective residue-field algebra homomorphism by two quotient lifts,
and proves generation of qL. For n = 1 it takes finite generators of q (their
quotient images are zero). For n >= 2 it lifts quotient generation using
Noetherianity and Nakayama. The existing basis and specified element lifts pass
through this argument unchanged. No data is selected by an unproved existence
theorem in a definition: all witnesses are eliminated inside this theorem proof.

The new module isolates the earlier enlargement and differential-basis construction
(steps 2–14 and only quotient generation from step 15). Its ideal conclusion is
strictly weaker: for n = 1 the generator family may be empty, and no conclusion
about qL follows from it alone. The main proof supplies the missing n = 1 argument
and the n >= 2 Nakayama argument as well as the residue compatibility.

Both sandbox modules compile through lcompile.py. The new theorem's docstring and
node retain the detailed transcendental and algebraic case arguments. The original
node now records the actual Lean reduction. The unit's own realized nodes and steps
are unchanged.

## Proved and sorry left

Closed: `Algebra.exists_popescu_admissible_differential_basis`
(node `lem-weil-pbc-popescu-solution-modulo-choose`). No sorry remains in the item's
module.

Added and still sorry: `Algebra.exists_popescu_admissible_quotient_basis`
(node `lem-weil-pbc-popescu-quotient-basis-enlargement`, new module
`Sheaf.RingTheory.PopescuQuotientBasisEnlargement`). Its proof is exactly `by sorry`.

This is a decomposition: one upper hole closed, one strictly smaller hole added;
net hole count zero. It is not a completed sorry-free proof of the enlargement.
There are no other new holes, axioms, definitions, or interface changes.

## No longer needed

Removed proof imports from the item's module:

- `Sheaf.Paper.CartierEquality`
- `Sheaf.RingTheory.ArtinianLocalEssentiallyFiniteTypeResidue`
- `Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian`
- `Sheaf.RingTheory.HenselianEtaleRetraction`
- `Sheaf.RingTheory.HenselianFiniteEtaleEquivalence`
- `Sheaf.RingTheory.JacobiZariskiHomologySequence`
- `Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension`
- `Sheaf.RingTheory.LocalDimensionZeroHenselian`
- `WeilConjectures.Mathlib.RingTheory.Etale.Field`

The main proof uses none of their declarations. Except for CartierEquality, their
mathematics remains in the new enlargement node's plan; removing these direct
imports does not claim their results can be pruned from that plan or from all
other targets. Its detailed proof dependencies remain on the new node. The
Cartier equality node `lem-weil-pbc-cartier-equality` and the finitely-generated
field-definition node `def-pc-field-extension` are not needed by either part of
this reduction: Mathlib `KaehlerDifferential.finite` directly provides finite
residue differentials from `Algebra.EssFiniteType`, which descends to the residue
quotient. No other mathematical dependency is claimed globally unnecessary.
All original public imports are preserved.

The complete list removed from the original node’s direct `proof_deps` is below.
Except for the two explicitly pruned nodes above, these dependencies remain in the
new enlargement node’s proof plan; this list does not claim global pruning.

- `def-pc-field-extension`
- `def-weil-algebraic-element`
- `def-weil-pbc-essentially-finite-type-algebra`
- `def-weil-pbc-finite-type-algebra`
- `def-weil-pbc-flat-ring-map`
- `def-weil-pbc-kahler-differentials`
- `def-weil-pbc-separable-algebraic-extension`
- `lem-weil-pbc-artinian-local-essentially-finite-type-residue`
- `lem-weil-pbc-artinian-local-noetherian-nilpotent`
- `lem-weil-pbc-artinian-local-unique-prime`
- `lem-weil-pbc-cartier-equality`
- `lem-weil-pbc-criterion-flatness-fibre-noetherian`
- `lem-weil-pbc-etale-ring-base-change`
- `lem-weil-pbc-etale-ring-map-iff-etale-affine`
- `lem-weil-pbc-faithfully-flat-ideal-contraction`
- `lem-weil-pbc-finite-separable-extension-etale`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-flat-local-hom-faithfully-flat`
- `lem-weil-pbc-henselian-etale-retraction`
- `lem-weil-pbc-henselian-finite-etale-equivalence`
- `lem-weil-pbc-jacobi-zariski-homology-sequence`
- `lem-weil-pbc-kahler-differentials-localization`
- `lem-weil-pbc-kahler-differentials-polynomial-extension`
- `lem-weil-pbc-local-dimension-zero-henselian`
- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-noetherian-local-quotient-artinian-local`
- `lem-weil-pbc-separable-first-purely-inseparable`

## Where the brief, the DAG or earlier work was wrong

The original step 2 goes through Cartier equality to obtain finite differentials.
Mathlib already proves finiteness for essentially finite type algebras in
Kaehler.Basic. This avoids a stronger field-extension finite-type interface; a
finitely generated field extension need not be a finite type algebra over its base
field. The new proof plan uses essential finite type throughout this step.

No false statement or forced adaptation was found. The original source tex file is
not present on this machine, so the source proofs were read at
https://stacks.math.columbia.edu/tag/07FH and
https://stacks.math.columbia.edu/tag/07FI. The latter's enlargement cases supply the
same construction recorded in the original node; they are not bypassed.

The new statement was checked at n = 1 (empty quotient generator family), n >= 2
(quotient generation is sufficient for Nakayama only after lifting), q = 0
(localization is a field and ideal generation is empty), and a zero-dimensional
space of differentials (empty basis). Characteristic p need not be assumed prime
separately: CharP of a field and p > 0 force p prime. No zero-ring case of L is
possible because q is prime.

Searches: LeanFinder for the whole enlargement returned cotangent-space and
localization tools, not an admissible-subalgebra enlargement theorem; grep of
Mathlib RingTheory found polynomial differential bases, not the desired choice.
LeanSearch returned an internal server error, recorded as unavailable in
searches.jsonl; it is not claimed as a completed negative search. Loogle and local
source reading provided quotient ideal correspondence, finite generating families,
and Nakayama for the completed portion. The repository searches found no duplicate
of the quotient-level enlargement.

## New nodes

`lem-weil-pbc-popescu-quotient-basis-enlargement` states the admissible enlargement,
specified element lifts, residue differential basis, and generation of the ambient
maximal ideal only in the truncated quotient. Its complete argument is copied
from the original node with the finite-differential shortcut and the empty n = 1
quotient-generator family. It keeps the original chapter and unit and has its own
module and one named public sorry. No change record is needed: all existing
statements, definitions, and visibility are unchanged.

## Second reading by S3

1. Compared the main module with the read-only repository using `diff -u`.
   The existing declaration signature and docstring are byte for byte unchanged.
   Only proof imports and the theorem proof changed; no definition, target, public
   import, visibility, or other module was adapted. Verdict: pass.
2. Compiled both modules in import order through `lcompile.py`: 3.1 s and 6.4 s,
   without errors or warnings. Inspected all declarations: exactly one named
   `by sorry` remains, in the reported new theorem; no forbidden declarations or
   data definitions were added. Scratch `#print axioms` checks record only the
   permitted standard axioms and `sorryAx` from that open theorem. Verdict: pass
   as a decomposition, not as a sorry-free proof.
3. Read the new statement, its full fifteen-step docstring, and its node. Checked
   the transcendental localization and finite separable/étale enlargement cases
   against [Stacks 07FI](https://stacks.math.columbia.edu/tag/07FI), and the choices
   against [Stacks 07FH](https://stacks.math.columbia.edu/tag/07FH). In the algebraic
   case the vanishing differential is computed on beta raised to a p-power, so
   alpha need not belong to the enlarged residue field. Rechecked n=1 (empty
   quotient generators), q=0 (a field localization), zero differentials (t=0),
   and n>=2 (Nakayama requires and receives finite generation). New LeanFinder
   and Loogle searches using enlargement and Kaehler-basis terminology, plus
   local source searches, found no duplicate that constructs the needed
   admissible enlargement. The new statement omits contraction, compatible
   embedding, and localized ideal generation: these are proved by the main
   module, including the separate n=1 argument. It is a proper intermediate
   statement, not a renamed copy of the item. Verdict: pass; the remaining
   enlargement cannot be closed by a short application of the searched lemmas.
4. Read the main proof from the conclusion downward. Quotient lifts give the
   embedding; ideal correspondence and the Mathlib Nakayama lemma give the
   localized generators. All added imports are proof-only and all unchanged
   public imports supply signature objects. Checked `dag/units/sk-thm-p1.json`:
   this node is below its realized statement and steps, and none is bypassed.
   The original pruning report omitted an explicit enumeration of every old
   proof dependency removed from the main node; added that enumeration above,
   distinguishing transfer to the new plan from actual pruning. Verdict: pass
   after this report repair.
5. Compared node fields and Lean signatures. The old node changes only `proof`,
   `proof_deps`, and `proof_origin`; its steps match the quotient lifts, n=1
   replacement family, and n>=2 Nakayama reduction. The new node has matching
   Lean statement, source, complete proof steps, dependency union, search
   records, creation provenance, and blueprint/unit/chapter fields. Verdict:
   pass.

Second reading changed only this report: completed the removed-node inventory
and recorded the independent checks. The Lean proof and nodes required no repair.
