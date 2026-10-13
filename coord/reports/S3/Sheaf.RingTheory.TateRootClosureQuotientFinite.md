## What changed

Replaced the sorry in `tate_root_closure_quotient_finite` with a compiling proof.
Added the proved module `Sheaf.RingTheory.TateRootIdealPrime`: normality descends
common powers into R, lying over supplies a prime, and division by y identifies it
with the root ideal. This proof handles y=0 explicitly.
Added `Sheaf.RingTheory.PrincipalPrimeQuotientFractionFinite` for the localization
and finite residue-field part of the argument, without any Japanese hypothesis.
The private proved helper `finite_integral_algebra_of_isN2` embeds an integral
algebra into its finite normalization; a finite-dimensional shrink handles the
universe restriction in IsN2. The assigned module combines these parts, transfers
N-2 along the contraction equality, and restricts scalars to R.
All original signatures and public imports are unchanged. Updated the parent
node proof and proof dependencies to match the new route.

## Proved and sorry left

Closed original hole: `tate_root_closure_quotient_finite`
(node `lem-weil-pbc-tate-root-closure-quotient-finite`). No sorry remains in the
assigned module. The new `tate_root_ideal_prime` and private helper
`finite_integral_algebra_of_isN2` are fully proved from Mathlib.
Added one hole: `principal_prime_quotient_fraction_finite`
(node `lem-weil-pbc-principal-prime-quotient-fraction-finite`). Its docstring and
node give the zero-prime argument, height-one localization, Tag 031F application,
and compatible fraction-field transport. This is a decomposition: one hole
closed and one strictly simpler hole added, net zero. The new statement has no
N-2 or module-finiteness conclusion and no root or normality hypotheses.
All three modules compile locally via lcompile.py.

## No longer needed

Removed the direct import `Sheaf.RingTheory.DimOneResidueFieldsFinite` from the
assigned module. Its node `lem-weil-pbc-dim-one-residue-field-extensions-finite`
is still needed below the new quotient-fraction-field lemma; this is relocation,
not global pruning. The following old parent proof dependencies are no longer direct dependencies:
`def-weil-finitely-generated-module`, `def-weil-pbc-krull-dimension-ring`,
`def-weil-pbc-localization-at-prime`, `def-weil-pbc-normal-ring`,
`lem-weil-pbc-dim-one-residue-field-extensions-finite`,
`lem-weil-pbc-localization-dimension-chains-below-prime`,
`lem-weil-pbc-localization-noetherian`,
`lem-weil-pbc-noetherian-height-quotient-bound`, and
`lem-weil-pbc-prime-residue-field-algebra`. Normality moves to the root-ideal
node; localization, height and residue-field arguments move to the quotient-fraction
node. Finite generation remains part of the parent signature, and dimension is used
below the quotient-fraction node. No old node is globally unnecessary.
The zero-parameter branch no longer needs a separate transport of N-2 to R and
its original fraction field: it is handled uniformly by the quotient argument.
All remaining proof imports supply constructions or lemmas actually used.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature change was found. Rewriting the quotient ideal
inside IsN2 directly fails because the domain instance depends on that ideal;
the proof transports the ideal and its domain instance together. The local
Stacks source file is absent on this machine; checked the primary source at
https://stacks.math.columbia.edu/tag/032P. Blueprint searches for 032P and
principal prime residue returned no matching blueprint node. Edge cases for the
new statements include x=0 (root ideal zero; quotient fraction fields recover
the original extension), e=0 (root equals the parameter), and nonzero x
(principal prime height one). A unit parameter is excluded by the quotient-domain
hypothesis. No unit route was changed.

## New nodes

`lem-weil-pbc-tate-root-ideal-prime` records the fully proved root-ideal argument
in `Sheaf.RingTheory.TateRootIdealPrime` (no new hole).

`lem-weil-pbc-principal-prime-quotient-fraction-finite` records the remaining
localization/residue-field step in its own module, usable for arbitrary domains
with compatible finite extensions of fraction fields. Its conclusion supplies
exactly the finite extension needed by the completed N-2 argument. No change
records or forced adaptations were needed.

## Second reading by S3

1. Compared the assigned module with the repository using diff. The entire original
   theorem signature, docstring, visibility and public imports are byte for byte unchanged.
   There are no definition or statement changes and no forced adaptations.
2. Read all three modules and compiled the complete set with lcompile.py. The only
   remaining sorry is the named theorem `principal_prime_quotient_fraction_finite`.
   No forbidden declarations or hollow definitions occur. The private finite-algebra
   helper constructs an embedding into integralClosure, and Shrink uses proved finite
   dimensionality, not arbitrary data chosen from an unproved existence statement.
   Scratch #print axioms checks show only propext, Classical.choice and Quot.sound
   for the root-ideal theorem and private helper; the parent additionally uses sorryAx
   from the named remaining lemma, as does that lemma itself.
3. Checked the split against Tags [031F](https://stacks.math.columbia.edu/tag/031F)
   and [032P](https://stacks.math.columbia.edu/tag/032P). The quotient-fraction lemma
   is strictly the residue-field part of the argument, without any N-2 hypothesis or
   finite-module conclusion. For x=0, localizing S by R's nonzero elements gives a
   K-subalgebra of L, finite dimensional and a domain, hence a field; Q is zero.
   For x nonzero, its prime principal contraction has height one, so Tag 031F applies.
   A unit x is impossible because a proper prime has proper contraction. For the
   root-ideal lemma, y=0 forces x=0 by injectivity and positive p^e; e=0 makes y the
   image of x. The lying-over and division argument proves both primeness and the
   exact contraction, with no finite-extension assumption. Repeated LeanFinder,
   Loogle and grep searches with height-one/residue-field wording, and searched
   Sheaf and upstream RingTheory. No duplicate full statement or immediate closure
   was found; quasi-finite residue lemmas require hypotheses unavailable here.
4. Read the proof from the parent downward. It combines the proved root-ideal
   argument, the residue-field step, and a proved Noetherian submodule argument.
   This is a valid decomposition, net zero holes, not a completed sorry-free proof.
   All removed old direct dependencies are now enumerated above. The split module
   now imports its planned proof dependencies. The item and new nodes are below
   sk-thm-p1's realized unit steps; read dag/units/sk-thm-p1.json, including its recorded unit text:
   none of its statement or step realizations is bypassed or changed.
5. Read all three node records against their Lean signatures and proof bodies.
   Parent proof_deps matches the reduction; the root-ideal node records lying over
   and division exactly as implemented. The fraction-field node has the named hole,
   complete proof plan, source, creation, blueprint and Lean fields. Corrected the
   zero-prime step's citation from the purely-inseparable definition to the existing
   finite-dimensional-domain-is-field node and recomputed the union proof_deps.

Changes by the second reader: added proof-only imports of DimOneResidueFieldsFinite,
KrullsHeightTheorem, Localization.Submodule and FiniteDimensional.Basic to the split
module; corrected the zero-prime DAG citation; completed the explicit pruning report;
removed an extra blank line. No mathematical statement or proof body was changed.
