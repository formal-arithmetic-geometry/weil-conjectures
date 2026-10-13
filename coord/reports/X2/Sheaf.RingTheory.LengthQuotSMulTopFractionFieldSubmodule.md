## What changed

Proved the unchanged declaration
`Submodule.length_quotSMulTop_le_of_ringKrullDim_eq_one_of_isLocalRing` in
`Sheaf.RingTheory.LengthQuotSMulTopFractionFieldSubmodule`.
The proof uses Mathlib's principal-quotient finite-length theorem and a proved generic
private chain-lifting helper. For each finite strict chain in M/xM, that helper takes
finitely many representative lifts, spans them, and pulls the chain back to the quotient
of their finite span. Taking the supremum bounds the length of the arbitrary quotient.

Added two fully proved modules, each with one public theorem and a matching new DAG node:
`Sheaf.RingTheory.FGFractionFieldSubmoduleLatticePresentation` constructs an integral
full-rank lattice presentation of a finitely generated fraction-field submodule;
`Sheaf.RingTheory.LengthQuotSMulTopFGFractionFieldSubmodule` proves the finite-case bound.
The finite case uses the finite cokernel F/N and the exact sequences
0 → F/N → F/xN → F/xF → 0 and 0 → N/xN → F/xN → F/N → 0.
Additivity and cancellation of length(F/N) give length(N/xN) = length(F/xF).
Coordinate reduction then computes the latter length.

The item's added proof imports are `Mathlib.RingTheory.OrderOfVanishing.Basic` and
`Sheaf.RingTheory.LengthQuotSMulTopFGFractionFieldSubmodule`, both non-public.
Its existing signatures, universes, public imports and docstrings are preserved.
The existing theorem docstring records the original nine-step plan; the updated DAG,
new finite-case docstring and this report record the shorter implemented argument.
No existing definition or statement changed and no adaptation is needed.
The unit route is preserved: this is a refinement below the unit level of Stacks 00PE.

The local literature/stacks-project/algebra.tex file is absent on this machine. The
source proof was read directly at https://stacks.math.columbia.edu/tag/00PE.
LeanSearch was unavailable with Internal Server Error; actual LeanFinder, Loogle and
source searches are recorded in the new nodes. No unavailable search is treated as
an absence result.

## Proved and sorry left

Closed the one original hole:
`Submodule.length_quotSMulTop_le_of_ringKrullDim_eq_one_of_isLocalRing`
(node `lem-weil-pbc-dim-one-submodule-quotient-finite-length`).

Added zero holes. Fully proved the two new public declarations:
`Submodule.exists_lattice_presentation_of_fg`
(node `lem-weil-pbc-fg-fraction-submodule-lattice-presentation`) and
`Submodule.length_quotSMulTop_le_of_fg_of_ringKrullDim_eq_one_of_isLocalRing`
(node `lem-weil-pbc-dim-one-fg-submodule-quotient-length-bound`).
All private helpers are proved. No sorry remains in any delivered module.
This is a complete proof, not a decomposition into unproved intermediate statements:
net holes closed minus holes added is 1.

All three modules compile cleanly in dependency order through lcompile.py.
Explicit #print axioms on each public declaration reports only propext,
Classical.choice and Quot.sound. The temporary print commands were removed afterwards.
Edge cases covered by the Lean proofs: r=0, M=0, zero-dimensional K-span, empty finite
chains and generator families, and unit x. The general chain argument does not assume
M finitely generated or that N/xN → M/xM is injective; the chosen witnesses ensure
strictness of its inverse-image chain.

## No longer needed

`lem-weil-pbc-zero-locus-eq-iff-radical-eq` is pruned from this theorem's proof route.
Neither PrimeSpectrum.zeroLocus_eq_iff nor Ideal.radical_eq_sInf is used. The nonunit
case split, maximal-prime radical argument, power filtrations, powers-of-x sandwich
and asymptotic integer estimate of the original plan are unnecessary.
No existing Sheaf proof-dependency module was imported for these steps.
This does not claim that the radical node is unused by other parts of the project.

`lem-weil-pbc-length-additive-short-exact` remains needed in the finite-case node;
it is relocated below the item's new finite-case dependency, not pruned globally.
`def-weil-pbc-krull-dimension-ring` remains a statement dependency, with dimension
used through the Mathlib principal-quotient finite-length theorem.

No original import was removed: each existing public import supports the unchanged
public statement. Removed a redundant `public import Mathlib.LinearAlgebra.Pi` from
the new lattice module, because its public Finiteness.Basic import already provides it.
Every retained non-public import supplies proof declarations used in its module.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The original finite-case plan
was longer than needed: the finite cokernel allows exact finite cancellation, so
passing to powers of x and using radicals is unnecessary. The source's finite-cokernel
assertion is proved from dF ⊆ N and the already available finite-length principal
quotient theorem, without a new assumption. All original hypotheses and conclusions
remain exactly as written.

## New nodes

`lem-weil-pbc-fg-fraction-submodule-lattice-presentation`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-fg-fraction-submodule-lattice-presentation.json`.
A fully proved algebraic construction with no dimension, locality or Noetherianity
assumption. Finite basis coordinates, common denominators and span induction give
N ⊆ R^s containing dR^s and an R-linear equivalence to the given module.

`lem-weil-pbc-dim-one-fg-submodule-quotient-length-bound`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-dim-one-fg-submodule-quotient-length-bound.json`.
A fully proved finite-case bound, using the lattice construction, coordinate quotient
length, principal-quotient finiteness, two exact sequences and finite cancellation.

Both nodes inherit the item's chapter, unit and blueprint ancestor. The original node's
proof, proof_deps and proof_origin now follow the compiled proof.
There are no change records because no existing interface was changed.

## Second reading by X2

1. **Existing interfaces: pass.** Compared the delivered item with the read-only
   repository using diff and checked its existing theorem signature byte for byte.
   Universes, hypotheses, conclusion, visibility, public imports, and existing
   docstrings are unchanged. There are no adapted modules or changed definitions.
   The existing node changes only proof, proof_deps, and proof_origin.
2. **Proof and trust: pass.** Independently compiled all three modules in import
   order through lcompile.py, without errors or warnings (2.5–2.8 seconds each).
   Scratch copies with #print axioms for all three public theorems report exactly
   propext, Classical.choice, and Quot.sound. Scanned the delivered Lean for sorry,
   axiom, unsafe, opaque, implemented_by, extern, and sorryAx: none occur.
   Read every private helper, including denominator clearing, both quotient exact
   sequences, finite cancellation, coordinate reduction, and the strict-chain
   inverse-image construction. Choices use proved existence statements; no
   arbitrary object is chosen from an unproved theorem. Scratch copies were removed.
3. **Intermediate statements: pass.** No unproved statement is split off. The two
   new proved public statements are genuine subarguments: the lattice presentation
   requires neither dimension nor locality, and the finite-case bound assumes FG
   rather than proving the arbitrary-module case by another name. Checked r=0,
   M=0, s=0, unit x and d, and empty generator/chain families. The denominator
   products are nonzero even for empty families; finite-cokernel cancellation only
   cancels the finite summand; the chain map need not be injective. Independent
   LeanFinder search for torsion-free-module parameter multiplicity and Loogle
   search `Module.length, QuotSMulTop` found no replacement. Source searches in
   lean/Sheaf/RingTheory, lean/WeilConjectures/RingTheory and Mathlib Length/Lattice
   found components or downstream users, not either combined statement.
4. **Route and pruning: pass.** Read the source at
   https://stacks.math.columbia.edu/tag/00PE and the unit sk-thm-p1's realized fields.
   Clearing denominators and finite-chain lifting follow 00PE; the finite-cokernel
   argument validly shortens only the argument below the unit level. No realized
   unit step is bypassed. Public imports support signatures; each private import
   supplies proof declarations. All five old proof dependencies are accounted for:
   principal-quotient finiteness and length remain; Krull dimension remains a
   statement dependency used by finiteness; additivity moves to the finite-case
   node; the radical/zero-locus node is unused and listed under No longer needed.
5. **DAG agreement: pass.** Checked the three node records against the declarations
   and actual proof steps. Proof-dependency lists are the unions of step uses;
   the two new nodes have sources, complete proofs in words, searches, creation,
   blueprint ancestry, chapter/unit, and matching Lean records. Existing statement
   fields are unchanged. The agent attribution correctly identifies the
   two-exact-sequence refinement of the source argument.

Second reading changed only this report by adding the independent review record.
No mathematical, Lean, import, or node repair was necessary. Independently verified
one original hole closed and zero holes added; no split-off sorry remains.
