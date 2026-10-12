## What changed

Proved `Algebra.exists_popescu_universal_standardizer` in
`Sheaf.RingTheory.PopescuUniversalStandardizer`. Added the proved coefficient-open lemma
`Algebra.popescu_standardizer_coefficient_smooth` in
`Sheaf.RingTheory.PopescuStandardizerSmoothOpens`. All existing signatures and public
imports are unchanged; no other existing module is adapted.

The quotient B is constructed explicitly from the displayed polynomials and raised to
Type(max u v) by ULift. Its presentation is transported from Mathlib's naive quotient
presentation. Finite generators of the singular ideal come from Noetherianity.
The coefficient-open lemma proves formal smoothness by the square-zero lifting criterion:
lift the coefficient map from A[1/a_j], lift each z_il, and correct z_ij by the discrepancy
divided by the unit alpha(a_j). The correction reduces to zero, satisfies every relation,
and gives a map on B and then its localization. Coefficients and generators verify that
its reduction is the original map. Finite presentation gives smoothness.

For each variable open, evaluate the relation to place x_i^(2N) in the singular ideal;
radical membership and `smooth_localization_of_mem_singularIdeal` give smoothness.
The existing proved construction in `ImprovePresentation` supplies the explicit symmetric
algebra and its retraction. Finite free differentials give strict-standard power bounds,
and max(1, sup_i e_i) gives the common positive exponent, including d=0.
Private proved helpers establish strict standardness of zero using the relation-ideal
square and specialize the stable-freeness power criterion to finite free differentials.
Localization tensor base change, ideal maps and radicals prove the Popescu-ideal inclusion;
`standardElements_baseChange` proves the standardness assertion after base change.

Added proof imports of `PopescuStandardizerSmoothOpens`, `SingularIdealLocalizationSmooth`,
`ImprovePresentation`, `SmoothFreeDifferentialsStrictlyStandardPower`,
`StrictlyStandardBaseChange`, Mathlib's finite free modules and localization base change.
The new module imports `SingularIdealLocalizationSmooth` for its proof.
Both node copies record the actual proof routes.

## Proved and sorry left

Closed: `Algebra.exists_popescu_universal_standardizer`
(node `lem-weil-pbc-popescu-universal-standardizer`), the item's sole original hole.
Added holes: none. There is no sorry in either delivered module.
New proved theorem: `Algebra.popescu_standardizer_coefficient_smooth`
(node `lem-weil-pbc-popescu-standardizer-smooth-opens`).
This is a proof from existing declarations, not a decomposition into new admitted lemmas.
The item's direct hole count changes from 1 to 0, with no lower hole added.

Both modules compile with no warnings. `#print axioms` for the coefficient-open theorem
lists only propext, Classical.choice and Quot.sound. The main theorem additionally inherits
the existing sorryAx from its downstream proof dependencies, which remain future items;
no new axiom or admitted declaration was introduced. The delivery dry run performs its
own declaration and axiom probes.

Edge cases: for d=0 the exponent is 1 and there are no variable opens or relations to
correct. For s=0 the coefficient assertion is vacuous and each variable power is zero
by its relation; its variable localization is smooth by radical membership.
Zero is strictly standard by the kernel-square calculation, without assuming any ring
nontrivial. The lifting proof also handles zero target rings. All carriers of the main
construction have the required universe. The improved carrier is the existing explicit
symmetric-algebra construction; it is not arbitrary data from an admitted existence lemma.

## No longer needed

No existing import was removed: the original three public imports are needed by the
unchanged statement. The following original proof dependencies are no longer directly
needed by the main theorem or the new coefficient-open theorem:

- `lem-weil-pbc-polynomial-ring-smooth`;
- `lem-weil-pbc-smooth-ring-map-principal-localization`;
- `lem-weil-pbc-smooth-ring-map-local-on-cover`.

The coefficient-open proof uses lifting and an explicit correction instead of a polynomial
algebra equivalence and smoothness of that polynomial extension. The variable-open proof
uses the singular ideal and its radical property instead of constructing a principal
cover. These three nodes are removed from the item's proof_deps. They are Mathlib leaves,
so there are no corresponding Sheaf proof modules to remove. The imported
`SingularIdealLocalizationSmooth` may itself use locality deeper in the library;
no claim is made that all three facts disappear from the entire targets' closure.
No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan's coefficient elimination is not the conclusion of an existing stated declaration.
It is now a proved local theorem. It was sufficient to implement the elimination as a
correction in the infinitesimal lifting property, rather than constructing a full algebra
equivalence with a polynomial ring. The remaining planned interfaces fit the proof.

The local source .tex is absent on this machine; Stacks Tag 07FJ was read online, including
Ad item-strictly-standard and Ad item-first-solve. LeanSearch returned HTTP 500 and is
recorded as unavailable. Loogle, LeanFinder, Mathlib grep and repository searches ran.
A whole-blueprint keyword search for standardizer returned no match. The new node retains
the item's recorded blueprint ancestry and names the exact coefficient-elimination step.

## New nodes

`lem-weil-pbc-popescu-standardizer-smooth-opens`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-popescu-standardizer-smooth-opens.json`,
states and proves smoothness of the coefficient opens of any presentation having the
specified linear relations. Its public declaration is in
`Sheaf.RingTheory.PopescuStandardizerSmoothOpens`. It supplies no generators, quotient
carrier, improved algebra, retraction, standard powers, tensor-base-change assertions,
or Popescu-ideal conclusion. The proof follows the coefficient elimination of Stacks
07FJ through the square-zero lifting criterion. It uses the existing Mathlib leaf nodes
for lifting smooth maps and deriving smoothness from lifting plus finite presentation.
No change record is required: no existing public interface was changed.

## Second reading by A2

1. I compared both delivered Lean modules with the repository versions. Existing
declaration signatures are unchanged; the main module only changes proofs/imports,
and the added coefficient-open module contains the new split-off declaration.

2. I compiled each delivered module with `lcompile.py`; both compile without errors or
warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by` declarations in the delivered Lean files. The proof uses only the
permitted kernel axioms, aside from `sorryAx` inherited by still-open dependencies.

3. The new coefficient-open statement is a strict intermediate result: it asserts only
smoothness of each specified coefficient localization, and is not a restatement of the
universal-standardizer target. Its docstring gives the square-zero lifting proof and its
node records the source, route, dependencies, and exact Lean declaration.

4. The proof follows the unit route through the explicit quotient presentation,
coefficient opens, improved presentation, strict-standard powers, and tensor base
change. It uses shorter local arguments where available and removes three unused
proof dependencies from the item's node; no unit statement or realized step is
bypassed.

5. The DAG records agree with the Lean proof: the item node's proof and dependencies
include the explicit quotient, coefficient-open lemma, improved presentation,
free-differential power bound, and base-change steps, while the new node records its
own coefficient-elimination proof. The new theorem is true in the edge cases
`d = 0` and `s = 0` as documented.

I changed only the report by adding this second-reading record; no proof or statement
needed repair after compilation and diff review.
