## What changed

Proved `Algebra.exists_principal_localization_presentation_of_local_generators` with its
signature unchanged. Added two general, fully proved algebraic tools in new modules:
`Sheaf.RingTheory.LocalGeneratorsClearing` and `Sheaf.RingTheory.QuotientAwayClearing`.
All new imports in the item are proof imports; its public imports and visibility are unchanged.
The proof clears the local generators, compares quotient localizations using their universal
properties, applies the already proved `Algebra.exists_localization_presentation` from
`Sheaf.RingTheory.EquationCountLocalizePresentation`, and reindexes variables and equations
using `finSuccEquiv`, `MvPolynomial.renameEquiv`, and `Ideal.quotientEquivAlg`.
The copied DAG node now records that route.

Source checked: Stacks Project, Algebra, Tag 00SC, `lemma-lci`, specifically the paragraph
clearing the local generators and adjoining the inverse variable. The repository's literature
file was absent on this machine; the source was read online and a copy of `algebra.tex` was
saved only in the sandbox scratchpad. The two new tools expand the algebra in that paragraph;
no dimension or regularity route is changed. Whole-blueprint searches for local generators,
quotient localization, denominator and 00SC found no duplicate statement of either new tool.
LeanSearch returned Internal Server Error for both new statements; LeanFinder, Loogle and
Mathlib source searches were performed and recorded in their nodes.

## Proved and sorry left

Closed the item's sole hole:
`Algebra.exists_principal_localization_presentation_of_local_generators`
(node `lem-weil-pbc-lci-regular-sequence-global-complete-intersection-presentation`).

Also proved from Mathlib, without adding any holes:
`Ideal.exists_clearing_of_local_generators`
(node `lem-weil-pbc-local-generators-clearing`) and
`Ideal.nonempty_quotient_away_equiv_of_clearing`
(node `lem-weil-pbc-quotient-away-clearing`).

No `sorry` remains in any delivered module. No deferred statement was split off.
The existing inverse-variable presentation used by the proof is already fully proved.
All three modules compile cleanly through lcompile.py. The delivery tool checks their axioms.

Edge cases: the clearing proof uses a product over a finite set, giving A=1 for an empty
set, and span induction also covers I=0. It does not require e>0. The comparison proof
assumes neither A nor B nonzero and works for zero rings. For B=0 both localized quotients
are zero rings, and the same universal-property argument applies. `finSuccEquiv` reindexing
works for n=0 and e=0. No extra hypothesis was introduced in any of these cases.

## No longer needed

No original proof imports were present to remove. The direct DAG dependencies
`lem-weil-pbc-polynomial-coefficient-map-kernel` and
`lem-weil-pbc-localization-away-polynomial-quotient` are no longer used: quotient and
localization universal properties replace the kernel/first-isomorphism-theorem argument.
`lem-weil-pbc-finite-type-algebra-noetherian` is no longer a direct dependency: the standard
Mathlib field and multivariate polynomial Noetherian instances give the required instance.
These three are Mathlib leaves, so no Sheaf statement module is pruned by their removal.
The polynomial-ring definition remains a direct dependency.
`def-weil-pbc-localization-at-prime` and `def-weil-ring-localization-away` also leave
the direct `proof_deps`, but remain needed through the clearing and comparison/presentation
tools respectively. This lists all five removed direct dependencies; no other planned branch
is omitted. During second reading the redundant public import
`Mathlib.RingTheory.Localization.Ideal` was removed from `LocalGeneratorsClearing`
(already supplied by `AtPrime.Basic`), and `Noetherian.Basic` was reduced to
`Noetherian.Defs`, which supplies both the signature and the finite-generation theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the statement or plan. The library already has a proved
inverse-variable presentation, so rebuilding a coefficient-map kernel proof was unnecessary.
The general quotient comparison gives the same algebraic identification more directly.
The item is not itself listed as a realization of a unit statement or step; its parent
LCI argument and the unit/chapter route are preserved. No existing statement, definition,
public import, target signature or other held module was changed.

## New nodes

`lem-weil-pbc-local-generators-clearing` records the fully proved common-multiplier theorem
for a finite family of generators of an ideal localized at a prime in a Noetherian ring.
Its module is `Sheaf.RingTheory.LocalGeneratorsClearing`.

`lem-weil-pbc-quotient-away-clearing` records the fully proved equivalence between the two
quotient localizations when A annihilates the difference of ideals. Its module is
`Sheaf.RingTheory.QuotientAwayClearing`. Both nodes have complete proofs, source, search
records and exact Lean signatures; neither is a new proof obligation. No change record
is required because no existing interface changes.

## Second reading by B3

1. PASS: diffed the existing module against the repository. Its sole theorem signature
   is byte-for-byte unchanged, as are all original public imports and visibility.
   The other two delivered modules and nodes are new. No definition, target, or
   existing statement was changed, and no change record is required.
2. PASS: read all three proofs and compiled each through lcompile.py in import order.
   Scratch copies with `#print axioms` for all three declarations show exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   No delivered module has `sorry`, forbidden declarations, or hollow definitions.
   All choices in the clearing proof use proved fraction-membership and finite-generation
   results; no data is chosen from an unproved existence theorem.
3. PASS: no deferred statements were split off. Both new helper theorems are fully
   proved, strictly smaller algebraic steps with matching nodes and proof docstrings.
   Independently checked e=0, n=0, I=0, J=I, A=0, B=0, and zero rings where allowed.
   For e=0 a nonzero I can vanish at p, so the multiplier need not be one: the Lean
   proof correctly produces an annihilator. Searches via msearch LeanFinder for stalk
   generators on distinguished opens and quotient maps with annihilated kernels,
   Loogle for localization/quotient equivalences and ideal spans, Mathlib grep, and
   rg over both library roots found component results but no duplicate helper.
   The uniform-annihilator module proves a related module result, not the numerator
   construction here; replacing this direct proof by it gives no shorter route.
4. PASS: read the already proved inverse-variable presentation and checked the
   composition and Fin/Option reindexing. This uses the shortest available presentation
   rather than rebuilding its kernel proof. Checked Stacks Tag 00SC, the source's
   clearing-and-inverse-variable paragraph. The item is absent from the unit's realized
   statement/steps, and no unit or chapter route is bypassed. Checked every old direct
   proof dependency against the report; the list is now explicit and complete.
   Public imports of the new helpers provide signature data, including the quotient
   algebra instance from `Quotient.Operations`; item additions are all proof imports.
5. PASS: checked every node signature verbatim against Lean, every dependency's
   existence, and that `proof_deps` equals the union of the proof steps' `uses`.
   The three node proofs and origins describe the actual fraction, common-product,
   localization-universal-property, and reindexing arguments.

Changes: removed the redundant Localization.Ideal import, reduced Noetherian.Basic to
Noetherian.Defs, corrected the clearing helper's docstring to distinguish an empty
generating set of I from an empty local-generator family, and completed the pruning
report with both removed direct definition dependencies. The proof terms were retained.
The original hole is closed; zero new holes are added, so this is a proof, not a decomposition.
