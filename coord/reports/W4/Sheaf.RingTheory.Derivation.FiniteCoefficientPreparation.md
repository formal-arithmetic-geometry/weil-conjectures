## What changed

Completed the recovered attempt in `Sheaf.RingTheory.Derivation.FiniteCoefficientPreparation`.
The unchanged theorem `Derivation.exists_finite_coefficient_derivation` now has a complete
Lean proof from normalization and relative differential detection. It proves that the detecting
hypothesis rules out a pth power, obtains a coefficient subring, separates its nonzero differential
by an M-linear functional, restricts the resulting derivation to the integers, and transports the
subring into B while proving finite type by composition and descent through a ring equivalence.
All added imports in this existing module are proof-only imports.

Added `Sheaf.RingTheory.Derivation.PowerSeriesPolynomialNormalization` with a complete proof of
`Derivation.exists_powerSeries_polynomial_normalization`. It uses the existing complete local
quotient, complete local domain finite over regular, and Noether normalization statements.
The remaining argument is Lean: exclude the Cohen-ring alternative in characteristic p,
construct the polynomial range, identify the fraction field after inverting g, and combine
algebraicity with essential finite type to obtain finite-dimensionality. The repaired scratch
proof had competing subalgebra scalar actions; explicit local scalar actions make the chosen
algebra tower consistent. It also had missing explicit localization and algebraicity parameters.

Added `Sheaf.RingTheory.Derivation.PowerSeriesPolynomialDifferential` with the remaining,
strictly smaller coefficient-subfield/differential step. It assumes a power-series polynomial
normal form and a finite field extension, and concludes a finite coefficient subring and a
nonzero relative differential. It assumes no detecting derivation, no complete local base,
and concludes neither finite type for B nor the desired derivation. Thus it is a part of the
argument, not a renamed version of the item. Its docstring and node give the full sourced proof.

Updated the item's proof DAG and added a node for each new module. No existing signature,
definition, public import, visibility, or target statement changed. Compiled all three modules
in import order with lcompile.py, with no errors or non-sorry warnings. Normalization and the
main proof were recompiled after removing unused/redundant proof imports.

## Proved and sorry left

Closed the original hole in `Derivation.exists_finite_coefficient_derivation`
(node `lem-weil-pbc-finite-coefficient-detecting-derivation`): 1 of 1 original holes closed.
There is no remaining sorry in the item's module.

The new `Derivation.exists_powerSeries_polynomial_normalization`
(node `lem-weil-pbc-power-series-polynomial-normalization`) has a complete proof from existing
library declarations. Those imported declarations may themselves depend on sorry; this is
not a claim that the normalization import closure is axiom-free.

Added one hole, and the only delivered sorry is
`KaehlerDifferential.exists_finite_subring_nonzero_differential`
(node `lem-weil-pbc-power-series-polynomial-nonzero-differential`). Its whole proof is `by sorry`.
The delivery closes one upper hole and adds one lower hole: it is a decomposition, with net
hole change zero before accounting for the imported dependency baseline, not an unconditional
proof of the target closure. No hole occurs in a definition or a private helper.

## No longer needed

No imports were removed from the repository version of the item: its existing public imports
are retained. The recovered normalization scratch imports `Mathlib.Algebra.CharP.Algebra`
and `Mathlib.RingTheory.EssentialFiniteness` were removed as redundant; their declarations
are available through the necessary imports `Mathlib.Algebra.CharP.Subring` and
`Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra`.

The planned dependency `lem-weil-pbc-finite-module-over-finite-algebra`
(`Module.Finite.trans`, Mathlib.RingTheory.Finiteness.Basic) is not needed by this proof.
The conclusion requires finite type, so the actual glue uses finite-to-finite-type,
`RingHom.FiniteType.comp`, and `RingHom.FiniteType.of_comp_finiteType` instead.
This removes that edge, not a claim that the node is unreachable from every other target.

The old direct edges to `lem-weil-pbc-complete-local-quotient`,
`lem-weil-pbc-complete-local-domain-finite-over-regular`,
`lem-weil-pbc-noether-normalization-over-domain`, and
`lem-weil-pbc-finite-algebra-is-integral` now occur in the normalization node.
The old direct edges to `lem-weil-pbc-p-basis-exists`,
`lem-weil-pbc-power-series-ring-subfields`, and
`lem-weil-pbc-intersection-subfields-differentials` now occur in the differential node.
The old direct edge to `lem-weil-pbc-p-basis-differentials-basis` is replaced by
`lem-weil-pbc-differential-zero-iff-pth-power`, which still uses it.
These nodes are not pruned: their arguments remain part of the reduction. In particular p-basis existence, power-series coefficient
subfields, and the intersection theorem are preserved; p-basis differentials are needed
through the existing differential-zero-iff-pth-power theorem. No unit statement or unit
proof step is bypassed. No other node or module is asserted to be pruned.

## Where the brief, the DAG or earlier work was wrong

The previous attempt was incomplete as a delivery: its two new modules lacked DAG nodes and
there was no report. Its main Lean proof compiled, but its substantial normalization scratch
proof had the scalar-action and parameter errors described above; these are repaired.

The original plan invokes a general relative differential kernel criterion, but the recorded
p-basis differentials declaration alone does not state that criterion. The split-off proof
uses the existing absolute perfect-field criterion and both clauses of 07P4 instead: the
finite extension clause gives intersection of the subfields M^p K_J equal to M^p, and the
kernel-intersection clause detects the absolute nonzero differential over one such subfield.
The universal property then detects it over the corresponding coefficient subring. This
preserves the coefficient-subfield route and does not assume a general kernel theorem.

The existing 07P5 interface takes the families k_J, C_J, K_J and their exact defining
conditions as arguments; it does not construct them. Constructing these families, transporting
through the normal-form ring isomorphism, and setting up their induced algebra structures
are included in the one remaining statement. No copy of the existing 07P5 conclusion is added.

The cited Stacks .tex files are absent in this read-only checkout. Read the source directly
at https://stacks.math.columbia.edu/tag/07PH,
https://stacks.math.columbia.edu/tag/07P4, and
https://stacks.math.columbia.edu/tag/07P5. The new natural-language proofs record their precise
places. Mathlib semantic searches, Loogle, and source grep found no exact shorter result;
LeanSearch returned Internal Server Error and is recorded as unavailable. Blueprint searches
for power series, 07PH, and nonzero differential found no duplicate blueprint statement.

Checked edge cases of the new statements: n=0 and m=0 simply remove their variables;
perfect k with n=m=0 makes the non-pth-power hypothesis impossible in a finite field
extension; an imperfect k with no variables still allows coefficient subfields. The
normalization statement permits noninjective R0-to-B by taking its proper prime-kernel
quotient. A fraction-field extension of degree one is allowed. The coefficient subring
map is always the given inclusion followed by C-to-M, with no unrelated algebra choice.

## New nodes

`lem-weil-pbc-power-series-polynomial-normalization`, module
`Sheaf.RingTheory.Derivation.PowerSeriesPolynomialNormalization`: the geometric/algebraic
preparation from 07PH's first two paragraphs. Proved from existing quotient, Cohen structure,
and normalization declarations, with the fraction-field and finite-type argument completed.

`lem-weil-pbc-power-series-polynomial-nonzero-differential`, module
`Sheaf.RingTheory.Derivation.PowerSeriesPolynomialDifferential`: the finite coefficient
subring with a nonzero differential, from 07PH's coefficient-subfield paragraph, 07P4,
07P5 and Algebra 031W. This is the sole split-off hole. Its proof steps name the existing
p-basis, power-series subfields, intersection subfields, perfect-field differential criterion,
and Kähler universal-property nodes. No change record is required: no existing interface changed.


## Second reading by W4

1. Compared the entire existing module with its repository version using `diff -u`.
   The only differences are four plain proof imports and the replacement of the original
   theorem's `sorry` body. Its signature, docstring, universes, public imports, namespace,
   and visibility are byte for byte unchanged. There are no existing definitions changed
   or forced adaptations. Verdict: passes.

2. Compiled all three delivered modules in import order with `lcompile.py --all`.
   All compile without errors or non-sorry warnings. Searched the delivered Lean for
   forbidden declarations and proof escapes; none occur. There are no definitions or
   private helpers and exactly one `sorry`, the named public differential theorem.
   Scratch probes with `#print axioms` for each of the three declarations show only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The normalization proof
   still uses open upstream theorems, and the main theorem uses the split differential
   theorem, so this is not an axiom-free closure claim. Verdict: passes as a decomposition.

3. Read both new statements against Stacks Tags 07PH, 07P4, and 07P5, and read the
   existing complete-local quotient, Cohen structure, normalization, p-basis,
   power-series subfields, intersection-subfields, and perfect-field differential
   interfaces. Normalization assumes exactly the original algebraic setup and produces
   a compatible finite fraction-field extension. The differential lemma assumes that
   normal form and extension, no detecting derivation or complete local ring, and
   supplies only the finite coefficient subring and nonzero differential. Each is a
   strict part of the original argument. In 07P4, use the finite-extension clause first
   to obtain intersection T_J = M^p, then the kernel clause on M; this avoids assuming
   an unstated relative kernel characterization. The coefficient-supported subring and
   fraction subfields must be constructed, not chosen as arbitrary witnesses from
   unproved existence. No delivered definition makes such a choice.
   Checked n=0, m=0, a perfect coefficient field with both zero (the non-pth-power
   hypothesis is then impossible), imperfect coefficients with no variables, degree-one
   extensions, and a noninjective base map (handled by its proper kernel quotient).
   Additional LeanFinder search for detection over a finite-index coefficient subring
   returned cotangent generator identities and KaehlerDifferential.finite, which do not
   detect a nonzero differential. Loogle `KaehlerDifferential.D, Module.Finite` returned
   no hits; grep `coefficient.*subring|subring.*differential|differential.*subfield`
   returned only unrelated polynomial subring results. Repository and upstream searches
   found no duplicate; the existing absolute-differential-to-derivation theorem has
   neither the relative base nor the coefficient finiteness conclusion. Verdict: passes.

4. Read the proof from the original theorem downward. The non-pth-power argument is
   the Leibniz formula in characteristic p. The normalization proof takes the image
   quotient, excludes the Cohen-ring alternative, and constructs the polynomial range;
   its explicit denominator calculation identifies M as Frac(B0), then algebraicity
   and essential finite type give finite dimension. The main proof separates df by a
   linear functional and transports the coefficient subring into B; finite-type
   composition and descent across its image equivalence give exactly the conclusion.
   All added imports of the existing module are plain imports, and the normalization
   imports correspond to declarations used in its proof. No shorter matching result
   was found. Inspected `dag/units/sk-thm-p1.json` realized statement and steps: these
   helper nodes are below the unit level, and the unit route is unchanged. Completed
   the pruning report by explicitly listing all old direct edges moved into the new
   helpers or replaced by the perfect-field differential criterion. No module is
   claimed pruned. Verdict: passes.

5. Read the three node proofs and their dependency union against the Lean and the
   sourced proof of the remaining hole. The original node uses normalization,
   coefficient differential detection, vector-space separation, and the Kähler
   universal derivation, exactly as its proof does. The normalization node names
   the quotient, regular-subring, normalization, and integrality inputs. The remaining
   node names p-basis existence, 07P5, both clauses of 07P4, the perfect-field criterion,
   and the universal property, with a complete natural-language argument. Both new
   nodes include source, creation, blueprint ancestry, searches, chapter/unit, and
   Lean records. Corrected the new nodes' Lean statement fields to preserve the
   exact multiline theorem signatures rather than whitespace-flattened copies.
   Verdict: passes.

Second reading changed only the two new nodes' signature formatting and the report's
explicit accounting of replaced direct dependency edges. No Lean proof needed repair.
One original hole closed and one lower hole added; this remains a decomposition.
