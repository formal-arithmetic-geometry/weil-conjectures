## What changed

Replaced the original hole in `Sheaf.RingTheory.PopescuDelocalizeBase` with a compiling
construction. The existing public signature and docstring are unchanged. The proof uses
`Algebra.Smooth.exists_standardSmooth_retract`, composes the retraction with the given
factorization, chooses a finite presentation of `A`, and applies
`Algebra.exists_standardSmoothPresentation_include_generators`.

Added the proof-only import `Sheaf.RingTheory.PopescuDelocalizeCertificate`. Its polynomial
certificate supplies equations, evaluation identities, a Jacobian congruence and ideal
memberships. The main proof explicitly constructs the quotient (with `ULift` to satisfy
the original universe), proves its finite presentation, descends both maps through their
kernels, and checks their composite on the original generators. A proved private helper
verifies the elementary-standard definition, including the difference between the chosen
presentation section and the constant lift and its contribution to the square ideal.

Added `Sheaf.RingTheory.PopescuDelocalizeDenominators`, containing only the rescaling and
coefficient/equality-clearing data of steps 4-9. The certificate theorem is proved from
this data: span induction and products with one factor omitted verify the remaining
relations, and differentiation plus determinant multilinearity verifies the Jacobian
congruence. The main proof then carries out step 10 and the final definition check of
step 11. Both new modules have their own nodes; the original node's proof and dependencies
now follow this route. There are no changes to existing interfaces or forced adaptations.

## Proved and sorry left

Closed the one original hole:
`Algebra.exists_factorization_isElementaryStandardElement_of_localized_smooth`
(node `lem-weil-pbc-popescu-delocalize-base`). It has no direct `sorry` and is proved from
the existing retract and prescribed-generator statements and the new polynomial data.

Also proved `Algebra.exists_delocalization_polynomial_certificate`
(node `lem-weil-pbc-popescu-delocalize-certificate`), with no direct `sorry`.
The private helpers `Algebra.elementary_of_polynomial_certificate` and
`Algebra.product_mul_mem_scaled_span` are proved without holes.

Added exactly one remaining hole:
`Algebra.exists_delocalization_denominator_data`
(node `lem-weil-pbc-popescu-delocalize-denominators`), whose entire proof is `by sorry`.
It supplies only polynomial equations, target-variable values and individual denominators
before either factorization map or the final quotient is constructed. Its docstring gives
the rescaling and denominator-clearing proof. This is a decomposition, not a complete
sorry-free proof: one upper hole closed and one lower hole added, net zero. The already
existing retract and prescribed-generator declarations are also unproved dependencies;
their holes are neither added nor modified here.

All three modules compile together in import order with `lcompile.py`, with no warnings.
The declaration signatures were compared with the node records and the original signature.
The formulas use empty products and the empty determinant, so zero generators or relations
are allowed. No nonzero-denominator or nontrivial-ring hypothesis has been introduced:
the localization equality/kernel criterion also handles `0 ∈ S`. The certificate proof
handles the initial and remaining index blocks explicitly, including either empty block.
The quotient and its maps are constructions; no public definition chooses data from a
new unproved existence theorem.

## No longer needed

No original Lean import was removed: both original proof-only imports are used.
No existing library module is pruned.

The original node no longer directly invokes
`lem-weil-pbc-polynomial-scalar-extension` or `lem-weil-pbc-localization-base-change`;
these remain needed in the denominator-data node, so they are not pruned from the argument.
The same applies to the localization definition used in that step. The new intermediate
route separates these dependencies from the fully written quotient and determinant proofs.

Deleted the two unlanded modules and node copies of the earlier attempt:
`Sheaf.RingTheory.PopescuDelocalizeData` / `lem-weil-pbc-popescu-delocalize-data` and
`Sheaf.RingTheory.PopescuDelocalizeElementary` / `lem-weil-pbc-popescu-delocalize-elementary`.
They are not imports or dependencies of this delivery. Their removal is not counted as
pruning existing library modules.

## Where the brief, the DAG or earlier work was wrong

The earlier `elementary_standard_of_localized_factorization` claimed the elementary
condition for an arbitrary finitely presented factorization algebra, even though the
smoothness hypothesis constrained only the localized intermediate algebra. That claim
loses the required relation between the factorization algebra and the denominator-clearing
construction. The earlier data theorem supplied an unrelated factorization and could not
repair that omission. Both statements and their old review text have been removed from
the sandbox delivery. The objection does not invalidate the original theorem or the
source proof; it invalidates that split. The new data is tied to explicit equations and
the quotient is built from those very equations in the main proof.

The local checkout does not contain `literature/stacks-project/smoothing.tex`; the source
proof was read at https://stacks.math.columbia.edu/tag/07F4, including the explicit quotient,
the choice of all denominators and the final determinant identity. The canonical source
path is retained in the nodes. The source's displayed `(f_1, ..., x_c)` is the already
recorded typo for `(f_1, ..., f_c)`. No additional error in the original statement was found.
The source's rescaling and denominator-clearing sentences remain the sole new hole, with
their full proof described in the denominator-data docstring.

Searches ran through `msearch.py`: LeanFinder found standard smooth presentations and
localization-away lemmas, but no descent certificate; grep found
`Presentation.exists_presentation_fin`, used in the proof. LeanSearch returned HTTP 500
and is recorded as unavailable, not as a no-match search. Blueprint searches for
`delocaliz` and `denominator` and source searches found no existing node with either new
polynomial-data statement. The unit's realized statements and steps are unchanged.

## New nodes

`lem-weil-pbc-popescu-delocalize-denominators` corresponds to
`Sheaf.RingTheory.PopescuDelocalizeDenominators` and its one remaining named hole. It is
strictly the rescaling and individual denominator data before the quotient construction.

`lem-weil-pbc-popescu-delocalize-certificate` corresponds to
`Sheaf.RingTheory.PopescuDelocalizeCertificate`. Its theorem constructs the scaled equations
and proves the product identities from the denominator data. It is not another hole.
Both inherit the original chapter and unit and identify the original blueprint ancestor.
No change record is needed: all existing signatures and public imports are unchanged,
and the only additions to the existing module are a private proved helper and a proof-only
import.

## Second reading by P1

1. Compared the delivered `PopescuDelocalizeBase.lean` with the repository using
   `diff -u`, then compared the original theorem signature byte for byte by an
   assertion. It is identical, as is its original docstring. The only original-module
   changes are its proof, one proved private helper, and the proof-only certificate
   import. There are no existing definitions changed, no public import changes, and
   no forced adaptations. Verdict: the original statement is preserved.

2. Read all three delivered modules and compiled them in import order through
   `lcompile.py --all`; all passed without warnings. The only direct `sorry` is the
   entire proof of `Algebra.exists_delocalization_denominator_data`. No axiom, unsafe,
   opaque, extern, implemented_by, skipped kernel check, or holed definition occurs.
   The quotient, generators, relations and descended maps in the original theorem
   are explicit constructions inside a proof of existence; no definition obtains
   arbitrary data from an unproved existence theorem. The scratch axiom prints for
   the original theorem and both new public theorems show only `propext`,
   `Classical.choice`, `Quot.sound`, and the expected `sorryAx`. Delivery's full probe
   additionally checks private helpers. Verdict: a valid decomposition, with one
   original hole closed and one new lower hole added, net zero; not a complete proof.

3. Read Stacks Tag 07F4 at https://stacks.math.columbia.edu/tag/07F4 and matched the
   two new statements to its construction. The denominator statement has no quotient,
   finite-presentation conclusion, factorization maps over R, or elementary-standard
   conclusion: it is strictly the variable rescaling and polynomial denominator data.
   Its hypotheses include the specified presentation kernel, the unit initial minor,
   `hmap`, the first-generator compatibility `hval`, and `hfactor`; these suffice.
   In particular scaling variables within the selected minor only scales its rows by
   units. Coefficient clearing scales columns by units. Residual localization kernels
   must be annihilated rather than assuming injectivity; the expanded docstring now
   gives that argument explicitly. For `0 ∈ S`, one may take all equations zero,
   `s₀ = 0`, all clearing elements zero, and extra target values zero. For `c = 0`,
   the empty determinant is 1; original relations that vanish after localization
   still have the required annihilators. Empty generator and remaining-relation
   blocks are covered by `Fin.addCases` and empty products in the certificate proof.
   No nontriviality assumption is needed. The certificate's evaluation proof fixes
   original generators; its determinant multiplies by the product of the `sf`, and
   its final span calculation uses each `sg` factor exactly once. Verdict: both
   statements are true and sufficiently strong, with only the denominator one open.

   Independent searches used different queries with `msearch.py` LeanFinder, Loogle,
   and grep. Loogle found `MvPolynomial.isLocalization` (read in
   `Mathlib/RingTheory/MvPolynomial/Localization.lean`); LeanFinder found
   `SubmersivePresentation.exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one`
   and `ofHasCoeffs` (read in Presentation/Core.lean). These are useful parts of a
   future proof, not matches for the full new statement: `ofHasCoeffs` also requires
   faithful scalar extension and coefficients already in the base, which cannot
   replace arbitrary localization with torsion. Searched repository and upstream
   RingTheory sources for delocalization and denominator constructions. Read the
   nearby `exists_cleared_submersive_presentation` and
   `exists_homogenized_local_equations`: they assume prime localizations, and the
   homogenization adds variables, so neither proves this statement for arbitrary S
   with the fixed indices. No duplicate statement was found. Closing this sole lower
   hole requires formalizing the substitution and clearing operations, beyond a
   short review repair; it remains explicitly open.

4. Read the proof top downward: standard-smooth retraction, prescribed-generator
   presentation, polynomial certificate, explicit quotient and its two maps, then
   the elementary-standard conditions. The helper correctly accounts for the chosen
   presentation section: its difference from the constant lift belongs to the kernel,
   and multiplication by a relation lands in the square ideal. Each original
   proof-only import and the added certificate import is used. New public imports
   provide types or operations in the new statements; the denominator import in the
   certificate is proof-only. Compared old and new `proof_deps`: the removed direct
   dependencies are `def-weil-pbc-module-localization`,
   `lem-weil-pbc-polynomial-scalar-extension`, and
   `lem-weil-pbc-localization-base-change`, all recorded under No longer needed and
   retained in the denominator node. No existing module is pruned. Read
   `dag/units/sk-thm-p1.json`: none of its realized statement or step nodes is
   bypassed or edited; this is an internal reduction below that unit. Verdict: the
   route and pruning record agree with the written proof.

5. Compared each new Lean theorem signature with its node's verbatim Lean record,
   and read all three node proofs and their dependency lists. The original node
   changes only `proof`, `proof_deps`, and `proof_origin`; its statement, Lean record,
   chapter, and unit stay unchanged. The two new nodes have sources, created records,
   blueprint ancestry, actual search records, and the original chapter/unit. Their
   proof dependency lists are the unions of their step citations. The denominator
   node records rescaling, equation clearing, inverse-minor identity, original
   relation membership, and evaluation annihilators. The certificate node records
   the proved product, differentiation and span-induction calculations. Verdict:
   the DAG agrees with the delivery.

Changes in this reading: expanded the denominator theorem's natural-language proof
with the actual inverse diagonal substitutions, row scaling, common denominator,
residual-kernel annihilator, and resulting exact polynomial identity; updated the
corresponding two node proof steps. No Lean signature, executable proof, or import
was changed. Added this independent review and scratch axiom checks.
