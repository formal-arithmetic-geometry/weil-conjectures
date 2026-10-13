## What changed

Repair of the returned duplicate-completeness helper: removed the ring-specialized
private Algebra.complete_of_nilpotent from SquareZeroCoefficientAdjustment. Replaced
it in place by the proved private Algebra.complete_of_power_annihilates, for an
arbitrary R-module M with I^N M=0. This is strictly more general: I itself need not
be nilpotent. Both calls specialize it to regular modules using the already proved
nilpotence witnesses. Updated step 4 of the square-zero node accordingly. No new
hole or public interface change was introduced by this repair.

Kept Algebra.exists_nilpotent_coefficient_adjustment and its public imports unchanged.
Added a private, complete induction on the nilpotence exponent, with a fixed residue
field K throughout. The n=0 contradiction and n=1 inverse-residue-map case are proved.
The induction constructs the quotient by m^n, its local structure, residue surjection,
generating finset, and vanishing nth power in Lean. It then uses the new proved theorem
Algebra.exists_square_zero_coefficient_adjustment.

New module Sheaf.RingTheory.SquareZeroCoefficientAdjustment proves the annihilated-layer
lifting step. It lifts the specified quotient section using
RingHom.exists_lift_of_field_charP. It constructs the restricted coefficient subring,
factors the quotient image by its kernel, proves this kernel nilpotent, and lifts the
structure map from k into that subring using the same field-lifting theorem.
After finite-rank correction, it proves generation by all residue coefficients using
adic completeness for nilpotent ideals and surjective_of_mk_map_comp_surjective.
Closure induction extracts finitely many coefficients for each error generator and
finite unions handle all errors. Finally, a proved scalar-action calculation using
mI=0 shows the whole k-span of the errors lies in the enlarged coefficient subring.

New module Sheaf.RingTheory.FiniteRankCoefficientCorrection states precisely the
remaining Jacobi--Zariski/derivation step. Its input includes an actual lifted section,
an actual ring map psi agreeing with the structure map modulo I, and a fixed finite
coefficient model for psi. Its output has only a finite k-linear error, with all
errors in I; it does not assert the desired finite-coefficient containment.

Updated the original DAG proof to the fixed-field induction and added matching DAG
nodes for both new public theorems. All proof imports are non-public. No existing
statement, definition, public visibility, or public import was changed, and no
adaptations are required.

## Proved and sorry left

Closed the original hole in Algebra.exists_nilpotent_coefficient_adjustment
(lem-weil-pbc-nilpotent-coefficient-adjustment), from one strictly smaller remaining
step. This is a decomposition, not a net elimination of holes: one old hole closed,
one new hole added, net zero.

Algebra.exists_square_zero_coefficient_adjustment
(lem-weil-pbc-square-zero-coefficient-adjustment) is completely proved from the existing
field-lifting theorem and the remaining finite-rank correction theorem. Its private
helpers and the original module's induction contain no sorry.

The only sorry added or left in the delivered sources is
Algebra.exists_finite_rank_coefficient_correction
(lem-weil-pbc-finite-rank-coefficient-correction). Its whole proof is by sorry; the
source and the complete basis/derivation argument are in its docstring and node.
It carries no nilpotence hypothesis or conclusion of finite coefficient containment.

Validation: all three modules compile together through lcompile.py, in dependency
order, without warnings. Existing theorem signatures were compared with the repository.
The residue-field universe matches the ambient local-ring universe; the private
induction works for every local algebra in that universe, including its quotients.

## No longer needed

The assigned module replaces the private proof imports
Sheaf.RingTheory.ExistsLiftOfFieldCharP and
Sheaf.RingTheory.JacobiZariskiHomologySequence with
Sheaf.RingTheory.SquareZeroCoefficientAdjustment and
Mathlib.RingTheory.LocalRing.RingHom.Basic. Its public statement imports are unchanged.
Field lifting remains imported by SquareZeroCoefficientAdjustment; the Jacobi--Zariski
sequence is part of the remaining correction theorem's recorded proof plan. No existing node or module is claimed globally pruned. The original proof
plan's direct dependencies have been moved to the exact remaining step that needs
them, rather than discarded: field lifting is used by SquareZeroCoefficientAdjustment,
and Jacobi--Zariski and Kahler differentials are needed by FiniteRankCoefficientCorrection.
The polynomial-ring dependency def-weil-pbc-mv-polynomial-ring is no longer needed on
this route: the lift of tau is made into the already constructed coefficient subring
S, using S/ker(S -> Lambda/I), rather than a truncated polynomial algebra. Ring closure,
first isomorphism, and nilpotence of the contracted maximal ideal suffice. Its module
Mathlib.Algebra.MvPolynomial.Basic is not directly imported for this step; this makes
no claim that it is absent transitively from Mathlib or the target closure.
The original direct proof dependencies def-pc-field-extension and
 def-weil-pbc-smooth-ring-map remain statement notions and are inherited by the new
nodes. No unit statement or realized unit step is bypassed.

The complete list of old direct proof_deps absent from the new direct list is
 def-pc-field-extension, def-weil-pbc-smooth-ring-map,
 lem-weil-pbc-field-char-p-nilpotent-lifting,
 def-weil-pbc-kahler-differentials,
 lem-weil-pbc-jacobi-zariski-homology-sequence, and
 def-weil-pbc-mv-polynomial-ring. Only the last is unused throughout this new route;
 the others remain statement notions or are used in the lower steps described above.

## Where the brief, the DAG or earlier work was wrong

The first delivery duplicated the private Algebra.complete_of_nilpotent already
stated in Sheaf.RingTheory.ArtinianCoefficientPresentation. That theorem cannot be
imported here: it is private, and ArtinianCoefficientPresentation imports the
assigned NilpotentCoefficientAdjustment module, which imports the square-zero
module. The return's permitted generalization is used instead. The replacement
assumes I^N M=0 for an arbitrary module, rather than nilpotence of I and M=R;
for example a nonnilpotent ideal can annihilate a quotient module. It also covers
the zero module and exponent zero. The proof uses only congruence at N to show
separation and stabilization. The private signature is explicit, and no existing
library module needs adaptation. The prior second reading below predates this
repair; the next reader must check the generalized helper and its two calls.

No mathematical error was found. The DAG's elementary labels hide substantial Lean
glue for nilpotent quotients and finite coefficient extraction; that glue is now proved.
Keeping K fixed avoids transporting H1Cotangent finite dimensionality across quotient
residue-field identifications. The source's truncated polynomial lift can be replaced
below the unit level by the coefficient-subring quotient lift described above.

The local Stacks source path literature/stacks-project/smoothing.tex is absent on this
machine, so Tag 07FG was read at https://stacks.math.columbia.edu/tag/07FG. LeanSearch
returned Internal Server Error for both new statements and is recorded as unavailable;
LeanFinder and grep found no matching lemma. Blueprint searches for 07FG and derivation
found no duplicate blueprint statement (the latter returned six unrelated nodes).

Edge cases: when I=0 the finite-rank correction allows sigma=sigma0, f empty and
b=psi(a); when k=K its discrepancy extends itself and the corrected error is zero.
When t is empty, m=0, and the induction uses the proved base case. An exponent zero
is contradictory for a nontrivial local ring and is eliminated in Lean. Nilpotence of
the maximal ideal is used only for lifting and generation, not assumed by the
finite-rank correction theorem. No arbitrary data are selected from a holed existence
theorem to define an object: all selections are local witnesses inside theorem proofs.

## New nodes

lem-weil-pbc-square-zero-coefficient-adjustment records the now proved lifting of an
already adjusted coefficient section through an ideal annihilated by the maximal
ideal. Its conclusion preserves the input section modulo that ideal. The proof uses
the existing characteristic-p field lift, complete-source surjectivity, and the new
finite-rank correction, plus the proved ring-closure and scalar-action calculations.

lem-weil-pbc-finite-rank-coefficient-correction records the remaining correction of a
lifted section by a derivation, leaving a finite k-span of errors in I. Its proof
follows the Jacobi--Zariski paragraphs of Tag 07FG. No coefficient enlargement or
nilpotent induction is part of this remaining theorem. No change records are needed.

## Earlier second reading (a previous round; superseded)

1. **Interface unchanged: pass.** Read the complete diff of
   NilpotentCoefficientAdjustment against the repository. The existing declaration
   Algebra.exists_nilpotent_coefficient_adjustment has byte-for-byte identical
   signature, docstring, visibility and public imports. The only additions are the
   private fixed-K induction, its two private proof imports and the theorem body.
   Both other modules are new; there are no existing definitions or forced adaptations.
   The existing node differs only in proof, proof_deps and proof_origin.

2. **Proof and trust: pass, conditional on the named remaining theorem.** Compiled
   all three files in dependency order with lcompile.py without errors or warnings.
   Separately compiled scratch copies with #print axioms for all three public theorems:
   each reports propext, Classical.choice, Quot.sound and sorryAx, with no other axiom.
   The source scan finds exactly one sorry, the complete named theorem
   Algebra.exists_finite_rank_coefficient_correction. No axiom, unsafe, opaque,
   implemented_by, extern, skipped kernel checking or holed definition is present.
   All witness choices occur locally in theorem proofs. Thus one original hole is
   closed syntactically and one smaller hole added: decomposition, net zero, not an
   unconditional proof of the original theorem.

3. **New statements: pass.** Read Stacks Tag 07FG at
   https://stacks.math.columbia.edu/tag/07FG, specifically the coefficient claim,
   section/map lifts, differential basis, Jacobi--Zariski and finite-error paragraphs.
   The square-zero theorem takes the already adjusted quotient section as input and
   preserves that section modulo I; its proof establishes every output clause.
   The remaining theorem assumes actual sigma0 and psi, agreement modulo I and
   containment in the fixed coefficient closure; it concludes only a finite k-span
   error in I. It neither repeats finite-coefficient containment nor asserts the
   nilpotent induction. From hI and hkill, I squared is zero. The section makes r
   surjective and equips I with K-scalars; hcomm identifies these restricted scalars
   with the given k-action. The discrepancy product identity is therefore a
   derivation. Finite dimensional H1 bounds the differential-map kernel, whose
   finite basis support permits extension of theta away from those finitely many
   coordinates. Closure reevaluation is x -> x + D(r(x)); the product rule and
   mI=0 prove multiplicativity, and this fixes t and maps sigma0 coefficients to
   sigma coefficients. This validates the docstring's last step without assuming
   polynomial expressions are unique.

   Small cases checked: I=0 forces psi=i and allows sigma=sigma0, f empty; k=K
   allows D=theta and eliminates the error; empty t forces m=0, hence I=0.
   The n=0 contradiction and n=1 inverse residue map are explicit Lean branches.
   The correction requires no nilpotence of m: annihilation suffices for its argument.
   Each new node has its source, complete proof, searches, creation, blueprint,
   chapter/unit and verbatim Lean statement records. Independent msearch LeanFinder
   (field derivation modulo finite-dimensional cotangent obstruction), Loogle
   (nilpotent ideal / adic completeness) and grep (derivation extension / finite
   derivation) found no theorem closing this correction. Read Mathlib
   FieldTheory/Differential/Basic and Kaehler/Basic and JacobiZariski; the differential
   field extension result is characteristic zero, while the latter files supply
   universal derivations and adjacent exactness, not this correction. Searches of
   lean/Sheaf, lean/WeilConjectures, upstream RingTheory and the DAG found no duplicate.
   FiniteCoefficientPreparation concerns detecting a non-pth-power via a derivation,
   not adjusting a residue section. Closing the remaining hole needs substantial
   module-action and basis glue, not a short application, so it remains named.

4. **Route and pruning: pass.** Read the fixed-field induction from its base cases
   down through the quotient local structure and power computation; the only
   non-elementary induction call is the stated square-zero lift. Read its helpers:
   the restricted closure map and first isomorphism construct psi, nilpotent adic
   completeness plus complete-source surjectivity prove full generation, closure
   induction extracts finitely many coefficients, and hscalar/hspan absorb every
   k-linear error using mI=0. The Mathlib surjectivity declaration is the exact
   statement of lem-weil-pbc-complete-source-surjective-mod-ideal; field lifting
   uses RingHom.exists_lift_of_field_charP with the required positive exponent and
   characteristic assumptions. Imports are either needed by the signatures or
   private proof imports. Read dag/units/sk-thm-p1.json realized: neither this item
   nor either new node replaces a realized unit statement or step; the parent route
   still calls the same fixed-generator claim. No global module is claimed pruned.
   For completeness, every old direct proof dependency absent from the new list is:
   def-pc-field-extension and def-weil-pbc-smooth-ring-map (statement notions),
   lem-weil-pbc-field-char-p-nilpotent-lifting (moved to square-zero lifting),
   def-weil-pbc-kahler-differentials and
   lem-weil-pbc-jacobi-zariski-homology-sequence (moved to the remaining correction),
   and def-weil-pbc-mv-polynomial-ring (unused on the new subring quotient route).

5. **DAG alignment: pass.** The original node's three steps match exponent induction,
   quotient construction and the square-zero call. The square-zero node's six steps
   match section lifting, psi construction, finite-rank correction, complete-source
   generation, finite coefficient extraction and scalar absorption. Its uses include
   precisely the field lift, correction and complete-source surjectivity nodes.
   The remaining node's proof is the Tag 07FG derivation argument, not claimed Lean
   code; its proof_deps name differentials and Jacobi--Zariski. All proof_deps are
   the unions of uses, and proof_origin identifies the corresponding source route.

Changed in this reading: corrected step 2 of the new square-zero theorem's docstring
from the unused truncated-polynomial construction to the actual restricted coefficient
subring, kernel quotient and first-isomorphism lift. No signature or proof was changed.
Added this review and the explicit accounting of all retired direct DAG dependencies.


## Second reading by P3

1. **Interface: pass.** Compared all delivered modules with the repository. Only
   NilpotentCoefficientAdjustment already exists. Its public imports, original
   docstring and theorem signature are byte-for-byte unchanged. The additions are
   a private induction, private proof imports and the theorem proof. Compared the
   existing node by JSON field: only proof, proof_deps and proof_origin differ.
   There are no definition changes, public interface changes or forced adaptations.

2. **Proof and trust: pass with the recorded remaining hole.** Compiled all three
   modules in dependency order with lcompile.py: no errors or warnings. Scratch
   copies with #print axioms show only propext, Classical.choice and Quot.sound
   for complete_of_power_annihilates and closure_eq_top_of_section; all three
   public theorems additionally use sorryAx. The source scan finds exactly one
   sorry, in the named exists_finite_rank_coefficient_correction theorem, and no
   forbidden trust mechanism or holed definition. Witness choices stay inside
   theorem proofs. The generalized completeness helper is valid even at N=0:
   its hypothesis then forces M to be zero. For arbitrary N, congruence at N is
   equality; compatibility proves separation and stabilization. Both calls use
   actual nilpotence proofs to annihilate their regular modules.

3. **Split statements: pass.** Independently read Stacks Tag 07FG at
   https://stacks.math.columbia.edu/tag/07FG. The remaining correction is precisely
   the differential-basis finite-support argument, followed by reevaluation in
   the coefficient closure. It does not assert nilpotent induction or final
   finite-coefficient containment. The action on I factors through K because
   ker(r)I=0, and agrees with the given k-action by hcomm. Thus the discrepancy
   and corrected error use the stated span over k. Rechecked I=0, k=K and empty t;
   each gives the expected zero-error case. The square-zero theorem preserves
   the specified quotient section. Each new theorem has its source, complete
   natural-language proof and matching node. Independent msearch LeanFinder for
   finite-obstruction extension of derivations found only characteristic-zero
   differential-field results and square-zero derivation infrastructure; grep
   for finite derivations and annihilated-module completeness found no match.
   Loogle for IsAdicComplete and Submodule.smul found no match. Local searches
   found private nilpotent-ideal completeness helpers, including the returned
   duplicate, but none with the repaired annihilated-module hypothesis. Closing
   the differential correction requires substantial additional formalization,
   rather than a short application of an existing theorem.

4. **Route and pruning: pass.** Read the fixed-K exponent induction and every
   square-zero helper and call. The repaired helper is strictly more general
   than nilpotent-ideal completeness: an ideal need not be nilpotent to annihilate
   a module by a power. No rewrite of the working proof is needed. The field lift,
   restricted coefficient-subring quotient, complete-source surjectivity, finite
   coefficient extraction and scalar absorption implement proper parts of the
   argument. All added proof imports are private. The report now correctly names
   the two replaced private imports; its full list of retired direct proof_deps
   matches the old node. Only the polynomial-ring node is unused throughout this
   route; no global module pruning is claimed. Read sk-thm-p1.json realized:
   no realized unit statement or step is bypassed.

5. **Nodes: pass.** The original node follows the induction and square-zero call.
   The square-zero node follows the actual code, including the generalized
   completeness helper at step 4 and its two regular-module specializations.
   The correction node records the unresolved derivation argument faithfully.
   proof_deps are the unions of the steps' uses; new nodes contain source,
   searches, creation, blueprint, unit/chapter and Lean records.

Changed in this reading: corrected the report's assertion that no private imports
were removed, and added this independent review. No Lean proof, statement or node
needed a further repair. Accounting remains one original hole closed and one
strictly smaller hole added: decomposition, net zero; no globally pruned module.
