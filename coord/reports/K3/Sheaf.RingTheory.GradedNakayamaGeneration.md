## What changed

Closed both holes in `Sheaf.RingTheory.GradedNakayamaGeneration` with unchanged signatures.
Added two fully proved helper modules, `Sheaf.RingTheory.FiniteGradedModuleLowerBound` and
`Sheaf.RingTheory.GradedQuotientSpanDescent`, and matching nodes. Their imports are private
proof imports. The lower-bound helper uses the existing finite homogeneous generators theorem;
the descent helper uses only Mathlib. Updated the original node's proof route and dependencies.

The proof works in N itself. Below a common generator degree every homogeneous element is zero.
Projecting a lift of the quotient expression gives x=q+x₀a+x₁b with a,b of degree one less.
Induction on the distance from the lower bound proves membership in the span. Finite additive
homogeneous decomposition finishes generation. The vanishing corollary applies generation to
Fin 0 after restricting scalars along k→k[x₀,x₁].

All three modules compile together without warnings through lcompile.py. Small cases checked
in the argument: the empty family, the zero module, negative generator degrees, and degrees
below the lower bound. The finite set of generator degrees may be empty; bddBelow still gives
a bound. The degree descent does not assume finite generation.

## Proved and sorry left

Holes closed (2):
- `MvPolynomial.graded_nakayama_generation`
- `MvPolynomial.subsingleton_of_graded_quotient_subsingleton`

Additional proved declarations:
- `MvPolynomial.exists_graded_module_lower_bound`
  (`lem-sc-p1-finite-graded-module-lower-bound`)
- `MvPolynomial.homogeneous_decomposition_of_quotient_span`
  (`lem-sc-p1-graded-quotient-span-descent`)

No sorry remains in any delivered module. Holes added: 0. This is a proof from the existing
stated dependency, not a decomposition into new holes. At second reading, the repository source now proves the transitive dependency
`MvPolynomial.exists_finite_homogeneous_generators`, but the local compiled baseline still
gives `sorryAx` for the lower-bound helper and the two original results. This delivery neither
changes nor duplicates that dependency. No sorry-free transitive axiom closure is claimed
against that compiled baseline; the descent helper already has only the three standard axioms.

## No longer needed

The direct proof import `Sheaf.RingTheory.FiniteHomogeneousGenerators` is replaced by the two
helper imports. Its module and node `lem-sc-p1-finite-homogeneous-generators` remain needed
transitively through the lower-bound helper; they are not pruned. No existing DAG node or
module is made unnecessary. The construction of a quotient grading on N/Q and a minimal
nonzero degree in that quotient are unnecessary; induction in N gives the same argument.
All original public imports remain necessary for the unchanged signatures.

## Where the brief, the DAG or earlier work was wrong

The original DAG treated component descent and the lower-bound calculation as elementary;
they require substantial Lean glue. They are now explicit, proved helper nodes. The unit
route is preserved (both helpers have the same unit; its realized statement/steps are empty).
The source blueprint file is absent from this checkout. As the existing node already records,
the standard graded Nakayama argument is an agent expansion of the graded-resolution proof,
not an explicit sentence or proof in that blueprint. No statement or definition was changed.
LeanSearch returned Internal Server Error and is recorded as unavailable; actual LeanFinder,
Loogle and source searches supplied the other searches.

## New nodes

`lem-sc-p1-finite-graded-module-lower-bound` records the proved lower bound supplied by finite
homogeneous generators. Its module is `Sheaf.RingTheory.FiniteGradedModuleLowerBound`.

`lem-sc-p1-graded-quotient-span-descent` records the proved component decomposition one degree
lower modulo the homogeneous span. Its module is `Sheaf.RingTheory.GradedQuotientSpanDescent`.
Both nodes are strictly parts of the degree argument, and neither introduces a hole.


## Second reading by K3

1. Compared the item module with the repository by `diff -u`. Both existing theorem
   signatures, universes, instance arguments and docstrings are byte-for-byte unchanged.
   Only the two proof bodies and private proof imports changed. No definitions were added
   or modified, and no change record is needed. Verdict: pass.
2. Compiled all three delivered modules in import order with `lcompile.py --all`: no errors
   or warnings. Searched the Lean files for forbidden constructs and holes: none. Compiled
   scratch copies with `#print axioms` for all four declarations. The descent helper uses
   only `propext`, `Classical.choice`, `Quot.sound`; the lower-bound helper and both original
   results also use the existing compiled dependency's `sorryAx`. The source of finite
   homogeneous generation has since been proved, so the report's earlier assertion that
   its repository source is still sorry was stale and is corrected above. Verdict: pass
   relative to the permitted existing open dependency, with the axiom limitation recorded.
3. No statements were split off with sorry. Read both new proved helpers in full: the lower
   bound is a strictly smaller part of generation, and component descent does not assume
   finite generation. Checked the empty family and zero module, negative shifts, degrees
   below the bound, and arbitrary homogeneous degrees (including zero generators, for
   which any chosen degree suffices). The lower-bound proof needs no minimum of a nonempty
   family. Projection of the lifted quotient expression and scalar-tower compatibility
   give exactly the descent conclusion. Repeated searches with different queries through
   LeanFinder, Loogle, and Mathlib grep, and searched Sheaf and upstream RingTheory sources.
   Found component and homogeneous ideal facts but no graded-module replacement for these
   helpers or the generation criterion. Verdict: pass.
4. Read generation from the top: lower bound, descent induction, then finite direct-sum
   induction; the vanishing corollary uses the empty family. No shorter applicable library
   route was found. All public imports supply types or instances used in signatures; the
   three Sheaf dependency edges are private proof imports. The sole old proof dependency,
   finite homogeneous generation, is retained transitively; no old node or module is
   pruned. Read `dag/units/sk-thm-picard-duality.json`: its realized statement and sole
   realized step are empty; no realized unit step is bypassed or changed. Verdict: pass.
5. Compared all three node proofs and dependency unions with their Lean proofs. The item
   uses the two helpers; lower bound uses finite homogeneous generators; descent uses
   Mathlib only. New nodes include self-contained statements, source qualifications,
   elementary proof steps, recorded searches, provenance, chapter/unit and matching Lean
   declarations/signatures. Existing node changes are confined to proof-route fields.
   Verdict: pass.

Second reading changed only this report: corrected the stale dependency-source status and
recorded the independent checks and their actual axiom results. The Lean proofs and DAG
records required no repair. Closed 2 existing holes; added 0 holes; split off 0 open statements.
