## What changed

Replaced the sorry in `AlgebraicGeometry.separated_lqf_base_change` with a complete
Lean proof following all five steps of the existing DAG plan. The separatedness
implication uses Mathlib's pullback instance. For local quasi-finiteness, install
the local finite type instance, obtain isolated fibre points before and after
base change, choose affine neighbourhoods in the target and its preimage, and
apply the existing affine-pair criterion. All statements and definitions are unchanged.

## Proved and sorry left

Closed the one hole in `AlgebraicGeometry.separated_lqf_base_change`
(node `lem-weil-pbc-separated-lqf-base-change`). No sorry remains in this module;
no new holes were added or split off. This is a proof from existing stated
lemmas, whose proofs remain the next tasks, rather than an axiom-free closure
of the dependency tree. The existing dependencies used are:

- `AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_of_isLocallyQuasiFinite`.
- `AlgebraicGeometry.Scheme.Hom.quasiFiniteAtPoint_isolated_in_fiber`.
- `AlgebraicGeometry.isolated_fiber_point_base_change`.
- `AlgebraicGeometry.Scheme.Hom.isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber`.

## No longer needed

Removed the redundant proof import `Sheaf.RingTheory.QuasiFiniteAtPrime`;
the public statement import `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`
already makes its definition available. That definition and its node remain
needed through the affine-pair criterion. No DAG nodes or modules are pruned
from the actual proof route; all five existing steps remain used. No unit
statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

None. Mathlib's base-change theorem for `LocallyQuasiFinite` uses a different
notion, so the existing fibre-isolation route was used. The neighbourhood
form of the affine-open basis is Mathlib's
`AlgebraicGeometry.exists_isAffineOpen_mem_and_subset`. The unchanged DAG
already records this argument and its exact dependencies. Local compilation
passed without warnings.

## Second reading by K3

1. Compared the sole delivered Lean module against the repository with `diff -u`.
   The existing declaration signature, definitions, docstrings, and public imports
   are byte for byte unchanged. The only code changes are the proof and removal
   of one redundant private import. No change record is needed. Verdict: pass.
2. Independently compiled the delivered file with `lcompile.py`: exit 0, no
   warnings. Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.separated_lqf_base_change`: precisely `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The last comes from existing
   imported open theorems, explicitly acknowledged above. There are no local
   sorries, new definitions, or forbidden declarations. Verdict: pass.
3. No statements were split off or added. Read the four existing theorem
   dependencies and checked their instantiation: the finite-type hypothesis is
   supplied before isolation and base change; the final affine-pair theorem is
   applied to the newly chosen neighbourhoods. Empty source schemes are handled
   by the pointwise universal quantifier. Verdict: pass.
4. Read the full proof top down, the node's five steps, and
   `dag/units/sk-thm-p1.json`, including its `realized` fields. The proof uses all
   five planned steps without bypassing any unit. Searched the library and
   upstream sources for alternative base-change results for the project's
   `IsLocallyQuasiFinite`; none was found. Mathlib's differently defined
   `LocallyQuasiFinite` is not directly applicable. All remaining private
   imports supply the explicit lemmas used. The removed ring-theory import is
   already public through `QuasiFiniteMorphism`; its definition and node remain
   used. No old proof dependency becomes unnecessary. Verdict: pass.
5. Checked the node's `proof`, `proof_deps`, and `proof_origin` against the actual
   Lean proof: separatedness and finite-type base change use Mathlib instances,
   affine neighbourhoods use the affine-open basis, and the four imported
   theorems carry the remaining steps exactly as recorded. No new nodes or
   metadata changes are required. Verdict: pass.

Second reading changed only this report by adding the independent review.
No Lean repair was necessary. Holes closed: one; holes added: zero.
