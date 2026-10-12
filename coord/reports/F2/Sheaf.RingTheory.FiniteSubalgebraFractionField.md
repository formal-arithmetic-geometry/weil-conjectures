## What changed

Proved `MvPolynomial.exists_finite_subalgebra_fraction_field` completely with its
existing signature byte for byte unchanged. The power-series and polynomial instances
prove the domain conjunct. The proof converts localization at the zero prime to
`IsFractionRing`, obtains a finite integral basis with
`FiniteDimensional.exists_is_basis_integral`, and constructs the subalgebra as
`Algebra.adjoin A (Set.range e)`. Integral generators imply module finiteness. For each
field element, the common denominator of its basis coordinates gives a numerator in
that subalgebra and a nonzero denominator from A.

Added the proof-only plain import `Mathlib.RingTheory.DedekindDomain.IntegralClosure`.
All five original public imports supply notions in the unchanged signature and remain.
Removed the first worker's undelivered core module and node; no new module or node is
needed. Updated the existing node's proof, proof_deps and proof_origin to match Lean.

## Proved and sorry left

Closed: `MvPolynomial.exists_finite_subalgebra_fraction_field` (the sole original hole,
node `lem-weil-pbc-finite-subalgebra-fraction-field`). Added holes: none. Remaining holes:
none. Removed the proposed split-off sorry
`exists_finite_subalgebra_fraction_field_of_domain` before delivery. This is a complete
proof, not a decomposition: one original hole closed, zero lower holes added.

The module compiles without warnings. A scratch copy with `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound` for the theorem.

## No longer needed

Removed from the original node's proof_deps:
- `def-weil-polynomial-ring`: no explicit polynomial-equation construction remains;
  the unchanged statement dependencies still record the polynomial-ring notion.
- `lem-weil-pbc-finite-algebra-is-integral`: the direct finite-algebra integrality step
  is subsumed by Mathlib's proved integral-basis theorem.

No original module import was removed, and no original library module is claimed as
pruned. The proposed core module and node were never in the repository and are omitted
from the delivery.

## Where the brief, the DAG or earlier work was wrong

The first worker's domain-general core restated essentially all of the construction
and left it unproved; it lacked the required complete docstring proof and node searches.
It was not an adequate delivered reduction. Mathlib has a finite integral-basis theorem
whose hypotheses require only a domain, its fraction field, and a finite extension;
its location in a Dedekind-domain file does not impose Dedekind or separability
hypotheses. Together with common denominator clearing for coordinates this closes the
whole construction. The only original compiler warnings were unnecessary `letI` and
unused `hp`; the final proof uses `let` and references `hp` without altering its binder.

The source was checked at https://stacks.math.columbia.edu/tag/07PR: the finite algebra
model is asserted in the proof. The proof here supplies that construction.

## Second reading by F2

1. Compared the delivered module with the repository using diff and a byte comparison
   of the entire theorem signature. Verdict: the existing statement, universes,
   visibility, hypotheses and conclusions are unchanged; no definitions changed, no
   change record needed. The only added import is plain and used only in the proof.
2. Compiled the original proposed set, repaired its warnings, then compiled the final
   module cleanly through lcompile.py. A scratch copy prints exactly the three allowed
   axioms. No sorry, axiom, unsafe, opaque, implemented_by or extern remains. Verdict:
   complete kernel-checked proof with no postponed construction or arbitrary choice
   from an unproved existence theorem.
3. Reviewed the proposed core and rejected it as an unproved restatement of the main
   construction. Independent leanfinder, loogle and grep searches through msearch.py
   found the proved integral-basis and coordinate-denominator ingredients. Searched
   lean/Sheaf and lean/WeilConjectures for existing uses. No split-off statements remain.
   Edge cases: n=m=0 still yield a domain, z=0 has the same nonzero denominator and zero
   numerator, and degree-one field extensions satisfy all basis arguments. Finite
   coordinate denominator clearing also handles an empty index type; a basis of a
   field cannot actually have empty index. No separability or Noetherian assumption.
   Verdict: nothing new is asserted with sorry, and the construction has no omitted case.
4. Followed the shortest route from the target through proved Mathlib ingredients;
   every added import is needed. Removed the two obsolete proof dependency edges listed
   above. Read dag/units/sk-thm-p1.json and its realized fields: this helper realizes no
   unit statement or step; the replacement stays below the unit route. Verdict: route
   kept, no original module pruned, no new intermediate statements.
5. Read the original and sandbox node records against the final Lean. Replaced the
   stale five-step handwritten plan with the integral-basis, finite-adjoin and
   coordinate-denominator proof; proof_deps is exactly the union of step uses, and
   proof_origin records the implemented route. No new nodes remain. Verdict: records
   agree with the proof.

Second reading changed the proof to close the whole theorem, removed the proposed
core module/node and sorry, repaired warnings, updated the theorem's proof docstring,
rewrote the node's proof route and obsolete edges, and corrected this report.
