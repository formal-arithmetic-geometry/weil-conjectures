## What changed

Replaced the only `sorry` in
`Sheaf.AlgebraicGeometry.SmoothSectionEtaleNeighbourhoods` with a complete Lean reduction.
The existing declaration's signature and public imports are unchanged. Its proof converts affine
smoothness to algebra smoothness, obtains a stabilized differential basis, constructs
`C = D / Ideal.span (Set.range f)` and its quotient section explicitly, checks the factorization
by composition of algebra homomorphisms, proves finite presentation of this quotient, applies
localized cotangent vanishing and the existing principal étale criterion, and composes with the
étale base extension. Both scalar-tower paths to the principal localization are identified in Lean.

Added two statement modules, one theorem each:
`Sheaf.AlgebraicGeometry.SmoothSectionDifferentialBasis` and
`Sheaf.RingTheory.SectionDifferentialBasisQuotient`. They split the first paragraph and the
rank/Nakayama argument of Stacks 07M7 into independent tasks. The first theorem supplies no
étale quotient or local étale conclusion. The second takes a fixed smooth algebra, a fixed
section, and specified differential-basis elements and proves only the localized cotangent
obstructions vanish for their explicit quotient. Neither is a renaming of the original theorem.
No new definition, choice of data in a definition, or axiom was added.

Read [Stacks 07M7](https://stacks.math.columbia.edu/tag/07M7), including the clarification of the
localized conormal target. The local TeX tree is not materialized on this machine; the online
source supplies the same cited proof. Searched the source library, Sheaf, and Mathlib before
splitting; the existing conormal-free-presentation-basis node concerns polynomial presentation
relations, so does not give either new statement. LeanFinder and grep returned ingredients;
LeanSearch returned Internal Server Error, recorded as unavailable in both nodes.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_etale_neighbourhoods_of_smooth_section`
(node `lem-weil-pbc-smooth-section-etale-neighbourhoods`). There is no `sorry` in its proof.

Added two holes, each the entire proof of a named public theorem:

- `AlgebraicGeometry.exists_smooth_section_differential_basis`
  (node `lem-weil-pbc-smooth-section-differential-basis`).
- `Algebra.localized_cotangent_vanishes_of_section_differential_basis`
  (node `lem-weil-pbc-section-differential-basis-quotient`).

This is a decomposition: one hole closed and two added, net minus one. It is not a proof
without `sorry` in its dependency closure. The main theorem also uses the existing
`AlgebraicGeometry.exists_etale_away_of_localized_cotangent_vanishing`; its proof is untouched.

All three delivered modules compile with `lcompile.py --all`. Temporary compiled checks confirm
that an empty differential basis is available for the identity algebra, the section on the
identity algebra to `R/J` is surjective, and a section to a subsingleton ring has no primes
containing its kernel. These scratch examples are excluded from the delivery.
Mathematically, `J = ⊤` can use the zero étale base algebra and yields a vacuous primewise
condition; the zero base ring forces zero algebras as well. In the quotient lemma `n = 0`
means the zero ideal quotient and vanishing residue differentials. When `Q` is zero, the kernel
condition is impossible. For a polynomial algebra with evaluation section, the coordinate
differentials supply the expected basis and the quotient by those coordinates is the base ring.
No nonzero-ring, positive-rank, or nonempty-spectrum assumptions were added.

## No longer needed

Removed these four direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.LiftProjectiveModuleEtale`;
- `Sheaf.RingTheory.JacobiZariskiQuotientSmooth`;
- `Sheaf.RingTheory.SmoothConormalSequenceExact`;
- `Sheaf.RingTheory.SymmetricAlgebraSmooth`.

These are retained as proof-plan imports of the new statement modules. Their nodes remain
needed transitively; none is claimed as pruned from the target closure. The original node's
remaining old proof dependencies are likewise retained through the two new nodes, apart from
notions already in statement dependencies. No module or mathematical ingredient of Stacks
07M7 has been eliminated. The redundant extra `Mathlib.RingTheory.FinitePresentation` import
tried during development was removed after a successful compile without it. The existing
principal cotangent criterion remains a direct proof import.

For completeness, the old node dependencies no longer used directly by the main proof are:

- `def-sbc-smooth-morphisms`;
- `def-weil-pbc-kahler-differentials`;
- `def-weil-pbc-smooth-ring-map`;
- `lem-weil-pbc-finite-module-surjective-endomorphism-bijective`;
- `lem-weil-pbc-finite-projective-rank-locally-constant`;
- `lem-weil-pbc-jacobi-zariski-quotient-smooth`;
- `lem-weil-pbc-kahler-differentials-base-change`;
- `lem-weil-pbc-lift-projective-module-etale`;
- `lem-weil-pbc-nakayama-local-generators`;
- `lem-weil-pbc-smooth-conormal-sequence-exact`;
- `lem-weil-pbc-smooth-ring-map-base-change-composition`;
- `lem-weil-pbc-symmetric-algebra-finite-projective-smooth`;
- `lem-weil-pbc-symmetric-algebra-universal-property`;

These are transferred to the new nodes, except `def-sbc-smooth-morphisms`, which remains
a statement dependency. This is removal of direct dependencies only: **no module is pruned
from the targets’ import closure**.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan labelled construction of the finite basis
quotient elementary, but omitted a Lean interface for stabilization with its differential basis
and for the localized rank/Nakayama calculation. Those are now explicitly stated in two modules,
while the quotient construction and its algebra-map compatibility are implemented in the main
proof. The original module imported constituent ingredients, not statements combining them;
the split records exactly that remaining work.

The `sk-thm-p1` unit's `realized` statement and steps are unchanged. This delivery retains the
07M7 route below that unit and uses the pre-existing conormal, lifting, symmetric-algebra,
Jacobi-Zariski, rank, Nakayama and cotangent-criterion dependencies. No route is bypassed.

## New nodes

`lem-weil-pbc-smooth-section-differential-basis` records stabilization over an étale base algebra,
with a compatible smooth enlarged algebra and a basis of reduced differentials lifted from its
section kernel. It corresponds to the first paragraph of 07M7 and the kernel-lift choice at the
start of the second. Its proof records conormal identification, complement lifting, symmetric
augmentation, and transport of the basis.

`lem-weil-pbc-section-differential-basis-quotient` records localized cotangent vanishing for the
specified quotient by a section differential basis. It corresponds to the Jacobi-Zariski and
rank/Nakayama portion of the second paragraph of 07M7. The surjective base map allows the
residue-field map to factor through the section target. Exactness, rank, surjectivity,
injectivity, and the final localization step are recorded separately.

Both nodes inherit `sec-proper-base-change` and `sk-thm-p1`; the original node's proof,
proof dependencies and proof origin have been updated to match the compiled reduction.
No definition or existing statement was changed, so no change record is needed.

## Second reading by G1

1. **Unchanged public contract — pass.** Compared the sole existing delivered module
   with the repository using `diff -u`. Only four private proof imports are replaced
   by two private proof imports, and the theorem body replaces `by sorry`. The existing
   signature and public imports are byte for byte unchanged. Both other modules and
   their declarations are new; no existing definition or statement changes.
2. **Proof and axioms — pass as a decomposition.** Recompiled all three modules locally
   in import order using `lcompile.py --all`: no errors or warnings. Scratch copies with
   `#print axioms` for each of the three declarations show exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The two new theorems have the only
   delivered sorries, each the entire named theorem proof. No definition, axiom, unsafe
   declaration, opaque declaration, foreign implementation, or hollow witness was added.
   The main proof constructs the ideal, quotient algebra and quotient map explicitly.
   Its existential elimination occurs within a theorem proof, not a data definition.
3. **Split statements — pass.** Independently read Stacks
   [07M7](https://stacks.math.columbia.edu/tag/07M7) and checked both docstring arguments.
   The first lemma supplies stabilization and a differential basis, with no étale
   conclusion for the quotient. The second applies to specified relations and proves
   only localized obstruction vanishing. The two arguments are separate strict parts
   of the original proof, not restatements. In the second, surjectivity of the base map
   implies surjectivity of the section, so the residue map factors through its target;
   finite projectivity gives the asserted rank, and Nakayama plus the finite-module
   surjective-endomorphism lemma proves the conormal isomorphism. Checked identity
   algebras, empty bases, the zero quotient and evaluation on polynomial coordinates;
   recompiled the existing three scratch edge-case examples against the sandbox overlay.
   Repeated LeanFinder searches using complementary-projective-module stabilization and
   conormal-isomorphism wording, and searched both Lean roots and Mathlib with `rg`.
   Results include `Algebra.FormallySmooth.projective_kaehlerDifferential`,
   `Algebra.IsStandardSmooth.free_kaehlerDifferential`, and
   `Algebra.Generators.cotangentRestrict_bijective_of_basis_kaehlerDifferential`.
   These concern differential modules or presentation kernels, not the two section
   statements. No duplicate or short replacement was found. Neither open lemma can
   be closed in a few minutes from these interfaces.
4. **Route and pruning — pass.** Read the main proof from its target down: convert
   smoothness, obtain stabilization, explicitly quotient the kernel relations, establish
   finite presentation, apply localized vanishing and the existing étale criterion,
   then compose étale maps using the scalar towers. Public imports serve the signatures;
   additional imports are private proof or documented remaining-proof-plan dependencies.
   Read `dag/units/sk-thm-p1.json`: its realized statement and steps are unchanged and
   none is replaced by another route. The four removed direct imports remain below the
   new statement modules. The report now names every old dependency removed directly;
   none is claimed as pruned from the target closure.
5. **DAG agreement — pass.** Parsed all three node files, compared each recorded Lean
   statement verbatim to the delivered signature, checked that each `proof_deps` equals
   the union of its proof steps' `uses`, and verified that every dependency has a node.
   The main node follows the actual reduction and both new nodes describe their
   remaining proofs, with source, creation, searches, chapter, unit and Lean records.
   Only the allowed proof fields change on the existing node.

Second reading changed the report only: completed the explicit list of old direct
proof dependencies and recorded this independent review. No Lean or node repair was needed.
One original hole is closed, two holes are added, and no module is pruned; this remains
an honest decomposition with net minus one hole, not a completed proof in the closure.
