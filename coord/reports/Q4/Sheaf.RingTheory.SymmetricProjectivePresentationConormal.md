## What changed

Replaced the sole sorry in `Algebra.symmetric_projective_presentation_conormal` with
an unchanged-signature Lean proof. It proves surjectivity of q from the generators
of I, gets surjectivity of α from the existing symmetric-algebra theorem, identifies
φ with coefficient reduction followed by α, and proves surjectivity of φ.

Added `Sheaf.RingTheory.ProjectiveSymmetricPresentationConormalEquiv`, whose theorem
`Algebra.projective_symmetric_presentation_conormal_equiv` is proved. The general
conormal map is surjective; its differential, in the polynomial Kähler basis, is
the base change of the split inclusion ker(q) into A^m. This proves injectivity
without the DAG's local regular-sequence conormal-basis argument.

Added `Sheaf.RingTheory.ProjectiveSymmetricConormalReductionExact` to isolate the
remaining coefficient-reduction exact sequence, including left injectivity.
The main proof transports its right map through the proved conormal equivalence,
checks the representative formula, proves projectivity of the tensor kernel,
splits the surjection, and constructs both requested linear equivalences using
Mathlib's split exact sequence and tensor-product basis equivalences.

All new imports of the existing module are proof-only. The open coefficient-reduction
module imports the declarations of its planned proof dependencies, also proof-only. Existing public imports,
its signature, and its docstring remain unchanged. A local heartbeat limit allows
the dependent conormal types and tensor equivalences to elaborate; compilation
remains well within the single-file time limit. Node proofs and dependencies now
follow the delivered argument. No existing interface or definition was changed.

## Proved and sorry left

Closed the original hole in `Algebra.symmetric_projective_presentation_conormal`
(node `lem-weil-pbc-symmetric-projective-presentation-conormal`), by reduction to
one strictly smaller exact-sequence theorem. This is a decomposition, not a
sorry-free proof of the full target closure: one hole closed and one added.

Also proved `Algebra.projective_symmetric_presentation_conormal_equiv`
(node `lem-weil-pbc-projective-symmetric-presentation-conormal-equiv`) without any
new hole. Its existing symmetric-algebra dependency is proved in the repository.

The only sorry left in the delivery is
`Algebra.projective_symmetric_conormal_reduction_exact`
(node `lem-weil-pbc-projective-symmetric-conormal-reduction-exact`). It asserts
only the coefficient-reduction exact sequence, its left injectivity and map
formulas. It assumes the surjectivities already proved by the main module and
does not assert the reduced conormal equivalence, splitting, or either final
free-module equivalence. Its source and complete argument are in its docstring
and node. The zero-ring and empty-generator cases were checked mathematically;
the statement has no nontriviality hypothesis.

## No longer needed

Removed direct proof imports:
- `Sheaf.RingTheory.ConormalIntersectionRegularQuotient`
- `Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`
- `Sheaf.RingTheory.RegularSequenceConormal`
- `Sheaf.RingTheory.SymmetricAlgebraBaseChange`

The intersection, free-cover and symmetric-base-change results remain needed
below the new coefficient-reduction node; their obligations were moved down,
not claimed as globally pruned. The main module now imports the two new modules
and the existing general symmetric-algebra cotangent module.

The delivered route no longer needs
`lem-weil-pbc-regular-sequence-conormal-free` or its module
`Sheaf.RingTheory.RegularSequenceConormal`: differential coordinates replace
that conormal-basis calculation. Regularity itself is still needed for the
intersection argument. The main node's old tensor-right-exact dependency is
also unnecessary: the proof explicitly base-changes a linear equivalence and
uses `TensorProduct.prodRight`, so
`lem-weil-pbc-tensor-right-exact` is removed from its proof dependencies.
For completeness, the old main-node dependencies no longer used directly are:
- `lem-weil-pbc-finite-projective-standard-free-cover`
- `lem-weil-pbc-symmetric-algebra-base-change`
- `lem-weil-pbc-symmetric-algebra-free-module-polynomial`
- `lem-weil-pbc-localization-module-exact`
- `def-weil-pbc-regular-sequence`
- `lem-weil-pbc-conormal-intersection-regular-quotient`
- `lem-weil-pbc-symmetric-algebra-universal-property`
- `lem-weil-pbc-regular-sequence-conormal-free`
- `lem-weil-pbc-tensor-right-exact`

The first six moved into the open coefficient-reduction argument, with their modules
imported there. The universal property remains a statement dependency, provided by
Mathlib. The coefficient-map-kernel node remains a direct dependency because the main
proof uses `MvPolynomial.map_surjective`. Only the conormal-basis and tensor-right-exact
nodes are unnecessary throughout this delivered argument.
No public import was removed. No assertion is made that these nodes are
unreachable from every other target route.

## Where the brief, the DAG or earlier work was wrong

The existing general symmetric-algebra theorem supplies only a surjective
conormal map, correctly avoiding the false unrestricted form of Tag 07EV.
Projectivity makes its differential injective through a split tensor inclusion;
no localization or regular-sequence conormal basis is needed for this step.

The coefficient-reduction argument still needs the separate left-injectivity
calculation. It is isolated with its precise canonical representative formulas,
not replaced by the original theorem under another name.

The referenced TeX literature files are absent in this checkout. Read the
Stacks Project pages for Tags 07CE, 07CX and 07D4 instead; their proofs support
the remaining local regular-quotient intersection calculation. LeanSearch
returned an internal server error; the unavailable search is recorded, and
LeanFinder, Loogle, and local Mathlib searches were used. The unit's statement
and route are retained.

## New nodes

`lem-weil-pbc-projective-symmetric-presentation-conormal-equiv` records the proved
projective case of the reduced symmetric conormal comparison, independently of
the coefficient ring P and its ideal I. Its Lean proof uses the existing general
cotangent theorem, the polynomial Kähler basis, and projective splitting.

`lem-weil-pbc-projective-symmetric-conormal-reduction-exact` records the remaining
coefficient-reduction exact sequence for an arbitrary coefficient ring P. Its
proof follows Tags 07CE, 07CX and 07D4: regular quotient coordinates give
IQ ∩ J² = IQJ, coefficient expansion identifies IQ/IQJ with C tensor I/I²,
and reduction computes the kernel and cokernel. It has one whole-theorem sorry.

No change record is required: no existing public interface changed and there
are no forced adaptations.


## Second reading by Q4

1. PASS. Read the repository/sandbox diff and checked the declaration table: the
   existing theorem signature is byte for byte identical, with the same public
   imports, visibility, and definitions. Only proof imports, a local elaboration
   option, and its proof changed. The other two modules are new. No change record
   or forced adaptation is needed.
2. PASS. Compiled all three files in import order using lcompile.py: 2.1, 4.0,
   and 11.6 seconds, without warnings or errors. Printed axioms in scratch copies:
   the conormal equivalence uses only propext, Classical.choice, Quot.sound; the
   main theorem and coefficient-reduction theorem additionally use sorryAx.
   The sole delivered sorry is the named whole coefficient-reduction theorem.
   No data definition, arbitrary witness definition, forbidden axiom, unsafe,
   opaque, extern, or implementation override was added.
3. PASS. Read both new statements and the complete docstring argument. The open
   result is strictly the coefficient-reduction exact sequence; the proved result
   supplies the independent reduced-conormal identification. Neither restates the
   original conclusion. Checked I=0, I=P, m=0 (surjectivity then forces M=0), and
   zero coefficient rings: the maps reduce to identities or maps of zero modules.
   The general argument applies to arbitrary P: split q gives finite projective
   summands and adapted free coordinates; coordinate variables are regular, and
   Stacks Tag 07CX gives H intersection J² = HJ. The obstruction quotient is a
   C-module, so the A-cover suffices to descend the equality even though its lifts
   need not cover Spec P. Flat polynomial coefficient expansion and right exact
   tensor quotient give H/HJ = C tensor_A I/I² with the stated formulas.
   Independently searched LeanFinder for transitivity/conormal coefficient
   injectivity, Loogle for Algebra.Extension.Cotangent, and local Mathlib/library
   sources for kerCotangentToTensor_injective_iff, Cotangent.exact, inf_sq_eq_mul,
   and symmetric conormal/reduction statements. Inspected the relevant Mathlib
   exactness and smoothness results: they supply components, not this complete
   canonical sequence. No duplicate or quick proof closing the remaining hole
   was found. Sources checked: https://stacks.math.columbia.edu/tag/07CX and
   https://stacks.math.columbia.edu/tag/07CE.
4. PASS after bookkeeping repair. The proved equivalence uses the direct split
   differential argument instead of local conormal bases; the main proof really
   establishes generator surjectivity, map compatibility, transport of exactness,
   projectivity, a section, and both equivalences. Its proof-only imports support
   these steps. Completed the list of old proof dependencies no longer directly
   used and distinguished moved obligations from pruning. Read sk-thm-p1.json's
   realized statement and all steps: this item lies below those realizations;
   the unit route is retained unchanged. This remains a decomposition: one old
   hole closed, one smaller hole added, not net sorry-free progress.
5. PASS after repair. Checked the three node records against the Lean statements,
   proof steps, proof_deps unions, proof_origin, source, creation, blueprint,
   chapter/unit, and searches. Added the coefficient-map-kernel dependency to
   the main node's first step and proof_deps, since map_surjective is used there.
   Added proof-only imports of all planned dependency modules to the open
   coefficient-reduction theorem, so its route is actually available downstream.

Second reading changed the open theorem's proof-dependency imports, one docstring
indentation, the main node's coefficient-map dependency, and this report's complete
pruning/accounting and review evidence. No theorem statement or proof was rewritten.
