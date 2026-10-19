## What changed

Proved `RingHom.isUniversallyCatenary_and_locallyNagata_of_weaklyEtale` in
`Sheaf.RingTheory.LocallyNagataCatenaryOfWeaklyEtale`, preserving its signature,
universes, visibility and all public imports. No definitions or other modules changed.

The proof follows the nine-step DAG argument. Private proved helpers handle localization
of the base in mixed universes, local Nagata ascent, contraction of finite and saturated
prime chains, catenarity under surjections and localization, essentially finite type
permanence, Nagata permanence, fibre incomparability, and contraction of adjacent primes.
For the latter, it constructs the local quotient map C to D and its minimal prime J,
applies the existing local component dimension theorem, and transports the dimension
bound through the double-quotient equivalence. A polynomial base change and polynomial
presentation of every finite type B-algebra finish universal catenarity.

The mixed-universe localization helper is needed because the existing source
`Algebra.WeaklyEtale.localization_base` takes all three rings in one universe. The helper
proves the generalization directly using the compatible tensor equivalence and flatness.
Likewise, the finite type catenarity helper uses `Shrink.algEquiv` so the same-universe
quantifier in `IsUniversallyCatenary` can be applied to finite type algebras in other
universes. These are private theorems with complete proofs, not new postponed items.

Added proof imports for the etale ring-map API, residue-field fibre correspondence,
source absolute-flatness results, shrinking algebras, essentially finite type algebras,
and polynomial tensor products. Updated the existing node's proof, proof dependencies
and proof origin to follow the Lean, including the pruning below. No new nodes.

Validation: the retained proof previously compiled in 6.1 seconds, and its reduced
import set compiled in 6.2 seconds through `lcompile.py`, without warnings. Preflight
identified a top-level tensor-product scope opening as an interface change; its sole
tensor type was written explicitly and the opening removed.

On resumption (2026-10-19), read the entire retained proof and checked it against the
current module, definitions, dependency signatures and DAG. Static checks confirm that
the main signature and all public imports are unchanged, there are zero `sorry` tokens
and no lines over 100 columns, the node changes only permitted proof fields and removal
of obsolete tool approvals, and `proof_deps` is the union of the proof steps' uses.
The unit's `realized` statement and steps remain empty.

The first required dry run received no answer from the compile service within 184
seconds. The retry succeeded: `deliver3.py --no-push` reported commit `c18d10eeba`
compiles and passes preflight, review class CODEX because the existing node is updated.
No Lean changes were needed on this resumption; the retained complete proof is delivered.

## Proved and sorry left

Closed one original hole:
`RingHom.isUniversallyCatenary_and_locallyNagata_of_weaklyEtale`
(node `lem-exc-weakly-etale-locally-nagata-catenary`).

Item holes: 1 before, 0 after. Added holes: 0. Split off: 0.
Every private helper is proved. The existing imported Nagata ascent and local component
dimension declarations are used as stated; their existing holes are not new holes of
this delivery. This proves the item from its declared dependencies, rather than claiming
that all transitive dependencies are already axiom-free.

## No longer needed

Pruned direct dependency modules:

- `Sheaf.RingTheory.WeaklyEtaleField` / `lem-weil-pbc-weak-etale-field`: fibre
  incomparability follows directly from the already proved
  `Ring.AbsolutelyFlat.of_flat_lmul'` and `Ring.AbsolutelyFlat.tfae` in
  `WeilConjectures.RingTheory.ProEtale.WeakDimension`. No finite-subalgebra,
  algebraicity or separability assertion is used.
- `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` /
  `lem-weil-pbc-localization-prime-residue-field-iso`: the proof uses Mathlib's
  localization ideal order embedding and prime order isomorphism directly, and needs
  none of this bundled theorem's local-ring or residue-field isomorphisms.
- `lem-weil-pbc-localization-at-prime-of-quotient`: no quotient-localization
  identification is needed. C is defined as R_q / pR_q; its local/domain, finite
  normalization and essential finite type properties are available directly.

Removed the two corresponding `tool_uses` approvals from the existing node, preserving
all remaining approvals and their order. No claim is made that these modules are unused
elsewhere: in particular they may still occur in the transitive dependencies of the
Nagata or local component dimension theorems.

Also removed the redundant direct imports `Sheaf.RingTheory.JapaneseDomain`,
`Mathlib.RingTheory.Etale.Weakly`, `Mathlib.RingTheory.FiniteType`,
`Mathlib.RingTheory.KrullDimension.Basic`, `Mathlib.Algebra.Polynomial.Basic`,
`Mathlib.RingTheory.Localization.Ideal`, `Mathlib.RingTheory.Ideal.Maps` and
`Mathlib.RingTheory.Localization.Basic`; their used declarations remain available from
the retained public and proof imports. The retained draft's
`WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale`,
`Mathlib.RingTheory.MvPolynomial.Localization`, and
`Mathlib.RingTheory.TensorProduct.Quotient` imports were removed too. Polynomial
base change uses `Mathlib.RingTheory.TensorProduct.MvPolynomial` instead.

The unit's `realized` statement and step lists contain no nodes, and its route is
unchanged. The local component dimension lemma and the polynomial/chain argument stay.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The previous report described an older
unfinished draft; the retained Lean file actually contained a complete proof draft.
That draft has now been compiled successfully and its unused imports pruned.

The DAG's exact-dimension-one argument can be shortened to an upper bound of one;
this suffices to rule out an intermediate prime. Its explicit saturated-refinement
argument is unnecessary for the existing definition of catenarity: contraction
transports its two quantified clauses directly. Its bundled localization/residue-field
and weakly-etale-field dependencies are stronger than the proof needs.

The resumed preflight caught the retained draft's top-level `open scoped TensorProduct`;
explicit tensor-product types remove that interface change without any definition or
statement repair.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
