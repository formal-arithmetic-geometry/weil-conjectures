## What changed

Replaced the sorry in `AlgebraicGeometry.exists_etale_split_residue_points` by a
complete Lean proof, preserving its signature and existing docstring. Added four
proved private helpers in the same module: `split_tensor_equiv_triplet`,
`tensorCongr_inr`, `fixed_pair_finite`, and
`finite_purelyInseparable_pullback_of_split_tensor`.

The proof follows the existing four-step DAG route. It transports each extension
along `hx`, applies the existing simultaneous separable splitting theorem, and
realizes its field by the existing prescribed-residue-field etale neighborhood
theorem. The private helpers explicitly construct the tensor/pushout isomorphism,
prove finiteness of the fixed-pair fibre using `carrierEquiv`, transport prime
quotients to the point residue fields, and transport finite generation and pure
inseparability along compatible field isomorphisms. `Finite.equivFin` then gives
the lists, their injectivity, projection equations, and exhaustion.

Added the proof-only import
`WeilConjectures.Mathlib.RingTheory.RingHom.PurelyInseparable` for its proved
compatible-isomorphism transport lemma. The second reader removed six redundant
Mathlib imports introduced by the first worker.

Validation: the prescribed local wrapper compiles the entire module without
errors or warnings. The statement permits `n = 0` and repeated input points:
the common splitting theorem handles the empty family, and the enumeration is
chosen separately for each indexed point. No distinctness, isolation, or finite
type assumptions were introduced. The private transport argument works for an
arbitrary second morphism, using etaleness only to select the neighborhood.

Searches: LeanFinder returned tensor and residue-field API, not a direct theorem;
Loogle returned `Triplet.tensor`, `carrierEquiv` and its projection lemmas; the
logged grep found the carrier equivalence. Local searches of both library roots
found no direct version. Read Stacks 02LM's proof (the common Galois field,
prescribed neighborhood, and fibre-product point paragraphs) and 01JT's
point/residue-field correspondence, as well as the cited Mathlib signatures.
The original unit route is preserved, with no new nodes or statement changes.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.exists_etale_split_residue_points`
(node `lem-weil-pbc-etale-split-residue-points`).

No sorry remains in the delivered module; no holes are added or split off.
The proof uses the existing named dependencies
`Algebra.exists_separable_split_purelyInseparable_prime_quotients`,
`AlgebraicGeometry.Scheme.exists_etale_neighbourhood_prescribed_residueField`,
and `AlgebraicGeometry.Scheme.Pullback.exists_residueField_equiv_ofPointTensor`.
Their existing holes are not changed by this delivery.

## No longer needed

All three existing proof-dependency imports and all original DAG proof nodes
are used. No original module or node is pruned. The second reader removed these
redundant added imports, whose API is already available through the retained imports:

- `Mathlib.Algebra.Category.Ring.Constructions`
- `Mathlib.RingTheory.TensorProduct.Maps`
- `Mathlib.RingTheory.Ideal.Quotient.Operations`
- `Mathlib.RingTheory.Spectrum.Prime.RingHom`
- `Mathlib.RingTheory.Finiteness.Basic`
- `Mathlib.Algebra.Field.Equiv`

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The anticipated transport and enumeration steps
could all be proved from the existing interfaces. The repository does not contain
the cited literature files on this machine; the relevant Stacks source was read
from the available local copy and the official Stacks pages.


## Second reading by R3

1. Compared the entire delivered module with the repository using `diff -u`.
   The existing theorem signature and docstring are byte-for-byte unchanged.
   The only additions are four private proved helpers, the proof body, and a
   proof-only upstream import. There are no definitions, public statement changes,
   new modules, change records, or new nodes. Verdict: pass.
2. Compiled the delivered file with `lcompile.py`, without errors or warnings.
   In a scratch copy, printed axioms for the target and all four private helpers.
   The tensor equivalence, tensor congruence, and fixed-pair finiteness helpers
   use only `propext`, `Classical.choice`, and `Quot.sound`. The target and the
   residue transport helper additionally use `sorryAx`, from the existing named
   imported dependencies. The delivered file contains no sorry or forbidden
   declaration and no data definition selecting an arbitrary unproved witness.
   Verdict: pass, conditional on the existing dependencies as the report states.
3. No statement is split off and no hole is added. Reviewed the new proved
   private helper statements: the tensor equivalence respects the right factor;
   triplet equality transports that inclusion by equality elimination; finiteness
   follows by a surjection from the prime spectrum; and the residue-field helper
   uses the quotient by the actual tensor-map kernel. In the latter, `hc` proves
   compatibility with exactly the transported second-projection scalar map before
   invoking the finite-module and purely-inseparable transport lemmas. This does
   not assume the arbitrary morphism is finite type or the point isolated.
   The empty family is accepted by the simultaneous splitting dependency;
   repeated input points receive separate enumerations, and no positive cardinality
   assumption is imposed. Verdict: pass; no new unproved statements to search for.
4. Read the three imported dependency statements and Mathlib's `carrierEquiv`
   and projection lemmas. Repeated a LeanFinder search for fixed-projection
   finiteness, and searched both local library roots for equivalent splitting
   and transport statements. The search returned the existing pullback API or
   finite-morphism results requiring hypotheses absent here, not a shorter direct
   theorem. The proof keeps the four planned steps: common separable splitting,
   prescribed etale neighborhood, fixed-pair point enumeration, and compatible
   prime-quotient residue-field identification. Checked `sk-thm-p1.json`'s
   `realized` entries; no unit realization or route is bypassed. Individually
   tested removal of each added import, then compiled after removing all six
   redundant Mathlib imports together. The sole retained added import is needed
   for `RingHom.IsPurelyInseparable.of_comp_eq_comp'`. No old proof dependency is
   unused. Verdict: pass after import pruning.
5. Read `lem-weil-pbc-etale-split-residue-points.json` and the fibre-product-points
   Mathlib leaf. The node's assumptions match `f`, `s`, `n`, `x`, `hx`, and
   `hfinite`; its conclusions match etaleness, the point over `s`, the indexed
   injective lists, both projections, finite purely inseparable extensions, and
   exhaustion. Each existing `proof` step and `proof_deps` entry is used, including
   the Mathlib carrier correspondence and the named quotient residue-field theorem.
   Its source-based `proof_origin` still describes this route. No DAG edit is
   needed. Verdict: pass.

Changed only redundant imports and one extra blank line in Lean; corrected the
report's import account and recorded this independent reading. No mathematical
repair, new hole, signature change, or dependency pruning was required.
