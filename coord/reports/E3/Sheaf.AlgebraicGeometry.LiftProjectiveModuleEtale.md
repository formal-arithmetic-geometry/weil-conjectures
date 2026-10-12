## What changed

Proved `AlgebraicGeometry.lift_finite_projective_module_etale` with its signature unchanged.
The private `finite_projective_projector` uses Mathlib's finite free splitting to build the
projector and its range equivalence. The private `quotient_tensor_equiv` upgrades the standard
quotient/tensor equivalence to linearity over the quotient ring. The conclusion composes this
with the two existing `LinearMap.idempotent_image_baseChange` equivalences.

Added two proved modules: `Sheaf.AlgebraicGeometry.IntegralModelFiniteFreeProjector` and
`Sheaf.AlgebraicGeometry.EtaleLiftFiniteFreeProjector`. The first constructs the integral
commutative algebra using Cayley–Hamilton, a determinant divisibility identity, and Mathlib's
polynomial idempotent repair. The second applies the existing integral-idempotent lifting theorem
and proves the tensor/matrix quotient compatibility. All new imports in the original module are
proof imports; its public imports, statement, universes, and docstring remain unchanged.

All three modules compile locally without warnings. Import directions checked for the existing
image/base-change and integral-idempotent lifting modules. New statements include n=0, the zero
ring, I=0, and I=top: the actual proofs use positive exponent n+1 and no nontriviality assumption.
The Stacks proof was checked at https://stacks.math.columbia.edu/tag/07M5. Searches used
LeanFinder, Loogle, and source rg; LeanSearch was attempted but returned an internal-server error.
No full-library build or push was run.

## Proved and sorry left

Holes closed: `AlgebraicGeometry.lift_finite_projective_module_etale`.
Holes added: none. Net direct holes removed by this delivery: one.

Original module: proved `AlgebraicGeometry.lift_finite_projective_module_etale` (node
`lem-weil-pbc-lift-projective-module-etale`), removing its sole direct sorry.

Also proved `AlgebraicGeometry.exists_integral_model_finite_free_projector` and
`AlgebraicGeometry.exists_etale_lift_finite_free_projector`, with their two nodes listed below.
All three private helpers are proved. No sorry is left in any delivered module; none was split off.
The proof still depends on the existing unfinished `LinearMap.idempotent_image_baseChange`
(node `lem-weil-pbc-idempotent-endomorphism-image-base-change`), and on whatever unfinished
statements the existing `AlgebraicGeometry.exists_etale_lift_isIdempotentElem` proof uses.
This is a proof from the library's named dependencies, not a claim of independent axiom closure.

## No longer needed

Removed the original proof import `Sheaf.LinearAlgebra.IdempotentEndomorphismCharpolyField`.
The theorem/node `lem-weil-pbc-idempotent-endomorphism-charpoly-field` is not used anywhere
in the new route. The determinant identity proves the needed divisibility directly over A/I,
so its residue-field, rank-nullity, and characteristic-polynomial factorization route is
unnecessary for this item.

The node `lem-weil-pbc-zero-locus-eq-iff-radical-eq` is also unnecessary: there is no passage
through primes or radicals, and no import of its planned spectrum module is added.
The Bezout/unit construction of the old plan's step 4 is replaced by Mathlib's explicit
`isIdempotentElem_one_sub_one_sub_pow_pow` formula; it needed no separately named old node.

Removed `Sheaf.RingTheory.LiftIdempotentUpstairs` as a direct import of the original module;
it remains genuinely needed by the new étale-projector module and is not globally pruned.
The characteristic-polynomial definition/properties, monic quotient freeness, finite-algebra
integrality, and Cayley–Hamilton remain used by the new integral-model module, now below that
node. The image/base-change module remains needed.

For completeness, the old direct `proof_deps` no longer listed on the item's node are:
`def-weil-pbc-charpoly-free-module`, `lem-weil-pbc-charpoly-free-module-properties`,
`lem-weil-pbc-monic-quotient-free`, `lem-weil-pbc-finite-algebra-is-integral`,
`lem-weil-cayley-hamilton-free-module` (now used by the integral-model node),
`lem-weil-pbc-lift-idempotent-upstairs` (now used by the étale-projector node),
`def-weil-etale-morphism` (still a statement dependency, not an invoked proof lemma),
and the two genuinely unused nodes `lem-weil-pbc-idempotent-endomorphism-charpoly-field`
and `lem-weil-pbc-zero-locus-eq-iff-radical-eq`.
Only the characteristic-polynomial field module is removed from this item's import route;
no claim is made that other targets cease to import it.

No unit statement or unit proof step is bypassed:
the item is below the unit's realized nodes and retains the projector/lift/image construction.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The planned residue-field/radical argument
was longer than necessary. For an idempotent M, with S=t*1 and N=C(M), the identity
(S-N)(1-S-N)=(t-t²)*1 gives charpoly(M) | (t-t²)^n by determinant multiplicativity.
This works over every commutative ring and avoids the field-specific characteristic-polynomial
sorry. Mathlib's `quotTensorEquivQuotSMul` is stated as an equivalence over the original ring;
the conclusion requires quotient-ring linearity, which is proved explicitly in the private helper.

## New nodes

`lem-weil-pbc-integral-model-finite-free-projector`: the proved integral commutative model,
module `Sheaf.AlgebraicGeometry.IntegralModelFiniteFreeProjector`. It contains the matrix lift,
Cayley–Hamilton algebra, direct determinant argument, and polynomial idempotent repair; its
statement contains no étale or module-lifting conclusion. Source: matrix construction in 07M5,
with the determinant replacement written and proved here.

`lem-weil-pbc-etale-lift-finite-free-projector`: the proved matrix/projector lifting step,
module `Sheaf.AlgebraicGeometry.EtaleLiftFiniteFreeProjector`. It combines the integral model
with 07M4 and proves reduction compatibility through the quotient of the tensor product.
The original module performs the finite/projective range and tensor-quotient argument itself.
No change records are needed: no existing definition, statement, or public import changed.


## Second reading by E3

1. Compared the existing module against the repository with `diff -u`. Its public theorem
   signature is byte-for-byte unchanged; its existing docstrings, universes, definitions and
   public imports are unchanged. The two additional modules are new. The existing node differs
   only in `proof`, `proof_deps` and `proof_origin`. Verdict: pass; no change record is needed.
2. Compiled all three modules locally in import order with `lcompile.py --all`, without errors
   or warnings. Read every proof and scanned for forbidden declarations and holes: none occurs
   in delivered code. Scratch-copy `#print axioms` reports only `propext`, `Classical.choice`
   and `Quot.sound` for `exists_integral_model_finite_free_projector`; the étale-projector and
   original theorem additionally use `sorryAx` from existing dependencies. No delivered
   definition or theorem introduces a hole. Verdict: pass as a proof from named dependencies,
   not an independently axiom-closed target.
3. No unfinished statement is split off. The two new proved results are strictly separate
   parts of the construction, not restatements of the module-lifting theorem. Rechecked the
   determinant identity, Cayley–Hamilton quotient, polynomial idempotent repair, tensor map,
   ideal containment and quotient-ring linearity against their Mathlib sources. For `n=0`,
   the characteristic polynomial is 1 and the auxiliary algebra is the zero ring, while the
   repair exponent is 1. For the zero ring or `I=top`, the quotient and its modules are zero;
   no nontriviality is assumed. For `I=0`, the same construction remains valid. Fresh LeanFinder
   search for “lifting a direct summand of a free module through a quotient using an etale
   algebra”, Loogle search `IsIdempotentElem, Matrix.charpoly` (no hits), and source `rg` for
   projector/projective/étale combinations found no duplicate complete theorem or shorter
   existing route. Source checked at https://stacks.math.columbia.edu/tag/07M5. Verdict: pass.
4. The proof starts from finite projective splitting and uses the existing image/base-change
   and integral-idempotent lifting statements, replacing only the lower residue-field/radical
   detour with the determinant identity. Imports needed only by proofs are plain imports;
   statement imports are public. Checked `dag/units/sk-thm-p1.json`: neither the item nor either
   pruned node realizes a unit step, and no realized step or unit route is bypassed. Expanded
   the pruning report to enumerate every old direct dependency, distinguishing relocation and
   statement use from genuine pruning. Verdict: pass.
5. Read all three delivered nodes and their referenced existing declarations. Their proof
   steps and dependency unions match the Lean argument; new nodes have sources, searches,
   provenance, blueprint ancestry and verbatim Lean signatures required by the stage brief.
   Verdict: pass.

Changes by the second reader: report only; explicit holes-closed/holes-added accounting,
complete direct-dependency pruning accounting, and this independent review. No proof repair
was required.
