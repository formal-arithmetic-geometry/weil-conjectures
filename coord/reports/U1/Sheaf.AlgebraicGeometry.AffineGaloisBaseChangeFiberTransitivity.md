## What changed

Proved `AlgebraicGeometry.exists_galois_map_eq_of_affine_projection_eq` without changing
its signature or existing public imports. Constructed the affine comparison from `X.isoSpec`,
`Spec.fullyFaithful.preimage`, `pullback.map`, and `pullbackSpecIso`; proved its projection
identities and its compatibility with `baseChangeMap f (specAlgEquivOver σ)`.

Added the proved ring lemma `Algebra.TensorProduct.exists_comap_eq_of_galois` in
`Sheaf.AlgebraicGeometry.TensorGaloisPrimeTransitivity`. Its proof constructs the right-factor
Galois action, proves open stabilizers by tensor induction, establishes invariance using the
existing proved tensor-invariants theorem and the infinite Galois fixed-field theorem, and
applies Mathlib's profinite prime-transitivity theorem. This is a separate reusable ring lemma,
not an unproved reformulation of the scheme theorem. Updated the existing node's proof route
and added the ring lemma's node. No changes to definitions, existing signatures, or other modules.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_galois_map_eq_of_affine_projection_eq`
(node `lem-weil-pbc-affine-galois-base-change-fiber-transitivity`).

Also proved the new declaration `Algebra.TensorProduct.exists_comap_eq_of_galois`
(node `lem-weil-pbc-tensor-galois-prime-transitivity`). No holes split off or added.
No `sorry` remains in either delivered module. Both modules compile through `lcompile.py`
without warnings. `#print axioms` for both declarations reports exactly `propext`,
`Classical.choice`, and `Quot.sound`; neither depends on `sorryAx`.

Edge cases: the ring lemma assumes neither nontriviality of A nor finite dimension or finite
type. If A is the zero ring its prime spectrum is empty; no points can satisfy the binders.
The trivial extension is covered by the same proof. Infinite algebraic Galois extensions use
Krull topology and compactness, never an assumption that the Galois group is finite.
The tensor action is constructed explicitly; no data is chosen from an unproved existence result.

## No longer needed

Removed the direct proof import `Sheaf.FieldTheory.TensorFieldExtensionGaloisInvariants`
from the item's module, replacing it with the new proved ring lemma. The tensor-invariants
module remains needed transitively by that lemma and is not pruned from the targets' closure.
The old direct proof dependency `lem-weil-pbc-tensor-field-extension-galois-invariants`
is replaced by `lem-weil-pbc-tensor-galois-prime-transitivity`; it is still used transitively.
Removed the redundant public import `Mathlib.RingTheory.TensorProduct.Maps` from the new
ring module, since `Mathlib.RingTheory.Spectrum.Prime.RingHom` publicly imports it.
No planned node or module is mathematically pruned: the original tensor-action, tensor-invariants,
affine-spectrum and pullback steps all remain used, with the ring steps grouped in the new node.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or incorrect mathematical step was found. Two planned dependencies
are Mathlib leaves (`pullbackSpecIso` and the algebra tensor map); they have no Sheaf modules
to import. The infinite fixed-field input is `InfiniteGalois.mem_range_algebraMap_iff_fixed`,
as already clarified in the node, rather than a finite-dimensional fixed-field theorem.

## New nodes

`lem-weil-pbc-tensor-galois-prime-transitivity` records the proved ring-level part of the
original argument in `lean/Sheaf/AlgebraicGeometry/TensorGaloisPrimeTransitivity.lean`.
It has the same chapter and unit, records the Mathlib and blueprint searches, and carries
its complete argument and exact Lean signature. No change record is needed: existing
interfaces and definitions are unchanged.


## Second reading by U1

1. Compared the existing Lean module and existing node with the repository by `diff`.
   The sole existing declaration's signature, docstring, universe and visibility are
   byte-for-byte unchanged. Only its proof and a private proof import changed. Existing
   node edits are confined to `proof`, `proof_deps` and `proof_origin`. There are no
   changed definitions, forced adaptations or changes to target statements. Verdict: pass.
2. Compiled both delivered modules in import order through `lcompile.py`, then compiled
   a scratch axioms probe against these exact compiled modules. Both declarations depend
   only on `propext`, `Classical.choice`, and `Quot.sound`. Neither module contains `sorry`
   or any forbidden declaration, and all local constructions use proved inputs.
   In particular the affine comparison is constructed explicitly, and the Galois witness
   comes from a proved theorem. Verdict: pass; one original hole closed, zero added.
3. There are no unproved split-off statements. Read the new proved ring lemma in full:
   its hypotheses allow the zero algebra (no prime points), the identity field extension,
   arbitrary non-finite-type algebras, and infinite algebraic Galois extensions. The action
   and stabilizer induction work in all these cases. Its inverse automorphism is necessary
   to convert ideal scalar multiplication into spectral comap. Repeated LeanFinder search
   using "Primes above one prime in scalar extension A tensor K are conjugate under
   automorphisms of K over k", Loogle search `PrimeSpectrum, Algebra.TensorProduct.map`,
   and `rg` in Mathlib tensor modules and both library roots. The hits are finite-group
   transitivity, integral-closure results, or purely inseparable spectral homeomorphisms;
   none replaces this specialization for arbitrary Galois extensions. The new lemma has
   its own module, complete proof docstring and matching node. Verdict: pass.
4. Read the scheme transport and ring proof from the target downward. They use the
   existing tensor-invariants theorem and Mathlib's profinite transitivity directly,
   without introducing a lower hole or restating the scheme theorem under another name.
   Every remaining import supplies signature data or an actual proof tool. In particular
   the existing public Jacobian import supplies `specAlgEquivOver` in the signature.
   Removed one redundant import from the new module and made the report name the old
   direct proof dependency that is now indirect. Checked `dag/units/sk-thm-p1.json`,
   including `realized`: no unit statement or step is replaced or bypassed. Verdict: pass.
5. Matched both nodes' Lean records to the declarations and each proof step to its uses.
   The existing node records the affine comparison, ring theorem application, and action
   compatibility; the new node records the explicit action, continuous/invariant
   instances and profinite prime theorem. Their dependency unions agree with their
   `proof_deps`, and the new node has source, searches, creation, blueprint, chapter,
   unit and exact Lean signature records. Verdict: pass.

Second reading changed only the redundant import in the new ring module and this report's
explicit dependency accounting and review record. No proof repair was needed.
