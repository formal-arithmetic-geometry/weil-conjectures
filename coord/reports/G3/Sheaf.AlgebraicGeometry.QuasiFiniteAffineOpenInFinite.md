## What changed

Proved `AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_of_isQuasiFinite_affine`
in `Sheaf.AlgebraicGeometry.QuasiFiniteAffineOpenInFinite` without changing its signature.
Added the proof-only import `WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization`.
Updated the existing node's proof, proof_deps and proof_origin to the shorter route.
All three public imports are retained because they supply the statement and its definitions.

The proof converts fibre isolation to discrete set-theoretic fibres using `fiberHomeo`,
then uses Mathlib's local-quasi-finiteness criterion. Affineness supplies separation and
quasi-compactness/quasi-separatedness of the base. The existing general finite-factorization
result gives the intermediate scheme, which is affine because it is finite over an affine base.
The item is absent from every `sk-thm-p1.realized` list, so this changes only the route below
that unit. `thm-pqf-zmt-factorization` is a closed source-library tool in another unit.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_of_isQuasiFinite_affine`
(node `lem-weil-pbc-quasi-finite-affine-open-in-finite`).
No holes remain in the item; no holes or declarations were added elsewhere.
A clean local compile succeeds. `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`; this is a proof, not a decomposition.

## No longer needed

Removed proof-only imports:
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`
- `Sheaf.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs`
- `Sheaf.RingTheory.QuasiFiniteAtPrime`
- `Sheaf.RingTheory.QuasiFiniteIntegralClosureOpen`

The following planned dependency nodes are no longer needed by this item's proof
(other targets may still reach them):
- `lem-weil-pbc-affine-open-spec-points`
- `def-weil-open-immersion`
- `def-pc-scheme`
- `lem-weil-pbc-affine-opens-induced-ring-map-spec-square`
- `def-weil-affine-spectrum`
- `def-weil-finite-type-morphism`
- `lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs`
- `def-weil-pbc-ring-map-quasi-finite-at-prime`
- `lem-weil-pbc-quasi-finite-ring-map-integral-closure-open`
- `def-weil-pbc-integral-closure`
- `def-weil-finitely-generated-module`
- `lem-weil-pbc-spec-finite-ring-map-finite`
- `def-pc-base-change`
- `lem-weil-pbc-finite-morphism-permanence`

The integral-closure route and its descendants need no work for this item. This is a local
pruning claim, not a claim that those modules leave the entire targets' closure.
`QuasiFiniteAtPrime` is still transitively exposed by the statement's `QuasiFiniteMorphism`
import; its direct proof-only import was redundant.

## Where the brief, the DAG or earlier work was wrong

The earlier DAG search missed the source library's general finite factorization theorem
in `WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization`, now also recorded
on `thm-pqf-zmt-factorization`. Its current proof is complete, and the specialized theorem's
axiom check confirms there is no transitive sorry dependency. No statement or source error
was found. The existing declaration docstring is retained as requested by the Lean skill;
it describes the former five-step plan, while the delivered node records the actual proof.
Searches used LeanFinder, Loogle, the launcher grep search, and rg over the source library
and Mathlib; the decisive hit was the general source-library theorem.

## Second reading by G3

1. Signature preservation: PASS. Compared the complete delivered module against the
   repository with `diff -u`. The sole existing declaration's signature and all definitions
   and docstrings are byte for byte unchanged. Only its proof and proof-only imports changed;
   no change record is needed.
2. Proof and trust: PASS. Independently compiled the module without errors or warnings.
   A scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_of_isQuasiFinite_affine`
   reports only `propext`, `Classical.choice`, and `Quot.sound`. The delivered file contains
   no `sorry`, additional declaration, hollow definition, or forbidden trust mechanism.
   Read the general factorization theorem and the definition of `f.IsQuasiFinite`:
   finite type and quasi-compactness are taken directly from `hf`; isolation transfers via
   the fibre homeomorphism to open singletons in every set-theoretic fibre. Affine schemes
   supply the separation and base compactness conditions. Finite over affine supplies
   affineness of the intermediate scheme, and the equality is reversed correctly.
3. Split statements: PASS, vacuous. No statements or holes were split off. The route uses
   an existing source-library theorem, not a new restatement. Searched the library and
   Mathlib for the factorization and fibre-discreteness declarations and read the relevant
   existing statements. Empty source and empty fibres pose no extra condition: the singleton
   argument quantifies over points actually in the fibre, and the general theorem applies
   without a nonemptiness hypothesis.
4. Route and pruning: PASS. The general finite factorization is already proved and is a
   shorter route than the integral-closure reconstruction. The sole new import is private
   to the proof; the retained public imports supply the statement's notions. All four
   removed direct imports and all fourteen removed old `proof_deps` are listed above.
   Checked `dag/units/`: this item appears in no `realized` list, so no required unit step
   is bypassed. The borrowed factorization theorem keeps its own established unit route.
5. DAG correspondence: PASS. Compared the node JSON files; only `proof`, `proof_deps`,
   and `proof_origin` changed. Each recorded proof step matches the Lean proof, the
   dependencies are exactly their union, and each dependency has a library declaration
   or Mathlib match. No new node or statement change is present.

Second reading changed only this report, adding the independent checks and verdicts.
No Lean or DAG repair was needed.
