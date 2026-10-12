## What changed

Proved `AlgebraicGeometry.Scheme.Hom.isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber`
in `Sheaf.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs`, with the statement
unchanged. Added the proof-only import `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`.
The proof uses the Mathlib candidate already recorded on the node: isolation gives
stalk quasi-finiteness, then affine section-ring quasi-finiteness, then an open singleton
in the topological fibre. The canonical fibre homeomorphism transports this singleton
to the project's predicate. Updated the node route accordingly; the declaration docstring retains the original geometric plan.
No definitions or statements changed. The unit's realized statement and steps are
preserved; this auxiliary node is not itself a unit realization.

## Proved and sorry left

Proved the sole original sorry:
`AlgebraicGeometry.Scheme.Hom.isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber`
(node `lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs`).
No sorry remains in the module and no new sorry was introduced.
Local compilation and the dry run axiom probe and server compilation passed without warnings.
The initial preflight caught an accidental textual `letI` to `let` change in the signature;
restored the original signature exactly. The original docstring is also preserved, with
the actual shorter route recorded in the node and this report.

## No longer needed

No existing imports were removed: all three public imports supply the statement's
notions. No planned Sheaf proof dependency was imported. The following former proof
dependencies are no longer needed by this proof (their modules, if any, need not be
imported here; other users may still need them):

- `def-weil-finite-type-morphism` — `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `lem-weil-pbc-affine-open-spec-points`
- `def-weil-affine-spectrum` — `Mathlib.AlgebraicGeometry.Scheme`
- `lem-weil-pbc-affine-opens-induced-ring-map-spec-square`
- `def-weil-open-immersion` — `Mathlib.AlgebraicGeometry.OpenImmersion`
- `lem-weil-pbc-fibre-ring-primes-bijection`
- `def-pc-scheme-fibre` — `Mathlib.AlgebraicGeometry.Fiber`
- `lem-weil-pbc-residue-field-point-naturality`
- `lem-weil-pbc-open-fibre-product`
- `lem-weil-pbc-spec-residue-field-identification` — `Mathlib.AlgebraicGeometry.ResidueField`
- `def-pc-fibre-product` — `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `lem-weil-pbc-fibre-product-affine-spectra`

The retained fibre-spectrum homeomorphism is an existing Mathlib leaf, replacing the
long affine-chart and fibre-product identification route.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG already identified the successful Mathlib candidate,
but left its conversion to the project's predicate unproved. That conversion is a
singleton-image rewrite through the existing homeomorphism; no intermediate sorry
or new node is needed. The edge conditions (point membership, affine pair containment,
and local finite type) are all used with their original hypotheses.

## Second reading by E3

1. Compared the complete Lean module and node against the repository. PASS: the
   existing theorem signature is byte-for-byte unchanged, as are all definitions and
   docstrings; the only Lean changes are its proof and a plain proof-only import.
   No change record is required.
2. Compiled the module locally without errors or warnings. PASS: no sorry or prohibited
   declaration occurs in the delivered module. An axiom probe for
   `AlgebraicGeometry.Scheme.Hom.isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber`
   reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
3. PASS: no statements were split off and no new declarations or nodes were added.
   Read the Mathlib affine-pair and isolated-singleton equivalences and the project's
   `Algebra.IsQuasiFiniteAtPrime` definition: the final homeomorphism image is exactly
   its singleton. No extra point, finite-type, or containment hypothesis was introduced.
4. PASS: the proof uses the existing Mathlib route directly, with no deferred project
   theorem. The original public imports provide the signature's fibre, finite-type,
   and project predicate notions; the added QuasiFinite import is proof-only. Compared
   old and new proof_deps: every removed dependency is listed under No longer needed.
   Checked `dag/units/sk-thm-p1.json`: this auxiliary node realizes none of its fixed
   statement or steps, and its realized route is unchanged.
5. PASS: the node changes only proof, proof_deps, and proof_origin. Its steps match
   finiteType_appLE, the two quasi-finiteness conversions, and singleton transport
   through preimageHomeomorphFiber. The retained dependency declarations agree with
   the actual proof; there are no new-node obligations.

Second reading changed only this report, adding the independent review. No repair to
the Lean proof or DAG was needed. One original hole closed; zero holes added.
