## What changed

Closed `AlgebraicGeometry.Scheme.Modules.picardExternal_right_cech_tensor_exact` in the item module, with its statement and public imports unchanged. All added imports are proof-only. The proved scalar Cech and tensor-total components are private helpers in this module; no new module or node is delivered.

The scalar argument inducts on tuple length to prove affine intersections, maps the sequence to abelian sheaves, and uses the proved affine Cech section-lifting criterion. Product projections and `ModuleCat.piIsoPi` prove monicity, epicity and middle exactness degreewise. The tensor argument evaluates the bicomplex twice, applies Mathlib's exact `tensorLeft` over a field, and uses the existing first-quadrant extended-total exactness theorem. Explicit bifunctor identity-map compatibility identifies the resulting maps.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.Modules.picardExternal_right_cech_tensor_exact` (`lem-sc-picard-external-right-cech-exact-tensor`). Added no holes. No `sorry` remains in the delivered module. The private helpers `scalar_cech_map_proj`, `picard_right_cech_sections_exact`, `tensorComplex_zero`, `tensor_total_extension_shortExact`, and `picard_right_tensor_total_shortExact` are all proved.

## No longer needed

The original `pqf-lem-affine-vanishing` dependency is no longer needed on this branch: affine section surjectivity is obtained directly from the proved affine Cech lifting machinery. `lem-sc-picard-affine-diagonal-intersections` remains needed via Mathlib's affine relative diagonal criterion. No original public import was removed. No product-cover exactness or cup-comparison theorem is used.

Removed the draft proof imports and separate modules `Sheaf.AlgebraicGeometry.PicardRightCechSectionsExact` and `Sheaf.AlgebraicGeometry.PicardRightTensorTotalShortExact`, consolidating their proved components as private helpers. Their draft nodes are not delivered. Removed the redundant draft imports `Mathlib.Order.Fin.Basic` and `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`; used imports already provide the necessary APIs.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's elementary tensor-total step required explicit bifunctor map-identity compatibility and the already proved first-quadrant totalization theorem. Unconstrained map comparisons caused excessive unfolding; using abstract cochain complexes and normalizing the concrete functor maps resolves this without changing a definition or increasing the compile timeout.

The empty tuple-index sets give zero product modules. Nonempty tuple length, not nonempty cover indexing, is used for affine intersections. Extension by zero handles negative degrees. No covering assumption, flatness over a scheme's structure sheaf, or new hypothesis is introduced. The unit route remains unchanged. All chosen lifts are inside proved theorems; no definition is added or changed.

## Second reading by V4

1. **Interface: pass.** Read the full repository/sandbox diff. The existing
   `picardExternal_right_cech_tensor_exact` signature is byte-for-byte identical,
   including universes, field, affine relative diagonals of both morphisms,
   finite index types, affine opens, all quasi-coherence instances, and the
   short-exact conclusion for the same `picardRightTensorCechFunctor`. Both
   original public imports and the original docstring are unchanged. No
   definition, other existing declaration, or change record is delivered.

2. **Proof and axioms: pass.** Compiled the sole delivered module through
   `lcompile.py --all` with no errors or warnings. Compiled a scratch copy with
   `#print axioms` for the target and all five private helpers: each uses only
   `propext`, `Classical.choice`, and `Quot.sound`, never `sorryAx`. Text checks
   found no `sorry`, forbidden declaration mechanism, or line over 100 columns.
   The coordinate lifts use proved section exactness/surjectivity inside theorem
   proofs; no data definition or arbitrary witness from an unproved existence
   theorem is introduced. The bifunctor identity normalization checks both maps
   of the short complex, not merely its three objects.

3. **Split statements and edge cases: pass.** No new holes, public statements,
   modules, or nodes are split off. The scalar helper proves affine intersections
   by induction on the positive length `n + 1`, not by assuming a cover or an
   inhabited index type. An empty right index type gives an empty tuple product,
   hence the zero sequence; an empty left index type or zero left coefficient
   gives zero tensor terms. The scalar middle-exactness and surjectivity branches
   assemble independent coordinate lifts via `ModuleCat.piIsoPi`. Field flatness
   is used only over `k`, never over a scheme's structure sheaf. Totalization has
   finite diagonals and extension gives zero sequences in negative degrees.

4. **Route, search, and pruning: pass.** Read the existing affine Cech lifting
   source, the module-sheaf forgetful colimit instance, the Cech projection APIs,
   Mathlib's flat tensor functor API, and `shortExact_extended_total`. Independent
   searches used `tensorLeft preserves exact sequences field` through `msearch.py`
   grep, and `shortExact.*cech`, `cech.*shortExact`, `tensor.*shortExact`, and
   `isAffineHom_diagonal_iff` through `rg` in Sheaf, upstream, and Mathlib.
   `etale_cech_shortExact_of_sections` concerns an etale site and larger universe;
   `TopCat.Sheaf.shortExact_cechComplex` concerns the explicit abelian complex,
   rather than the scalar categorical complex. Neither directly replaces the
   scalar proof. The now-proved left-coefficient module has private helpers and
   fixes the other tensor argument on integer complexes; it supplies no public
   replacement for the right helper. All five proof imports supply declarations
   or instances explicitly used; none is incorrectly public. `No longer needed`
   names the sole removed original proof dependency, `pqf-lem-affine-vanishing`.
   No original public import or existing module is pruned. Read
   `dag/units/sk-prop-av-cube.json`: its cube statement and general-cube application
   step are unchanged, and its `realized` entries are empty; this supporting
   coefficient proof changes no unit realization or route. The generated
   literature unit file is absent on this machine; its statement and proof step
   are present in that unit JSON and were read there.

5. **DAG: pass.** Only `proof`, `proof_deps`, and `proof_origin` differ in the
   existing node. The dependency union equals the steps' `uses`: affine diagonal
   intersections; exact forgetting to abelian sheaves; affine basic-open Cech
   acyclicity; topological Cech section lifting; extended first-quadrant total
   exactness. Each matches the declaration actually applied, directly or through
   the proved affine Cech wrapper. The coordinate product assembly and field
   tensor argument are written out in Lean and correctly marked elementary in
   this node. The existing Lean record still matches the unchanged signature;
   no new-node fields or statement-change record are needed.

**Changes by the second reader:** appended this independent review. The proof,
imports, definitions, signatures, and node records required no repair. One
original hole is closed and zero holes are added: this is a proof, not a
hole-preserving decomposition. No global import-closure ledger count is claimed.
