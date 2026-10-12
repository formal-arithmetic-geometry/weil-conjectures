## What changed

Proved `AlgebraicGeometry.Scheme.Hom.hasUniversallyBoundedFibers_of_isLocallyQuasiFinite`
in the assigned module, without changing its signature or public imports. Added the
proof-only import `Mathlib.Algebra.Module.SpanRankOperations` and three fully proved private
helpers: `finite_spec_bound`, `finite_affine_bound`, and `bounds_of_open_cover`.

The proof follows Stacks Tag 03JA: choose finitely many compatible affine opens, make their
restrictions quasi-finite, factor them as open immersions followed by finite morphisms, bound
the finite morphisms by their number of module generators, and sum the bounds on a finite
open cover of each fibre. Composition with each target-open inclusion bounds the maps to
`Y` directly, so no separate residue-field comparison is needed. The item node's proof,
proof_deps and proof_origin now describe this argument. No unit statement or realized unit
step is bypassed (checked `dag/units/sk-thm-p1.json` and its blueprint section).

Validation: the complete module compiles without warnings through `lcompile.py`; all lines
are at most 100 characters. Read Stacks `lemma-locally-quasi-finite-qc-source-universally-bounded`
and `definition-universally-bounded`, corresponding to Tags 03JA and 03J4. Edge cases: the
finite subcover may be empty; the proof uses `Fin 0` and the existing empty-cover case of
`finite_open_cover_degree_sum`. It imposes no nonemptiness or separation hypothesis on either
scheme. All original proof-dependency imports are used.

Searches through `msearch.py`: LeanFinder returned the existing Mathlib locally quasi-finite
interfaces, Loogle for `"finrankΓ"` returned no hits, and grep for
`finrankΓ|universallyBounded` returned no hits. Direct searches of the actual library found
`nonempty_algEquiv_tensorProduct_Γ_of_isPullback`, `finrankΓ_eq_of_iso`, and the already proved
factorization and finite-open-cover theorems. Direct Mathlib search found
`Submodule.FG.spanFinrank_baseChange_le`, which closes the finite affine case without a new
statement.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Hom.hasUniversallyBoundedFibers_of_isLocallyQuasiFinite`
(blueprint: `lem-weil-pbc-lqf-qc-source-bounded-fibres`). One hole closed, zero holes added;
zero `sorry`s remain in the delivered module. All three private helpers are proved.
No new modules and no split-off statements.

This is a complete proof from existing declarations, not an axiom-free closure of all its
existing dependencies. `#print axioms` reports `sorryAx` through
`AlgebraicGeometry.Scheme.Hom.boundsFiberDegrees_comp`, whose existing dependency
`AlgebraicGeometry.Scheme.Hom.finite_fiber_degree_pullback` is still `sorry` in
`Sheaf.AlgebraicGeometry.FiniteFiberDegreeBaseChange`
(node `lem-weil-pbc-fibre-degree-base-change`). This delivery leaves that module unchanged.
The factorization, restriction, quasi-finiteness equivalence, immersion bound, and finite
open-cover sum have only `propext`, `Classical.choice`, and `Quot.sound` in the compiled
snapshot. The theorem's other axioms are exactly those three standard axioms.

## No longer needed

No imports removed: each existing proof import is used, and both public imports remain.
No Sheaf or WeilConjectures module is claimed globally pruned.

Removed these four direct proof-dependency edges from the item node:

- `def-weil-pbc-localization-at-prime`: the finite bound uses an arbitrary residue-field
  point's ring map and the affine pullback section isomorphism directly.
- `lem-weil-pbc-spec-residue-field-identification`: no identification with the ring-theoretic
  prime's residue field is required.
- `lem-weil-pbc-residue-field-point-naturality`: composition with `Vᵢ → Y` replaces the
  comparison of the two residue fields; fibre-cover pasting uses `Spec κ(y)` throughout.
- `lem-weil-pbc-finite-over-field-affine-finite-dim`: finiteness and the dimension estimate
  are returned together by the finite-open-cover theorem, while the finite affine case
  uses `IsFinite.finite_appTop` over an arbitrary ring directly.

The corresponding Mathlib modules may remain reachable indirectly; these are pruned direct
DAG edges, not assertions that the whole target import closure loses those modules.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The original plan's residue-field
identification and naturality steps were unnecessary: composition bounds provide a shorter
way to compare all covering pieces over the original target. The source argument and the
unit's route are preserved. The complete proof required no statement or definition changes.

## Second reading by M1

1. **Interface: pass.** Compared the complete module with the read-only repository
   version. The existing theorem signature is byte-for-byte identical; both public
   imports and the exposed public section are unchanged. Only the proof, its outline,
   three private theorem helpers, authorship, and one proof-only import differ.
   There is no definition or interface change and no change record is required.
2. **Proof: pass, with the existing open dependency disclosed.** Independently
   compiled a scratch copy containing the delivered module verbatim and appended
   `#print axioms` checks. Compilation succeeded without warnings. The theorem uses
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the latter is
   inherited from the existing composition bound and its named open base-change
   theorem, not introduced here. Checked the factorization, restriction, immersion,
   quasi-finiteness equivalence, and finite-cover sum: all have only standard axioms.
   No delivered `sorry`, forbidden declaration, hollow definition, or data definition
   choosing an arbitrary witness from an unproved existence theorem occurs.
3. **Split statements: pass (none).** No statements were split off and no holes added.
   Read the private helpers: the finite bound uses a finite module and its actual
   generator rank; the affine transport uses an isomorphism; the covering helper
   transports each piece through the canonical pullback isomorphism. Empty source,
   empty fibres, zero generator rank and `Fin 0` require no extra assumptions.
4. **Route and pruning: pass.** Read the uniform-bound definition and the invoked
   factorization, composition and finite-cover interfaces, and checked the proof
   against [Stacks 03JA](https://stacks.math.columbia.edu/tag/03JA) and
   [03J4](https://stacks.math.columbia.edu/tag/03J4). A fresh Mathlib grep search for
   `degree.*quasi|quasi.*degree|bounded.*fiber|bounded.*fibre`, plus direct searches
   in both Lean roots, found no theorem providing a shorter uniform degree bound.
   Every proof import supplies an explicitly used declaration; the extra span-rank
   import is correctly private. The four removed edges listed above are exactly the
   old direct dependencies no longer needed after the correction below. Checked
   `sk-thm-p1.json`'s statement and all four realized step lists: this below-unit
   simplification bypasses none of those realizations or unit steps.
5. **DAG: corrected, then pass.** Only `proof`, `proof_deps`, and `proof_origin`
   differ from the old node. The six steps describe the actual cover, generator
   bound, affine factorization, composition and pullback/sum proof. Their dependency
   union agrees with `proof_deps`. There are no new nodes to validate.

Changed only the existing node: restored `def-weil-residue-field` to step 3's uses
and to `proof_deps`, because the proof still explicitly uses residue fields. The
first version had inadvertently removed that fifth edge while reporting only the
four legitimate removals. No Lean repair was needed; added this independent review
and retained the one-hole-closed, zero-holes-added accounting.
