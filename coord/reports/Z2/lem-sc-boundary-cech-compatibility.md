## Worker report

Item `lem-sc-boundary-cech-compatibility`, module `Sheaf.Paper.BoundaryCechCompatibility`, theorem
`AlgebraicGeometry.Scheme.Modules.boundary_cech_compatibility` (proof `sorry`). The item became
open when its statement dependency lem-sc-boundary-cech-injective-middle landed.

It is the statement of that node without the injectivity of the middle term, with the same
objects:

- `0 → A → B → C → 0` short exact: `S : ShortComplex X.Modules`, `hS : S.ShortExact`.
- the covering: `{ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)`.
- `s ∈ H^0(X, C)` and lifts `t_i ∈ B(U_i)`: `s : S.X₃.val.obj (op ⊤)`, `t`, `ht`.
- "the differences `t_{i_1} - t_{i_0}` are sections of `A` and form a Čech 1-cocycle":
  `∃ z : (Čech complex of A).cycles 1` whose components map under `S.f` to
  `t (y 1)| - t (y 0)|` on `U_{y 0} ∩ U_{y 1}`; determined, as `S.f` is injective on sections.
- "under the canonical homomorphism `c_A` its class maps to `∂(s)`": `c` with
  `IsModuleCechComparison U S.X₁ 1 c`, and `c (homologyπ 1 z) =
  RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0 (toRightDerivedZero.app S.X₃ s)`.

The sign is the one fixed by the lead on 2026-10-10 (`t_{i_1} - t_{i_0}`, class `+∂(s)`), the
same as in the child. `stmt_deps` gains def-sc-module-cech-comparison and
def-sc-module-cohomology-boundary (landed definition nodes the statement uses).

Imports by rule 7 of `stages/2-statements.md` §3: the modules of the statement and proof
dependencies (`SchemeModulesEnoughInjectives`, `RightDerivedUniversalDeltaFunctor`,
`SiteCechComplex`, `BoundaryCechInjectiveMiddle`, `PQFCohomology`) are imported without
`public`; this repairs point 1 of the second reading below, the only fault it found.

Finding outside this item (also in the second reading, point 6): the landed
`boundary_cech_local_lifts` (lem-sc-boundary-cech-local-lifts) uses the opposite difference with
the same boundary; it needs the reversed difference or a negated boundary.

Edge cases: empty index type, `s = 0`, repeated indices. Searches: as for the child; no existing
statement. Compile: 3 s.

## Second reading by Z2

Independent reader Z2-bcc (a fresh `codex exec` session that did not write the module). Its
verdict was RETURN for the missing imports of point 1 alone; they were added as it asks and the
statement was not otherwise changed:

VERDICT: RETURN

1. **Missing proof-dependency imports.** The contract (§3; stages/2-statements.md rule 7) requires imports of stated proof dependencies. Neither `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives` nor `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor` is imported, even transitively. Add ordinary, non-public imports. Add `Sheaf.Paper.BoundaryCechInjectiveMiddle` when delivering the reviewed sibling with this file; document any deferred import.

2. **The mathematical statement matches the node.** `X` is the scheme; `S.X₁, S.X₂, S.X₃` are `A, B, C`; `hS` asserts short exactness. No injectivity of **B** is assumed. `U, hcover` give the covering; `s, t, ht` give the global section and its local lifts. The node is precisely the injective-middle statement with middle-term injectivity removed.

3. **The cocycle is fully determined.** `cycles 1` asserts the cocycle condition. The component equation specifies every component after inclusion into B. Since `S.f` is monic and injective on sections, product projections and `iCycles` determine `z` uniquely. The categorical product of the two opens is their intersection. With `y 0 = i₀`, `y 1 = i₁`, the difference is exactly `tᵢ₁ − tᵢ₀`. Mathlib’s alternating cofaces give `d⁰(t) = tᵢ₁ − tᵢ₀`.

4. **The sign is plausibly correct.** In the injective-middle computation, the total differential is `D(t) = β(z) + α(q̃)`, hence `c[z] = −[q̃]`. The horseshoe differential `d_B(a,b) = (da − b, −db)` sends the lift `(0,q̃)` to `(−q̃,0)`, giving `∂(q) = −[q̃]`. `rightDerived_triangle_connecting` identifies this with the triangle boundary used by `moduleCohomologyBoundary`. No definite sign error in this file.

5. **The cohomology and comparison are correctly specified.** `moduleCohomologyBoundary … S hS 0` is the actual transported triangle connecting map. `toRightDerivedZero.app S.X₃ s` reads the global section in H⁰ through the canonical isomorphism for left-exact global sections. `hc` fixes `c` by the α/β comparison equation; invertibility of H¹(α) ensures uniqueness. Universal binding therefore expresses the canonical map correctly. The supplied injective-middle sandbox also binds `c` universally; the landed `BoundaryCechLocalLifts` binds it existentially.

6. **External sign discrepancy:** `BoundaryCechLocalLifts.lean` does use `t(x 0) − t(x 1)` with the same boundary and comparison convention. Its formula needs the reversed difference or a negated boundary. This is not a fault of the reviewed file.

7. Empty cover indices force empty X; sheaf sections and the relevant classes then vanish. Empty X and zero objects cause no issue. The universe binders follow the existing comparison API; no hollow mathematical hypothesis appears. Both docstrings contain sources and the blueprint identifier, and the declaration reproduces the node’s three proof steps. All lines are ≤100 characters. Searches found no existing exact general statement in `lean/`, Mathlib, or the source library. This was a read-only review, without compilation.
