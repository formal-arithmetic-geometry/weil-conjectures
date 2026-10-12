## Worker report

Item `lem-sc-boundary-cech-injective-middle`, module `Sheaf.Paper.BoundaryCechInjectiveMiddle`,
theorem `AlgebraicGeometry.Scheme.Modules.boundary_cech_injective_middle` (proof `sorry`).

The item had been released with "unit statement: the Lean leaves the connecting map and the
local-lift cocycle unconstrained". The node can be written as it stands; what was missing was the
Lean for its objects. The statement is now tied to the recorded declarations:

- `X` a scheme; `0 → A → I → Q → 0` short exact with `I` injective: `S : ShortComplex X.Modules`,
  `hS : S.ShortExact`, `[Injective S.X₂]`.
- `U = {U_i}` an open covering: `{ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)`.
- `q ∈ H^0(X, Q)` and lifts `x_i ∈ I(U_i)` of `q|_{U_i}`: `q : S.X₃.val.obj (op ⊤)`,
  `x : ∀ i, S.X₂.val.obj (op (U i))`, `hx : ∀ i, S.g.val.app (op (U i)) (x i) =
  S.X₃.val.presheaf.map (homOfLE le_top).op q`.
- "`(x_{i_1} - x_{i_0})` is an `A`-valued Čech 1-cocycle": `∃ z : (Čech complex of A).cycles 1`
  whose component at every `y : Fin 2 → ι`, mapped by `S.f`, is
  `x (y 1)|_{U_{y 0} ∩ U_{y 1}} - x (y 0)|_{U_{y 0} ∩ U_{y 1}}`. The Čech complex is
  `(CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat`, the one of
  `IsModuleCechComparison` (def-sc-module-cech-comparison); `S.f` is injective on sections, so
  `z` is determined.
- "the canonical map `c_A` sends its class to `∂(q)`": `c` with
  `hc : IsModuleCechComparison U S.X₁ 1 c` (the canonical comparison of Stacks 01EQ, unique for a
  covering and existing by lem-sc-cech-comparison-map-naturality), and
  `c (homologyπ 1 z) = RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0
  (toRightDerivedZero.app S.X₃ q)`: the connecting map is the recorded
  `moduleCohomologyBoundary` (def-sc-module-cohomology-boundary), and `q` is read in `H^0`
  through `Functor.toRightDerivedZero`.

`stmt_deps` gains the two landed definition nodes whose declarations the statement uses:
def-sc-module-cech-comparison and def-sc-module-cohomology-boundary (STMT_DEPS MAY GAIN LANDED
NODES).

Sign: with Mathlib's Čech differential `d(s)_{i_0 i_1} = s_{i_1} - s_{i_0}` the node's cocycle
`x_{i_1} - x_{i_0}` and class `+∂(q)` are those of the node's proof (horseshoe connecting map,
identified with the triangle boundary by `rightDerived_triangle_connecting`).

Finding outside this item: the landed sibling `boundary_cech_local_lifts`
(lem-sc-boundary-cech-local-lifts, `Sheaf.AlgebraicGeometry.BoundaryCechLocalLifts`) uses the
opposite difference `t (x 0) - t (x 1)` with the same boundary, as its node still does
(`f_{i_0} - f_{i_1}`); with lem-sc-boundary-cech-compatibility as corrected by the lead on
2026-10-10 one of the two signs is off. It is a stage-3 repair of that node, not of this one.

Edge cases: empty index type (then `X` is empty); `q = 0`; repeated indices. Searches: grep of
`lean/Sheaf` and `lean/WeilConjectures` for `moduleCohomologyBoundary`, `IsModuleCechComparison`,
`homologyπ 1`: only `boundary_cech_local_lifts` (algebra-sheaf case) and `cechH1Map_natural`;
no existing statement. Compile: 3.0 s locally.

## Second reading by Z2

Independent reader Z2-bim (a fresh `codex exec` session that did not write the module):

VERDICT: PASS

1. **Objects and hypotheses match.** `X` is the scheme; `S`, `hS` encode `0 → A → I → Q → 0`, with `[Injective S.X₂]`; `U`, `hcover` encode the open covering. `q` is a global section of `Q`, and `x`, `hx` specify exactly the chosen local lifts. No additional mathematical restriction or weakened conclusion was found.

2. **The cocycle is now determined.** `z : cycles 1` imposes the actual Mathlib Čech cocycle condition. Its component equation specifies every overlap component after applying `S.f`. Since `hS` makes `S.f` monic, hence injective on sections, these equations uniquely determine `z`. The earlier unconstrained-cocycle fault is resolved.

3. **Indices and Čech sign match.** With `y 0 = i₀`, `y 1 = i₁`, the finite product of opens represents their intersection, and the projections give the restrictions. Mathlib’s differential is the alternating coface sum: face zero omits `i₀`, face one omits `i₁`. Thus `d(s)ᵢ₀ᵢ₁ = sᵢ₁ − sᵢ₀`, exactly the displayed difference.

4. **Comparison and boundary are constrained correctly.** `IsModuleCechComparison` requires the α/β comparison equation for every injective resolution. Invertibility of `H¹(α)` for a cover gives uniqueness; the landed comparison-naturality statement supplies existence. Consequently, universally binding `c` with `hc` expresses the canonical map’s property. Unlike the sibling’s existential formulation, this theorem does not itself assert its existence, but that existence is already supplied. `moduleCohomologyBoundary` is the transported derived-triangle boundary, and `toRightDerivedZero.app S.X₃` correctly identifies global sections with `H⁰(X,Q)`.

5. **The sign is plausibly correct.** In the stated horseshoe,
   `d_B(0,q̃) = (-q̃,0)`, so its snake boundary is `-[q̃]`. Meanwhile,
   `d_Tot(x) = β(z) + α(q̃)`, giving `c[z] = -[q̃]`. The landed `rightDerived_triangle_connecting` identifies that horseshoe boundary with the triangle boundary used here. These computations agree; I found no definite sign error.

6. **Sibling discrepancy:** `BoundaryCechLocalLifts.lean` indeed specifies `t(x 0) − t(x 1)` while equating its comparison class to the same boundary. That is the opposite convention, matching the warning in this node’s `lead_note`. It needs separate review; it is not a fault of this file.

7. **Remaining checks:** An empty cover index forces `X` empty; sections and relevant cohomology then vanish, so no counterexample arises. Empty opens and repeated indices also cause no problem. No hollow hypothesis or definition was found. Universes follow the landed infrastructure. The docstring includes the source, blueprint identifier, and all three proof steps. Lines satisfy the 100-character limit; imports support the definitions and injective-resolution instance infrastructure. Searches found no existing equivalent theorem in `lean/` or Mathlib. This was a source-level review, without compilation or file changes.
