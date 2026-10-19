## Worker report

The module `Sheaf.CategoryTheory.SingleHornRelativeCompletion` states
`SSet.Enhanced.single_horn_relative_completion`, with its sole proof `sorry`.
It introduces no definition and changes only the item's `lean` record.
The seven-step natural-language proof is in the theorem docstring, including the
facewise retraction argument chosen by the node instead of the printed K2 gluing.

Source checked directly: Lurie, Higher Algebra, Lemma the project server, printed pp. 330–332,
https://www.math.ias.edu/~lurie/papers/HA.pdf. Page 330 gives the inner fibration
and cocartesian lift hypothesis; page 331 explicitly gives the individual
extension subclaims (i-prime) and (ii-prime); page 332 finishes the construction.
The PDF and extracted excerpts are sandbox reference material, not delivered files.
The source's individual-extension assertion matches the node; no source-based
statement correction or additional node is needed.

Every hypothesis and conclusion is rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| Small simplicial sets and fixed horn H | `E S : SSet.{u}`, `(horn 3 2).toSSet`, `(horn 3 2).ι` |
| Inner fibration r:E→H | `r` and `_hr : InnerFibration r` |
| Each vertex over 1 | `_hlift` quantifies over `x : E _⦋0⦌`; `stdSimplex.obj₀Equiv` of its image equals 1 |
| Source of an edge with target over 2 | Witnesses `y,e`, `E.δ 1 e = x`, `E.δ 0 e = y`, and the vertex label of `y` is 2 |
| Edge over 1→2 | `yonedaEquiv.symm e ≫ r ≫ (horn 3 2).ι = stdSimplex.map (SimplexCategory.mkOfSucc ⟨1, ...⟩)` |
| Cocartesian for the arbitrary base H | `IsCocartesianEdge r (yonedaEquiv.symm e)`; no Quasicategory instance on E or H |
| Map s:S→Δ³ and monomorphism u | `s : S ⟶ Δ[3]`, `u : E ⟶ S`, `[Mono u]` |
| su=ιr | `hcomm : u ≫ s = r ≫ (horn 3 2).ι` |
| u categorical equivalence | `_hu` is exactly the enlarged `hFun` testing condition in the Joyal dependency |
| Canonical E→S×H is an isomorphism | `_hpull : IsIso (pullback.lift u r hcomm)` |
| n≥2, 0<i<n | `_hn : 2 ≤ n`, `i : Fin (n + 1)`, `_hi₀ : 0 < i`, `_hiₙ : i < Fin.last n` |
| Specified simplicial horn map α | `α : (horn n i).toSSet ⟶ S` |
| Small Sα over Δ³ | Existential `Sα : SSet.{u}` and `sα : Sα ⟶ Δ[3]` |
| Monomorphism v over Δ³ | Existential `v : S ⟶ Sα`, `Mono v`, and `hv : v ≫ sα = s` |
| v categorical equivalence | Same enlarged `hFun` condition applied to `v` |
| Canonical map induced by vu is an isomorphism | `IsIso (pullback.lift (f := sα) (g := (horn 3 2).ι) (u ≫ v) r ...)`; its equality proof uses only associativity, hv and hcomm |
| vα extends to Δⁿ | `∃ b : Δ[n] ⟶ Sα, (horn n i).ι ≫ b = α ≫ v` |
| No simultaneous filling or quasicategory conclusion | The conclusion stops at this one filler; it has no Quasicategory binder for Sα |

The witness `y` is just the target of `e`, so its explicit naming does not change
the lift hypothesis. The ambient Δ³ equality determines the unique edge 1→2
inside H because the horn inclusion is monic. `[Mono u]` and `Mono v` express
degreewise injectivity in this presheaf category. The categorical-equivalence tests
use `SSet.{max u v}` and `uliftFunctor.{v,u}` exactly as in the dependency and the
already-landed parent `RelativeJoyalFactorization`; the term variables `u,v` and
universe variables `u,v` occupy separate Lean namespaces. All universes and term
variables are explicit, with auto-implicit binding disabled.

Dependency declarations inspected and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: reexports the Mathlib primitives
  `SSet`, `SSet.horn`, `SSet.stdSimplex`, `SSet.yonedaEquiv`, and degreewise
  simplicial products/pullbacks. No private replacement was defined.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`: reexports
  `SSet.InnerFibration` and `SSet.Enhanced.IsCocartesianEdge` from
  `Sheaf.CategoryTheory.InfinityFibrations`. Its complete outer-horn signature
  was read; it takes no quasicategory instances and is applicable to H.
- `Sheaf.AlgebraicTopology.JoyalModelStructure`:
  `SSet.exists_joyal_model_structure`; its weak-equivalence characterization
  supplies the exact explicit `hFun` predicate used twice here, including the
  universe enlargement. No model structure is arbitrarily selected.
- Proof-only imports: `Sheaf.CategoryTheory.ModelCofibrantColimitComparison`
  (`HomotopicalAlgebra.modelCofibrantColimitComparison`),
  `Sheaf.AlgebraicTopology.JoyalQuasicategoryCharacterizations`
  (`SSet.joyal_quasicategory_characterizations`), and
  `Sheaf.CategoryTheory.AllCofibrantLeftProper`
  (`HomotopicalAlgebra.weakEquivalence_pushout_inl_of_all_isCofibrant`).
  The face-conservation proof dependency has no recorded Lean declaration at
  the time of writing, so its import is omitted; its role remains in the docstring.

Edge cases checked before writing:

- `n = 2, i = 1` is included. The outer values i=0 and i=n are excluded exactly
  by the strict inequalities. Dimensions 0 and 1 are excluded by n≥2.
- Empty E is permitted; the cocartesian lift hypothesis then quantifies over
  no vertices. Neither E nor S is assumed inhabited or a quasicategory.
- If there are no vertices over 1 the lift hypothesis is correctly vacuous,
  as in the node. It is not vacuous for arbitrary nonempty fibers over 1.
- For u the identity with S=E and s=rι, the canonical pullback condition has
  its usual meaning; no proper inclusion is required. Likewise v may be an
  identity if the specified horn already fills.
- The canonical map, rather than an arbitrary pullback isomorphism, is required
  both in the hypotheses and conclusion. The final IsIso fixes both projections.
- All objects Sα stay in the input universe u. The testing quasicategory may
  live in any enlargement max u v, following the recorded Joyal convention.

Searches for an existing declaration:

- `msearch.py`, LeanFinder: “Fill one inner horn by a categorical enlargement
  over Delta three preserving exactly its inverse Lambda three two”. Eight
  results, all horn₃₁/horn₃₂ gluing declarations, not categorical enlargements.
- `msearch.py`, LeanSearch: “A categorical enlargement over the three simplex
  fills one prescribed inner horn and preserves its inverse second inner three
  horn”. Eight results: horn gluing, Quasicategory.hornFilling and
  KanComplex.hornFilling. None preserves a fixed inverse horn by enlargement.
- `msearch.py`, Loogle: `"horn", "Mono", "equivalence"`. Zero results.
- `msearch.py`, Mathlib grep, AlgebraicTopology:
  `relative.*horn|horn.*relative|categoricalEquivalence`. Zero results.
- `rg` over upstream `WeilConjectures` and side `lean/Sheaf` with
  `relative.*[Hh]orn|[Hh]orn.*[Rr]elative|singleHornRelative|single_horn_relative|lem-coef-single-horn-relative-completion`:
  no upstream match; side hits are other relative-horn results and the parent
  RelativeJoyalFactorization's proof-docstring citation, not this statement.
- `rg` for `IsCategoricalEquivalence` found the core-testing and rigidification
  definitions in CoherentNerveInfrastructure and ContravariantSliceModel.
  Their signatures were read. They use different presentations; this item
  follows its specifically named Joyal node's ordinary hFun tests directly,
  as does its landed parent, without defining another equivalence predicate.
- `rg` for the chosen full theorem name across Mathlib, upstream, side sources,
  and `dag/lean_names_upstream.json`: no collision.
- `tools/lean_names_upstream.py show lem-coef-single-horn-relative-completion`:
  no recorded existing declaration for the item.

Validation: `scompile.py Q34 lem-coef-single-horn-relative-completion` compiled
both the sandbox probe and the named library-path file cleanly (2.1 s and 2.2 s).
The initial elaboration needed explicit f/g parameters on the final pullback lift;
these now name exactly sα and the horn inclusion. No substantive node fault or
statement dispute was found. The required delivery dry run is run after this report.

## Second reading by Q34

I reread the node `lem-coef-single-horn-relative-completion`, the theorem
`SSet.Enhanced.single_horn_relative_completion`, the recorded dependency
signatures, and Lurie, *Higher Algebra*, Lemma the project server (printed pp. 330--332).
The source's displayed pullback diagram and its individual-extension claims
(i-prime) and (ii-prime) agree with the node. The statement is not corrected.

The node's objects, hypotheses, and conclusion render in Lean as follows.

| Node item | Lean rendering and verdict |
| --- | --- |
| Small simplicial sets, (H=\Lambda^3_2), and its inclusion \(\iota\) | `E : SSet.{u}`, `(horn 3 2).toSSet`, and `(horn 3 2).ι`; exact objects. |
| Inner fibration `r : E → H` | `_hr : InnerFibration r`; exact dependency predicate. |
| Every vertex over 1 has a cocartesian edge over `1 → 2` | `_hlift` quantifies `x : E _⦋0⦌`, tests its label as `1`, and supplies `y`, `e`, the two face equations, label `2` for `y`, the edge equation using `mkOfSucc ⟨1, ...⟩`, and `IsCocartesianEdge r ...`; exact outer-horn notion over the arbitrary base. |
| Small `S → Δ³` and monomorphism `u : E ↪ S` | `(S : SSet.{u})`, `s`, `(u : E ⟶ S)`, and `[Mono u]`; exact. |
| Commutativity `s u = ι r` | `hcomm : u ≫ s = r ≫ (horn 3 2).ι`; the same equality in categorical composition order. |
| `u` categorical equivalence | `_hu` is the recorded Joyal weak-equivalence test over all `C : SSet.{max u v}` with `C.Quasicategory`; exact dependency convention. |
| Canonical `E → S ×_{Δ³} H` is an isomorphism | `_hpull : IsIso (pullback.lift u r hcomm)`; it is the canonical lift, not an arbitrary isomorphism. |
| `n ≥ 2`, `0 < i < n`, and `α : Λⁿᵢ → S` | `_hn : 2 ≤ n`, `i : Fin (n + 1)`, `_hi₀ : 0 < i`, `_hiₙ : i < Fin.last n`, and `α`; `Fin.last n` gives exactly `i < n`. |
| Small `Sα → Δ³` and monomorphism `v : S ↪ Sα` over `Δ³` | The existential `(Sα : SSet.{u})`, `sα`, `v`, `Mono v`, and `hv : v ≫ sα = s`; exact. |
| `v` categorical equivalence | The second enlarged Joyal `hFun` test, with `v` mapped by `uliftFunctor`; exact. |
| Canonical pullback map induced by `v u` is an isomorphism | `IsIso (pullback.lift (f := sα) (g := (horn 3 2).ι) (u ≫ v) r ...)`; its equality proof follows only associativity, `hv`, and `hcomm`; exact canonical map. |
| `v α` extends over `Δⁿ` | `∃ b : (Δ[n] : SSet.{u}) ⟶ Sα, (horn n i).ι ≫ b = α ≫ v`; exact. |
| No quasicategory or simultaneous-filling conclusion | The conclusion has no `Quasicategory Sα` binder and ends with the one filler; exact. |

I checked the dependency declarations rather than relying on names: the
simplicial-set/horn/pullback primitives come from
`Sheaf.CategoryTheory.EnhancedDiagramsCones`; `InnerFibration` and
`IsCocartesianEdge` come from `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`
and its reexport; and the categorical-equivalence predicate is exactly the
weak-equivalence characterization in `SSet.exists_joyal_model_structure`.
The unsplit face-conservation node is proof-only and has no recorded Lean
declaration, so no private replacement or extra hypothesis was introduced.

Edge cases checked: `n = 2, i = 1` is admitted; `i = 0` and `i = n` are
excluded by the strict inequalities; `n = 0,1` are excluded by the node's
`n ≥ 2`; empty `E`, empty fibers over `1`, and empty `S` are allowed; no
inhabitedness or quasicategory instance is added; the identity cases for `u`
and `v` are allowed; the zero/empty simplicial-set cases remain covered; and
all objects stay in the input universe while the Joyal tests use the required
`max u v` enlargement.

I repeated the existing-declaration searches with `msearch.py` (LeanSearch,
LeanFinder, and Loogle queries for relative horn completion, categorical
equivalence, and cocartesian extension), `rg` over Mathlib, upstream
`WeilConjectures`, this project's `lean/Sheaf`, and
`dag/lean_names_upstream.json`. They found only ordinary horn fillers,
horn-colimit maps, and unrelated categorical-equivalence infrastructure; no
matching declaration exists. The theorem name is collision-free.

No mismatch was found, so no Lean, node, or dependency record was changed in
this second reading. The module was compiled with the required
`scompile.py` wrapper and produced no errors or warnings.
