## Worker report

Item: `lem-coef-infinity-final-index-colimit`, group Q20, stage 2, 2026-10-16 UTC.

The module `Sheaf.CategoryTheory.FinalIndexColimit` states this node in two
named theorems. Both proofs are `by sorry`; nothing is proved as a theorem.
The two helper definitions have real data and no postponed obligations.
There is no statement correction, new DAG node, or dependency repair.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Infinity categories are simplicial sets with inner horn fillers. | `{J C : SSet.{u}} [Quasicategory J] [Quasicategory C]` uses Mathlib's exact horn-filling class. |
| The standard simplex is the nerve of the finite ordinal. | Mathlib's `Δ[n]` is the representable simplicial set of monotone maps of finite ordinals, canonically the nerve of `[n]`. |
| A final object `t` of `J`. | `(t : J _⦋0⦌) (ht : IsTerminal J t)`; the dependency's `IsTerminal` unfolds to `∀ j, IsContractible (mappingSpace J j t)`. The full right-pinched mapping space is used. |
| A functor `p : J → C`. | `(p : J ⟶ C)`, an actual simplicial map. No ordinary-category replacement or edge-inverting assumption occurs. |
| `p` has a cocone with vertex exactly `p(t)`. | `∃ c : (coconeCategory p) _⦋0⦌, c.1.1 = p.app _ t ∧ ...`. The apex is the first coordinate in the dependency's actual simplicial pullback. |
| The cocone is a colimit in the coherent mapping-space sense. | `IsColimiting p c` is the dependency's initial-object predicate on the coherent comma category. It quantifies over every cocone and asks that the entire mapping space from `c` to it be weakly contractible. This is the standard equivalent universal-property formulation: composition from `Map(apex,T)` to coherent transformations from `p` to the constant diagram at `T` is an equivalence. Fibers over such transformations are precisely these contractible comma mapping spaces; this uses all simplices, not just a homotopy category. |
| The component at `t` can be the identity of `p(t)`. | The final equality in `exists_colimiting_cocone_of_final` evaluates the actual transformation on `(J.σ 0 t, id_[1])` and requires equality with `C.σ 0 (p.app _ t)`, the degenerate identity edge. There is no arbitrary automorphism or merely equivalent edge in its place. |
| For every `n ≥ 0` and every simplex-shaped diagram. | `exists_colimiting_simplex_final_cocone` has `(n : ℕ) (p : Δ[n] ⟶ C)` and only `[Quasicategory C]`. It requires no extra instance/hypothesis on the simplex. |
| Apex `p(n)` at the last vertex. | `c.1.1 = p.app _ (stdSimplex.obj₀Equiv.symm (Fin.last n))`. |
| The specified cocone, not an arbitrary cocone with that apex. | `coconeHomotopy p c = simplexFinalPrism n ≫ stdSimplex.σ (Fin.last n) ≫ p` is equality of the entire coherent transformation. |
| The order map fixes `0,...,n` and sends `n+1` to `n`. | `stdSimplex.σ (Fin.last n)` is exactly the simplicial map of this order map. `simplexFinalPrism` maps `(i,0)` to the original vertex `i` in the right cone and `(i,1)` to its new last vertex. Thus the equality is precisely the transformation induced by the node's cone map `Δ[n+1] → Δ[n] → C`. |

The `coconeHomotopy` helper converts the existing comma vertex's path datum
via `unitHomEquiv`, `Functor.natTransEquiv`, and `MonoidalClosed.uncurry`.
It extracts the actual transformation and introduces no alternate cone notion.
`simplexFinalPrism` gives the canonical map `Δ[n] × Δ[1] → Δ[n+1]` degreewise:
for a pair of ordinal maps `(a,b)`, its value at `i` is `(a i).castSucc` if
`b i = 0`, and the new final vertex otherwise. Monotonicity and naturality are
construction obligations discharged inside the definition, with no `sorry`.
These helpers belong to the cocone normalization of this node, and all four
declarations are listed in `lean.declarations`.

### Dependencies and source readings

Read the statements and complete recorded declarations/docstrings of both
statement dependencies. `def-weil-pbc-simplicial-set` is a Mathlib leaf; its
`mathlib_match` supplies `SSet`, `SSet.degenerate`, `SSet.nonDegenerate`,
`SSet.Subcomplex`, and `SSet.Finite` in the Mathlib simplicial-set modules.
Only `SSet` itself is needed in the present signatures. The standard simplex,
horns, simplicial maps, and degeneracies use Mathlib's existing API.

The other dependency is imported publicly as
`Sheaf.CategoryTheory.EnhancedDiagramsCones`. Its record became available while
this worker was reading the dependency. The complete local source and the source
returned by `scompile.py --source Sheaf.CategoryTheory.EnhancedDiagramsCones`
were checked. The declarations used are:

- `SSet.Enhanced.coconeCategory`: the actual degreewise simplicial comma construction;
- `SSet.Enhanced.IsTerminal`: contractibility of all incoming right-pinched mapping spaces;
- `SSet.Enhanced.IsColimiting`: initiality in that coherent cocone category;
- transitively, `SSet.Enhanced.mappingSpace`, `IsContractible`,
  `IsWeakHomotopyEquivalence`, `comma`, `commaSubcomplex`, `constantDiagrams`,
  `evaluation`, and `diagramVertex`.

No definition from that dependency is restated. Its `IsColimiting` gives the
same coherent colimit notion used by the item; no interface repair is needed.
The proof dependencies `lem-coef-infinity-terminal-anodyne` and
`lem-coef-infinity-anodyne-cocones` have no Lean records yet. Their future
proof imports are consequently absent, as allowed by the stage-2 import rule;
their exact uses remain in the theorem docstrings.

Read Kerodon [03LQ](https://kerodon.net/tag/03LQ),
[02XU](https://kerodon.net/tag/02XU), and [02XY](https://kerodon.net/tag/02XY).
The first identifies final objects with right cofinal vertex inclusions, the
second supplies the (dual) cofinal change of indexing objects, and the third
makes a cone with an equivalence at the final vertex colimiting. Also read the
current blueprint's `prop-coef-integral-exceptional-adjoint.md` and its proof
under `main-20261015/blueprint/sec-six-functors/sk-thm-sf-package`: this node is
an inherited foundational input for the finite-shape/stable-enhancement route
to the derived coefficient adjunction, not a replacement for the unit theorem.

### Edge cases and statement checks

- `n = 0` is included literally. The last degeneracy is `σ₀ : Δ[1] → Δ[0]`;
  after `p`, the specified cone is the identity edge on its sole vertex.
- For every `n`, the prism followed by `σₙ` is identity on the zero end,
  constant at `n` on the one end, and constant at `n` along `{n} × Δ[1]`.
  Hence it has the stated endpoints and normalized last component.
- An empty `J` cannot supply `t`; the theorem adds no nonemptiness premise.
  An empty `C` cannot receive `p` from a `J` with the supplied vertex. These
  vacuous cases do not produce a false existence assertion.
- If `J` is a point or `C` is a point, the cocone is the identity as expected.
  The first theorem does not require a finite shape or any colimits elsewhere.
- Universes are explicitly declared, and `autoImplicit` is false. A common
  arbitrary simplicial universe matches the published dependency and its size
  convention. No independent small test universe can make a mapping-space
  hypothesis vacuous. No ordinary-category hypothesis is imposed.
- Both `sorry`s match this one node's two conclusion clauses. Their docstrings
  include the full five-step proof plan, with the anodyne and mapping-space
  dependencies named. No statement is disputed and no node fault was found.

### Searches for an existing statement

All searches were performed before choosing the new declarations.

- `msearch.py leanfinder`, query: `A coherent diagram indexed by a quasicategory
  with a final object has colimit its value at that object`. Eight hits, headed
  by `CategoryTheory.Limits.colimitOfDiagramTerminal`; the other hits concern
  ordinary final functors, ordinary colimit presentations, or colimits in SSet.
  Read `Mathlib/CategoryTheory/Limits/Shapes/IsTerminal.lean`, including the
  complete `coconeOfDiagramTerminal` and `colimitOfDiagramTerminal` signatures
  and docstrings. They concern ordinary functors, not arbitrary quasicategories.
- `msearch.py loogle`, query: `"Quasicategory", "colimit"`: zero hits.
- `msearch.py leansearch`, query: `A diagram on a quasicategory with a final
  vertex has a normalized colimiting cocone`: eight hits on ordinary colimits;
  none states the coherent assertion or the simplex normalization.
- `msearch.py grep`, query: `colimit|cocone|terminal|final`, subdirectory
  `AlgebraicTopology/Quasicategory`: eight hits, all about terminal simplicial
  sets and inner fibrations, not terminal vertices and coherent colimits.
- `rg` in the upstream `WeilConjectures` tree for the item id and the final
  object/coherent colimit terms: no exact statement. The matching upstream
  uses of ordinary terminal-diagram colimits are ordinary-category instances.
- `rg` in `lean/Sheaf` for the item id, `IsColimiting`, and final-colimit terms:
  only the newly published dependency supplies the definitions; no theorem
  states this item. The item id has no upstream declaration binding in
  `dag/lean_names_upstream.json`.
- Duplicate-name check by `rg` across Mathlib, upstream `WeilConjectures`,
  `lean/Sheaf`, and the upstream-name index for `coconeHomotopy`,
  `simplexFinalPrism`, `exists_colimiting_cocone_of_final`, and
  `exists_colimiting_simplex_final_cocone`: no existing declaration.
  A separate `msearch.py grep` on those names also returned zero hits.

### Validation

Used only `scompile.py Q20 lem-coef-infinity-final-index-colimit` for Lean
compilation. The final module passed both the sandbox and library-path checks
cleanly (1.7 and 1.8 seconds respectively). All definitions have real data,
all variables/universes are bound, and every line is at most 100 characters.
The node copy differs only in its `lean` field, whose main signature is copied
verbatim from the file. The delivery dry run is the final worker check; the
independent second reader will add their own reading and deliver.

## Second reading by Q20

I reread the node statement, its Kerodon source places (03LQ, 02XU, and 02XY),
the complete `EnhancedDiagramsCones` dependency, and the module together. The
object and hypothesis list is as follows, with the corresponding Lean rendering
and verdict:

1. An infinity category is a simplicial set with inner horn fillers. Lean uses
   `{J C : SSet.{u}} [Quasicategory J] [Quasicategory C]`; this is the recorded
   Mathlib quasicategory structure and has no extra assumption.
2. The standard simplex is the nerve of a finite ordinal. Lean uses `Δ[n]`,
   `stdSimplex.objEquiv`, `obj₀Equiv`, and the existing `stdSimplex.σ`; these are
   the dependency's standard simplex and order-map declarations.
3. A final vertex `t` of `J` means contractible incoming mapping spaces. Lean
   uses `(t : J _⦋0⦌) (ht : IsTerminal J t)`; the dependency definition expands
   exactly to `∀ j, IsContractible (mappingSpace J j t)`.
4. A diagram `p : J → C` is rendered by `(p : J ⟶ C)`, an actual simplicial
   map. No ordinary-category, finiteness, or edge-inverting hypothesis is added.
5. The first conclusion introduces a cocone `c : (coconeCategory p) _⦋0⦌`,
   requires apex equality `c.1.1 = p.app _ t`, requires
   `IsColimiting p c`, and requires the component at `t` to be the degenerate
   identity edge. The final equality evaluates
   `coconeHomotopy p c` on `(J.σ 0 t, 𝟙 ⦋1⦌)` and equals
   `C.σ 0 (p.app _ t)`, so it specifies the identity exactly.
6. The simplex clause quantifies over every `n : ℕ` and every
   `p : Δ[n] ⟶ C`, with only `[Quasicategory C]`; it introduces no hidden
   assumption on `n` or `C`.
7. Its apex is exactly the final vertex, rendered as
   `p.app _ (stdSimplex.obj₀Equiv.symm (Fin.last n))`.
8. The specified cocone is rendered by the full equality
   `coconeHomotopy p c = simplexFinalPrism n ≫ stdSimplex.σ (Fin.last n) ≫ p`.
   `simplexFinalPrism` is the canonical prism into `Δ[n+1]`, and
   `stdSimplex.σ (Fin.last n)` is the order map fixing `0,...,n` and sending
   `n+1` to `n`. Thus the entire coherent transformation, rather than only its
   apex, is fixed.

The dependency declarations were checked directly: `coconeCategory` uses the
reverse endpoint conditions for a cocone, `IsTerminal` uses the full mapping
space, and `IsColimiting` is `IsInitial (coconeCategory p)`. No dependency is
restated or specialized. The two helper definitions have real data; neither is
a hollow definition. All four declarations carry the source and blueprint
docstrings, and both postponed theorem proofs are exactly the two conclusions
of this node with their step-by-step proof plans.

Edge cases are covered. `n = 0` gives `σ (Fin.last 0) : Δ[1] → Δ[0]` and the
constant identity edge. A point-shaped `J` or `C` specializes to the identity
cocone. An empty `J` cannot furnish `t`, and an empty `C` cannot receive a map
with the supplied vertex, so no vacuous false existence is introduced. The
explicit universe `u` is shared by all simplicial sets and the index type is
not independently enlarged. Characteristic, zero-object, and scheme hypotheses
are irrelevant to this simplicial assertion and are correctly absent.

I repeated the existing-definition searches with LeanFinder, Loogle, LeanSearch,
and `rg` over Mathlib, the upstream `WeilConjectures` tree, and `lean/Sheaf` for
the theorem names, coherent colimit/final-object notions, and the two helpers.
Only ordinary-category colimit results and unrelated quasicategory horn APIs
were found; no exact declaration exists. No mismatch was found, so no Lean or
node statement was changed in this second reading.

Second-reader search details: LeanFinder query `Evaluation at a terminal vertex
is a colimit in an infinity category` returned eight ordinary-category hits,
headed by `CategoryTheory.Limits.colimitOfDiagramTerminal`. Loogle query
`"Quasicategory", "IsColimit"` returned zero hits. LeanSearch query
`A final vertex inclusion computes homotopy coherent colimits` returned eight
ordinary final-functor hits. Direct `rg` over all three source trees found no
existing declaration with any delivered name. I also checked the dependency
node records and the absence of an item repair note. No new node, dependency
module, or statement correction is present, so H12/H13 and the citer audit do
not require additional records.

The independent `scompile.py` run passed sandbox and library-path compilation
in 2.5 and 3.6 seconds, with no warnings. A mechanical comparison confirmed
`lean.statement` equals the main signature verbatim, all variables and universes
are explicitly bound, and every Lean line has at most 100 characters. The
second reading changed only this report by adding the independent audit.
