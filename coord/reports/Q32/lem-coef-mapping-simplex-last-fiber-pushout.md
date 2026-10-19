## Worker report

This repairs the delivery returned at immutable head `506281d2f886` for
H3/H6 (indexing, unspecified maps, missing base compatibility and naturality)
and H8 (missing proof-step summary). The retained packet was first inspected and
run through `deliver2.py --no-push`: it mechanically passed at `7848804d4a`, but
self-check confirmed the substantive return. The repair therefore changes the
actual statement and its constructions, rather than re-pushing that packet.
The saved node and the current shared node agreed in every field except `lean`.
The current node is retained, with `lean` replaced and the already landed
`def-coef-mapping-simplex-functor` added to `stmt_deps` as authorized by §5.

The module is `Sheaf.AlgebraicTopology.MappingSimplexLastFiberPushout`, with main
theorem `SSet.Enhanced.mappingSimplex_last_fiber_pushout`. All definitions have
actual data; all theorem proofs are `sorry`. There are no new independent notions
or new nodes: the extra declarations are the canonical maps and their necessary
simpliciality and square-compatibility obligations expressly authorized as helpers
in the owning node's module. Their source/blueprint docstrings and the node's
`lean.declarations` list cover every declaration.

Here is the clause-by-clause correspondence. Write `N` for the dimension called
`n` in the node, and `n` for the Lean binder.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Arbitrary positive dimension `N > 0` | `n : ℕ`, with `N = n + 1`. Every positive natural has this form, and there is **no** extra `0 < n` binder. The former packet's erroneous extra restriction is removed. |
| Any chain `A_0 ← … ← A_N` of small simplicial sets | `A : SimplexChain.{u} (n + 1)`, the existing opposite finite-ordinal functor into `SSet.{u}`. No assumption on its maps or objects. |
| Composites `t_(j,i)` | `A.map (homOfLE h).op`, with the transition's component `.app r`. |
| Mapping simplex and its operators exactly as in the node | Existing `mappingSimplex`, `MappingSimplexDegree`, and `mappingSimplexOperator`; no replacement definition. Its simplices are dependent pairs with the specified final fibre. |
| `M_-` deletes only the last fibre | `mappingSimplexTruncation A`, by precomposition with `mappingSimplexCastSuccFunctor n`. This has `n + 1` vertices and mapping-simplex dimension `n = N - 1`. |
| `T = Δ^{0,…,N-1} ⊆ Δ^N` | The standard `Δ[n]` with Mathlib's `SSet.stdSimplex.δ (Fin.last (n + 1)) : Δ[n] ⟶ Δ[n+1]`. Its vertex map is `Fin.castSucc`, since `Fin.succAbove_last` identifies the last coface with that inclusion. This is the canonical parametrization of the node's face. |
| `g(a,α) = (α,t_(N,α(r)) a)` | `mappingSimplexLastAttachApp` and `mappingSimplexLastAttach`. The fibre transition ends at the castSucc of the last value of `α`, exactly the same vertex of the full chain. |
| `h(a,α) = (α,t_(N,α(r)) a)` | `mappingSimplexLastCylinderApp` and `mappingSimplexLastCylinder`, using the full `Δ[n+1]`. |
| Canonical inclusion `j : M_- ↪ M(A)` | `mappingSimplexInitialInclusionApp` and `mappingSimplexInitialInclusion`, sending `(α,a)` to `(castSucc ∘ α,a)`. This function is degreewise injective, without requiring a chain transition to be injective. |
| Inclusion `k : A_N × T → A_N × Δ^N` | `mappingSimplexLastFace A := 𝟙 _ ⊗ₘ SSet.stdSimplex.δ (Fin.last (n+1))`. |
| All three prescribed maps are simplicial | `mappingSimplexLastAttachment_naturality`, used only for naturality proof fields of the three natural transformations. Their data are the formulas just given. |
| The attaching square commutes | First clause of `mappingSimplexLastAttachment_comm`: `g ≫ j = k ≫ h`. |
| Ordinary small pushout | `mappingSimplexLastPushout A := pushout g k`, using the recorded colimit notion via Mathlib's pushout API. |
| The induced **canonical** isomorphism to `M(A)` | `mappingSimplexLastPushoutComparison A := pushout.desc j h ...`; the main theorem asserts `IsIso` of precisely this map. Its restrictions to the two legs are `j` and `h` by `pushout.inl_desc` and `pushout.inr_desc`. `IsIso` supplies the inverse of this specified map, rather than an unrelated existential equivalence. |
| It respects maps to `Δ^N` | Main theorem's second conjunct: `mappingSimplexLastPushoutComparison A ≫ mappingSimplexProjection A = mappingSimplexLastPushoutProjection A`. The latter projection is explicitly `pushout.desc` of `mappingSimplexProjection (mappingSimplexTruncation A) ≫ δ_last` and `CartesianMonoidalCategory.snd _ _`. Their agreement is the second clause of `mappingSimplexLastAttachment_comm`. Thus both specified base maps, and not a chosen arbitrary base map, occur. |
| Natural for every map of chains commuting with transitions | Main theorem's third conjunct quantifies all `B` and all `f : A ⟶ B`. The map on targets is the recorded `mappingSimplexChainMap f`. `mappingSimplexLastPushoutMap f` is the actual `pushout.map` from the truncated `mappingSimplexChainMap` and `f.app (op (Fin.last (n+1))) ⊗ₘ 𝟙 Δ[n+1]`, using the same final-fibre map on the intersection. The equation is `pushoutMap f ≫ comparison B = comparison A ≫ mappingSimplexChainMap f`. |
| No injectivity or fibrancy hypotheses | None appear in the theorem or in any construction. No nonemptiness assumptions appear either. |

The usual universal property is already part of Mathlib's chosen pushout from
`def-weil-pbc-category-colimit`. Invertibility of its canonical comparison gives
exactly that universal property with vertex `M(A)`, rather than the previous
packet's redundant universal property of an otherwise unspecified chosen pushout.
The over-base equation also identifies the canonical map as an isomorphism in
the slice over the standard simplex: its inverse respects the base by cancellation.

Dependency declarations read and used:

- `def-cbc-enhanced-diagrams-cones`: module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, reexported by the existing
  mapping-simplex modules. Its small simplicial sets, standard simplices and
  degreewise products are Mathlib's `SSet`, `SSet.stdSimplex`, and cartesian
  tensor. The node's recorded `coneCategory` is not the construction needed here;
  its underlying recorded simplicial primitives are used directly, not copied.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit`,
  `Cocone`, `IsColimit`, `colimit.desc` from
  `Mathlib.CategoryTheory.Limits.HasLimits`. The pushout specializations used are
  `pushout`, `pushout.desc` and `pushout.map` from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `def-coef-mapping-simplex-functor`: recorded
  `SSet.Enhanced.mappingSimplexChainMap` in
  `Sheaf.AlgebraicTopology.MappingSimplexConeFibers`, directly imported.
  Its source/target constructions `SimplexChain`, `MappingSimplexDegree`,
  `mappingSimplexOperator`, `mappingSimplex`, `mappingSimplexProjection` are
  in `Sheaf.CategoryTheory.CartesianMappingSimplexPresentation`, reexported there.
  Full signatures and source docstrings were inspected.

Four theorem holes remain, all matching claims of this same node:
`mappingSimplexLastAttachment_naturality` (the prescribed `g,h,j` are simplicial),
`mappingSimplexLastAttachment_comm` (the attaching and base squares),
`mappingSimplexLastAttachment_chainMap` (the induced span squares for ladders),
and `mappingSimplex_last_fiber_pushout` (canonical isomorphism, base compatibility,
and naturality). These are the node's Steps 2, 6 and main conclusion, not new
unrelated lemmas or stronger assumptions. Every one has its source and complete
natural-language proof plan in its docstring. The main theorem docstring now
summarizes all six DAG proof steps, including operators that lose the final
vertex, uniqueness, base compatibility and ladder naturality.

Edge cases checked against the actual definitions:

- `n = 0`, i.e. node dimension `N = 1`: `A_0 ← A_1`, shorter simplex `A_0`,
  attaching face `Δ[0]`, and cylinder `A_1 × Δ[1]`. This was excluded before.
- Arbitrary node dimensions `N ≥ 1` are all represented by `n = N - 1`.
  The node's excluded dimension `N = 0` is not accidentally introduced.
- Empty final fibre: the two products are empty, so the pushout is the initial
  mapping simplex. All fibres empty: the mapping simplex and pushout are empty.
- A noninjective transition: only the last-face product map is an inclusion;
  `g` can identify simplices and is still the formula using that transition.
- A face losing the last vertex: the operator switches from the cylinder part
  to the shorter-simplex part, precisely the compatibility case in proof Step 4.
- Identity ladders and arbitrary commuting ladders are both included in `f : A ⟶ B`;
  there is no equivalence, monomorphism or fibrancy restriction on `f`.
- All inputs and the degreewise pushout lie in the same arbitrary universe `u`;
  the finite ordinal indexing creates no universe constraint.

Searches retained from the original packet and repeated for the repair:

- `msearch.py leanfinder`: “The mapping simplex of a chain of simplicial sets is
  the canonical pushout attaching the last fibre times the standard simplex
  along its initial face, naturally over the standard simplex”. Eight hits:
  pointed-simplex structures, `stdSimplex.objMk`, augmented standard simplices,
  cylinder endpoint inclusions and `SSet.S.map`; none states this result.
- `msearch.py loogle`: `"SSet", "pushout"`. Twelve hits: ordinary horn pushouts,
  subcomplex unions and relative cell complexes. The subcomplex pushout cannot
  replace `g`, which is not required to be a mono. Read the actual pushout API
  and the standard-simplex and monoidal-product signatures used above.
- `msearch.py grep`: `mappingSimplex|mapping.?[Ss]implex` under Mathlib
  `AlgebraicTopology/`: zero hits.
- Repository `rg` for `mappingSimplex`, `MappingSimplex`, `mapping.?[Ss]implex`,
  the item id and all new declaration names in the authorized upstream and
  shared `lean/Sheaf` trees. No upstream match; shared declarations give the
  existing mapping simplex and chain map, which are imported. No exact theorem
  or existing truncation/attachment/comparison declarations were found.
  The pre-existing initial coface is taken directly from Mathlib, not duplicated.

The final module compiled cleanly in both the scratch and library-module checks
through the required `scompile.py` wrapper (1.9 s and 2.2 s reported). All
variables and the universe are explicitly bound, with `autoImplicit false`.
There is no mathematical statement correction, dispute, new node, or dependency
interface repair. The node's natural-language statement and six-step proof stay
unchanged. Its missing formalization clauses are repaired in Lean.

## Worker self-check

I performed a separate self-check with both the current DAG node and the repaired
module open; no other agent was started, as the dispatcher brief prohibits it.
This is not claimed as an independent worker's review. The initial saved packet
was mechanically green but failed the substantive check. The mismatches and their
repairs are concrete:

1. The old `(n : ℕ) (hn : 0 < n) (A : SimplexChain (n+1))` missed chains of
   dimension one. The repaired binder has no `hn`; the dimension is explicitly
   `N = n+1`, and testing `n = 0` now gives exactly the node's first allowed case.
2. Old arbitrary `∃ g,h,j` have been replaced by concrete natural transformations
   with the exact three degreewise formulas in the node. The truncation and
   transition endpoints were reread to check that no fibre is shifted or dropped.
3. The comparison is exactly `pushout.desc j h` of those maps and the canonical
   attaching face, and `IsIso` is asserted for that exact morphism.
4. A separately constructed pushout projection and an explicit equality after
   comparison restore the over-`Δ^N` clause.
5. The actual `pushout.map` induced by every `f : A ⟶ B` and the existing
   `mappingSimplexChainMap f` occur in an explicit naturality equation.
6. The theorem docstring now contains all six proof steps and their dependency
   references. The well-definedness helper docstrings explain precisely their
   portions of Steps 2 and 6. Every theorem proof remains `sorry`.

I also checked that the main statement in the JSON is the verbatim multiline
signature from the file and that the original node changes only in `lean` and
addition of the already landed mapping-simplex definition node to `stmt_deps`.

## Second reading by Q32

Independent maintainer second reading, 2026-10-17, of immutable delivery
08e6327cd50c23278611ff3c776e523d2fab116b. This reader did not write or previously
review this delivery. The preceding worker self-check is retained as history.

I read the item and all three statement dependencies in the immutable snapshot,
the delivered module and every declaration it lists, and the actual imported
mapping-simplex declarations in the read-only Q32 clone. I also read HTT §3.2.2,
printed pp. 179–180 and 182–183, directly at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf (PDF pages 196–197, 199–200,
zero based). The explicit unmarked pushout is in Proposition 3.2.2.10's proof.
The cofibration replacement in Lemma 3.2.2.9 concerns its later homotopical
argument; it is unnecessary for this degreewise pushout identity.

Clause checks, independently against the actual Lean:

1. Dimension: the node's N > 0 is exactly N = n+1 with unrestricted n : ℕ.
   SimplexChain (n+1) is a functor (Fin (n+2))ᵒᵖ ⥤ SSet.{u}; all chain
   transitions are present, with no injectivity, fibrancy or nonemptiness binder.
2. Mapping simplex: MappingSimplexDegree is the dependent sum over monotone α
   with second coordinate in A_(α(last)). mappingSimplexOperator restricts the
   second coordinate and then applies the transition from α(last) to αθ(last).
   mappingSimplexProjection records α. These existing data are reused exactly.
3. Truncation: mappingSimplexCastSuccFunctor and mappingSimplexTruncation retain
   precisely vertices 0,…,N-1 and their transitions. InitialInclusionApp sends
   (α,a) to (castSucc ∘ α,a), which is injective degreewise.
4. Face and attaching maps: δ (Fin.last (n+1)) is the initial-face inclusion,
   since SimplexCategory.δ uses succAbove and Fin.succAbove_last is castSucc.
   LastFace is its product with the identity. LastAttachApp and LastCylinderApp
   apply precisely A.map of the arrow from the final vertex to the last value
   of α; the former uses castSucc in the full chain. These are the node's g,h.
   LastAttachment_naturality states exactly their required simpliciality.
5. Canonical isomorphism: LastAttachment_comm has g ≫ j = k ≫ h.
   LastPushout is Mathlib's colimit of this span; LastPushoutComparison is its
   pushout.desc j h. IsIso of that specified comparison is exactly the claimed
   canonical isomorphism, rather than an arbitrary isomorphism or arbitrary map.
6. Base compatibility: LastPushoutProjection is pushout.desc of the truncated
   projection followed by δ_last and the cylinder's second projection. Its
   compatibility obligation is the second conjunct of LastAttachment_comm.
   The main theorem's second conjunct equates comparison followed by the
   mapping-simplex projection with this independently prescribed base map.
7. Naturality: every B and every natural transformation f : A ⟶ B is quantified.
   TruncationMap is whiskering; LastAttachment_chainMap supplies the exact span
   squares; LastPushoutMap is pushout.map of these three specified components.
   The last conjunct compares this map with the existing mappingSimplexChainMap.
   Identity ladders, collapsing components and arbitrary commuting ladders occur.

The six proof steps also check mathematically: the initial-labelled part is
stable under operators; transitions make g,h simplicial; the compatible pair
(p,q) defines the piecewise extension; when an operator loses the last vertex,
pg=qk is precisely the missing compatibility; j,h are jointly surjective in
every degree, giving uniqueness; base labels and ladder squares give the final
compatibilities. The main docstring includes all six steps and their dependencies.

Dependency checks: CartesianMappingSimplexPresentation.lean:49–107 supplies the
chain, simplex degree, operator, construction and projection;
MappingSimplexConeFibers.lean supplies the recorded mappingSimplexChainMap with
exact component formula. EnhancedDiagramsCones publicly imports the existing
SSet standard-simplex and cartesian-product primitives. Its coneCategory is not
being substituted for any object here. HasPullback.lean:103–142 defines pushout
as colimit(span) and desc as colimit.desc; :309–313 defines the actual pushout.map.
Thus the colimit dependency is used through its exact pushout specialization.

Edge cases checked: n=0 is the dimension-one mapping cylinder; empty final
fibre leaves the truncated simplex; all fibres empty gives the empty simplicial
set; constant chains give the expected product decomposition; noninjective
transitions only affect g and are allowed. Operators losing the final vertex
are covered by the compatibility case above. Universe u is arbitrary, shared
only for the small simplicial sets; finite indexing requires no additional
size equality. Node dimension zero is correctly outside this item.

Independent searches on 2026-10-17:

- LeanSearch through msearch.py: “Simplicial replacement of a finite inverse chain
  is a pushout attaching its terminal fibre over the opposite face”: eight hits,
  including Subcomplex.BicartSq.isPushout, SimplicialObject and opFunctor; none
  states this result. Read SubcomplexColimits.lean:84–104: its inclusion square
  cannot replace a possibly noninjective attaching g.
- LeanFinder through msearch.py: “Pushout decomposition of the simplicial
  replacement of a finite inverse diagram by adjoining the terminal fibre”:
  eight Čech-conerve hits, none exact. CechNerve.lean:185–220 constructs a
  cosimplicial wide-pushout diagram, not this finite inverse-chain simplex.
- rg for mapping-simplex, simplicial replacement and last-fibre pushout variants
  in upstream WeilConjectures, Mathlib/AlgebraicTopology and Q32 lean/Sheaf found
  the existing chain/simplex data reused here, but no exact theorem or duplicate
  attachment helpers. MappingSimplexInitialHornPushout.lean:107 concerns a marked
  initial horn, not the unmarked initial face. MappingSimplexFinalEdge states a
  mapping-space equivalence, not this result. The worker's Loogle search is also
  retained above. No missing independent prerequisite or dependency repair arose.

Gates: all 18 declarations are listed in lean.declarations and have source and
blueprint docstrings. Four named theorems, including all well-definedness holes,
have exactly sorry proofs; no definition contains sorry data or an internal
sorry proof. The functor's subsingleton law fields are structural terms, not
additional proved theorem declarations. No stronger assumptions, arbitrary
construction, pro-etale substitute, private copy or silent statement correction.
The JSON lean.statement equals the main signature verbatim; all lines meet the
100-character limit, namespace/import conventions hold, and autoImplicit=false
with an explicit universe u leaves no unbound variable.

Reproduced compilation with:
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q32
lem-coef-mapping-simplex-last-fiber-pushout
snapshot/lean/Sheaf/AlgebraicTopology/MappingSimplexLastFiberPushout.lean
(the arguments above form one command). Exit 0, no errors or warnings; sandbox
1.9 s and library-module 2.0 s. The installed wrapper currently dispatches to
the server's private side overlay; this is server confirmation through the
prescribed wrapper, not a direct ssh invocation or a global build. The worker's
recorded 1.9 s / 2.2 s result is reproduced in substance.

Findings and changes: the Lean and node require no change. H11/H1 reporting is
repaired by this independent reading, because the delivered section explicitly
was only a worker self-check. H4 reporting is completed by the actual LeanSearch
query and results above. The complete replacement report preserves Worker report
and renames the old second-reading heading to Worker self-check. No clone,
branch head, immutable snapshot, or live Lean file was modified.
