## Worker report

The module `Sheaf.CategoryTheory.Triangulated.ProZeroMiddle` states
`CategoryTheory.Pretriangulated.proZero_middle_of_distinguished_tower`, with the whole
proof `sorry`. No definitions, dependency modules, or new nodes are needed; the natural
statement and dependencies are unchanged.

Hypothesis and conclusion correspondence:

- The triangulated category is `{D : Type u} [Category.{v} D]`, with `[Preadditive D]`,
  `[HasZeroObject D]`, `[HasShift D ℤ]`, additive shifts, `[Pretriangulated D]`, and
  `[IsTriangulated D]`. These are the structures recorded by
  `def-weil-triangulated-category`, including TR4. Independent object and morphism
  universes are explicit.
- The triangles and every transition forming an inverse system are
  `(T : ℕᵒᵖ ⥤ Triangle D)`. Each object has all three objects and arrows, including
  the connecting arrow into the shifted first object. Every mapped morphism is a
  `TriangleMorphism`, with its three components and all three commutative squares.
  Functoriality imposes identity and composition laws. This is precisely the functor
  encoding of `def-weil-inverse-system`, reindexed by `n ↦ n + 1` from natural indices
  to the paper's positive indices; there is no omitted initial level.
- Distinguishedness at every level is
  `hT : ∀ n : ℕ, T.obj (Opposite.op n) ∈ distTriang D`.
- The simultaneous eventual zero maps on the first and third terms are `hAC`:
  `∀ n, ∃ (k : ℕ) (hnk : n ≤ k), ...hom₁ = 0 ∧ ...hom₃ = 0`, both evaluated
  on the same `T.map (homOfLE hnk).op`. The opposite of the order arrow sends
  level `k` to level `n`, as required.
- The conclusion uses the same quantifiers and arrow with `.hom₂ = 0`, hence says
  exactly that each middle level receives a zero transition from some later level.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`:
  `CategoryTheory.Pretriangulated`, `distTriang`, and
  `CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂` / `yoneda_exact₃`.
  This is the Mathlib match of `def-weil-triangulated-category` and the proof leaf
  `lem-weil-pbc-hom-out-of-triangle-exact`. The module is publicly imported through
  `Mathlib.CategoryTheory.Triangulated.Triangulated`; no redundant separate proof
  import is needed because the proof leaf's module is already publicly available.
- `Mathlib.CategoryTheory.Triangulated.Triangulated`:
  `CategoryTheory.IsTriangulated`, supplying the node's full triangulated assumption.
- `Mathlib.CategoryTheory.Triangulated.Basic`: `Triangle`, `TriangleMorphism`, and
  their category instance, read in full at their definitions and imported transitively.
- `Mathlib.CategoryTheory.Functor.OfSequence`:
  `CategoryTheory.Functor.ofOpSequence` and `CategoryTheory.NatTrans.ofOpSequence`.
  This dependency explicitly identifies towers with functors `ℕᵒᵖ ⥤ C`; the
  statement uses that recorded equivalent encoding directly rather than imposing
  that a general functor be presented by its sequence constructor.

Source checked: local Stacks `derived.tex`, label
`lemma-essentially-constant-2-out-of-3` (Tag 0G3A). The item is explicitly the
zero-valued specialization, not the full essentially constant theorem. Its docstring
carries all four steps of the DAG's direct factorization proof, including the named
Hom-exactness input and the two successive choices of later index.

Edge cases checked: the zero category and all-zero triangles are allowed; no nonzero
object or strict inequality is imposed. The witness may equal the original level,
correctly forcing the corresponding identity to be zero. Two different later choices
are needed in the argument; the statement does not falsely require the middle map
to vanish at the first witness. Constant nonzero outer towers fail the hypothesis,
so the implication asserts no vanishing there. All positive indices are covered by
the order isomorphism `ℕ ≃ ℤ_{≥1}`; no empty indexing case exists for this fixed tower.
There is no size restriction on `D` beyond independent explicit universes.

Searches (2026-10-15):

- `msearch.py leanfinder`, query "inverse system distinguished triangles pro-zero
  outer terms imply middle term pro-zero": eight hits, including
  `Triangle.yoneda_exact₂`, `yoneda_exact₃`, their covariant variants and t-structure
  vanishing results. None states the tower conclusion.
- `msearch.py loogle`, query `CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂`:
  one hit, the exactness input, not the tower statement.
- `msearch.py leansearch`, query "inverse system of distinguished triangles with
  pro-zero first and third terms has pro-zero middle terms": service unavailable,
  Internal Server Error. Other search methods completed.
- `msearch.py grep`, query `essentially.?constant|pro.?zero` in `CategoryTheory`:
  seven unrelated product/coproduct-zero hits, no match.
- Direct `rg` for essentially constant/pro-zero terminology in the upstream
  `WeilConjectures` and project `lean/Sheaf`: existing essentially constant
  ind/pro-diagram material and abelian-group towers, Tor and tensor results, but no
  inverse-triangle pro-zero theorem. Upstream blueprint-id grep returned no match.
- Direct `rg` for the proposed name and pro-zero triangle/middle terminology across
  Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no match.

No statement dispute or node fault found. All files are confined to the designated
sandbox; compilation uses the server `scompile.py` only.

## Second reading by NY

Read independently against the node copy, Stacks `derived.tex`,
`lemma-essentially-constant-2-out-of-3` (0G3A), and
`lemma-representable-homological` (0149). The source assumes a triangulated
category and an inverse system of distinguished triangles, with no finiteness,
linearity, or size hypothesis. This node explicitly takes only its zero-valued
specialization; it does not claim the full essentially constant conclusion.

Object, hypothesis, and conclusion checklist (all pass):

- Triangulated category D: `{D : Type u} [Category.{v} D]`,
  `[HasZeroObject D] [HasShift D ℤ] [Preadditive D]`, additive shifts,
  `[Pretriangulated D] [IsTriangulated D]`. Read `Pretriangulated.lean`
  lines 43–87 and `Triangulated.lean` lines 300–314 against
  `def-weil-triangulated-category`: these give exactly TR1–TR4, with
  binary biproducts supplied by the pretriangulated structure. No extra
  completeness, idempotent completeness, or smallness instance is required.
- Objects A_n, B_n, C_n and all triangle arrows: `(T : ℕᵒᵖ ⥤ Triangle D)`.
  Read `Basic.lean` lines 44–57: `obj₁`, `obj₂`, `obj₃`, `mor₁`, `mor₂`,
  `mor₃`, including `mor₃ : obj₃ ⟶ obj₁⟦1⟧`. Thus the connecting arrow
  is present and has the correct shift.
- Positive indices: Lean index n denotes paper index n+1. This order
  isomorphism covers every positive index, including the first one.
  Read `def-weil-inverse-system` and `Functor.OfSequence.lean` lines
  149–191: its recorded equivalent encoding is precisely a functor from
  `ℕᵒᵖ`; no private definition or replacement constructor is used.
- Distinguishedness at every level: `hT : ∀ n : ℕ,
  T.obj (Opposite.op n) ∈ distTriang D` is exactly that hypothesis.
- Every transition is a triangle morphism and transitions compose:
  `T.map (homOfLE hnk).op` goes from k to n for `hnk : n ≤ k`.
  Read `Basic.lean` lines 104–150: the category's morphisms have
  `hom₁`, `hom₂`, `hom₃` and all three squares `comm₁`, `comm₂`,
  `comm₃`; composition is componentwise. Functor laws impose identity
  and composition for every transition, not merely consecutive maps.
- Simultaneous outer vanishing: `hAC : ∀ n : ℕ, ∃ (k : ℕ)
  (hnk : n ≤ k), ...hom₁ = 0 ∧ ...hom₃ = 0`. Both clauses use the
  same k and the same triangle morphism; neither hypothesis is omitted.
- Middle vanishing conclusion: `∀ n : ℕ, ∃ (k : ℕ) (hnk : n ≤ k),
  (T.map (homOfLE hnk).op).hom₂ = 0`. Quantifiers and non-strict
  inequality are identical to the node. It does not require the middle
  map to vanish already at the witness supplied by hAC.

Proof and imports: read the proof dependency
`lem-weil-pbc-hom-out-of-triangle-exact` and its Mathlib match
`Triangle.yoneda_exact₂` at `Pretriangulated.lean:248`: precisely a
map from the middle object killed by the first arrow factors through
`mor₂`. The module's docstring correctly follows all four node steps:
kill the first transition, factor the middle map, kill a later third
transition, and compose. This proof dependency is already publicly
imported through `Mathlib.CategoryTheory.Triangulated.Triangulated`.
There are no sibling modules, new definition nodes, dependency repairs,
or statement corrections to review. The sole theorem retains its full
`sorry` proof; no hollow definitions or file-local conventions occur.

Edge cases: zero objects and all-zero towers are allowed; k=n is
allowed and then the relevant identity must be zero. A constant nonzero
outer tower fails hAC, as it should. There is no empty index set: the
node fixes the nonempty positive integers. An empty category cannot be
triangulated because a zero object is required, in both formulations.
The Lean n=0 case is the paper's n=1, not an added missing level.
No schemes, coefficient characteristic, or numerical parameter occur.
The independent universes u and v cover arbitrary object and Hom sizes;
no limit universe or essentially-small hypothesis occurs.

Independent searches on 2026-10-15:

- `msearch.py leanfinder`: "tower of exact triangles eventually zero
  transition maps on outer objects implies eventually zero on middle
  objects" returned eight hits: homology-sequence exactness, t-structure
  vanishing, and `Triangle.yoneda_exact₃` / `coyoneda_exact₃`.
  None states the inverse-tower result.
- `msearch.py loogle`: `CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂`
  returned just the factorization input, whose actual signature was read.
- `msearch.py grep`: `proZero_middle|pro_zero.*triangle|triangle.*pro_zero|essentially_zero`
  returned zero hits.
- Direct `rg` with `pro.?zero|essentially.?zero|essentially.?constant|distinguished.*tower|tower.*triangle`
  across pinned Mathlib CategoryTheory, upstream `WeilConjectures`, and
  project `lean/Sheaf` found general essentially constant diagrams,
  abelian-group towers, homotopy-limit triangles, and Tor/tensor results.
  None is this statement. Direct full-name and blueprint-id searches in
  the project, upstream, and `dag/lean_names_upstream.json` found no match.

No mathematical or textual mismatch found. The Lean module and node
record are unchanged. The recorded `lean.statement` was compared
verbatim with the module signature, and all variables/universes are bound.
Compilation and delivery checks use only the prescribed server scripts.
