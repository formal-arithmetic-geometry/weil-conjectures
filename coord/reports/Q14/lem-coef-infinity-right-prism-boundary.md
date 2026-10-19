## Worker report

Item: `lem-coef-infinity-right-prism-boundary`, group Q14, stage 2.

`Sheaf.CategoryTheory.RightPrismBoundary` states
`SSet.exists_right_prism_boundary_filtration`, with its entire proof `sorry`.
It creates no definitions or helper theorems. All variables and the universe `u`
are explicitly bound, and `autoImplicit` is disabled. The module compiles without
errors or warnings using the prescribed `scompile.py` wrapper (both sandbox and
library-module checks passed, approximately two seconds each).

I read the node, its six proof steps, both statement dependencies and their Lean
records, and the full `EnhancedDiagramsCones` module and the relevant Mathlib
signatures and docstrings. I also read Kerodon Lemma the project server (Tag 00TH), assertions
(a), (b), and its proof online at https://kerodon.net/tag/00TH. It agrees with the
node's endpoint, horn orientation, shuffle formula, and recursive unions.
Archival copy WANTED: the node currently cites the online Kerodon page.

Hypothesis and clause correspondence:

- The sole mathematical parameter, an integer `m ≥ 0`, is `m : ℕ` with no
  positivity assumption. `SSet.{u}` permits every small-set universe `u`.
- Simplicial subsets of the degreewise product are
  `(Δ[1] ⊗ Δ[m] : SSet.{u}).Subcomplex`. This is Mathlib's cartesian monoidal
  product, whose simplices and operators are pairs in every degree.
- The finite chain `X₀, …, Xₘ₊₁` is
  `X : Fin (m + 2) → (Δ[1] ⊗ Δ[m]).Subcomplex`, with `hX : Monotone X`.
  Adjacent stages indexed by `q : Fin (m + 1)` are `X q.castSucc` and `X q.succ`.
- The initial-stage equality is the first conjunct. The terminal vertex `{1}`
  is `Subcomplex.ofSimplex (stdSimplex.obj₀Equiv.symm 1)`. Its external product
  with `⊤`, joined with `⊤.prod (boundary m)`, is precisely the stated union.
- The boundary is the existing Mathlib `boundary m`: its simplices are the
  nonsurjective monotone maps. `boundary_eq_iSup` identifies it with the union
  of all faces; `boundary_zero` identifies the zero-dimensional case with `⊥`.
- The final-stage equality is `X (Fin.last (m + 1)) = ⊤`.
- For every `q`, the existential `σ : Δ[m + 1] ⟶ Δ[1] ⊗ Δ[m]` is constrained
  on every vertex `j : Fin (m + 2)`. Applying `stdSimplex.obj₀Equiv` to each
  output coordinate and taking `.val` gives exactly `(0,j)` when `j ≤ q`,
  and `(1,j-1)` otherwise. The formula uses natural-number coordinates to
  avoid dependent casts; it loses no information because Fin values are
  injective. Maps between these nerves of finite posets are determined by
  vertices, so these are the source's specified maps, with no arbitrary choice
  substituted for their construction.
- `X q.succ = X q.castSucc ⊔ Subcomplex.range σ` is the final union clause.
- `a` has source `(horn (m + 1) q.succ).toSSet` and target the preceding stage;
  `b` has source `Δ[m + 1]` and target the next stage. The horn index `q.succ`
  is exactly `q + 1`, including the last, outer horn when `q = m`.
- `IsPushout (horn (m + 1) q.succ).ι a b
  (Subcomplex.homOfLE (hX (Fin.castSucc_le_succ q)))` gives exactly the square
  with top horn inclusion, left `a`, right `b`, and bottom stage inclusion.
  Mathlib's `IsPushout` contains commutativity and the `IsColimit` universal
  property of the associated pushout cocone.
- The last two conjuncts say `b` composed with the next-stage ambient inclusion
  equals `σ`, and `a` composed with the preceding-stage ambient inclusion
  equals the horn inclusion followed by `σ`. Thus both vertical maps are the
  restrictions named in the node; neither map is left unconstrained.

Dependency declarations and interfaces:

- `def-cbc-enhanced-diagrams-cones`: imported through
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`. Its documented simplicial
  primitives are the existing Mathlib `SSet`, `stdSimplex`, `horn`, and the
  degreewise cartesian product from `Monoidal`. The particular recorded
  `SSet.Enhanced.coneCategory` and the other enhanced cone constructions are
  not mathematical objects used in this prism statement. The same underlying
  primitives are used directly, without recreating any notion.
- `def-weil-pbc-category-colimit`: imported through its recorded
  `Mathlib.CategoryTheory.Limits.HasLimits`. The recorded
  `CategoryTheory.Limits.colimit` and `IsColimit` give the ordinary colimit
  interface; the statement uses its pushout specialization
  `CategoryTheory.IsPushout`, imported from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`. I read its
  structure: `CommSq` plus `Nonempty (IsColimit (PushoutCocone.mk ...))`.
- Supporting existing Mathlib declarations read and used:
  `SSet.Subcomplex.ofSimplex`, `.prod`, `.range`, `.ι`, `.homOfLE`,
  `SSet.stdSimplex.obj₀Equiv`, `SSet.boundary`, and `SSet.horn`.

Edge cases checked: `m = 0` has two stages and the single index `q = 0`.
The boundary is empty, the initial stage is `{1}`, the map has vertices
`(0,0)` and `(1,0)`, and `horn 1 1` is `{1}`. For `q = 0` in any dimension,
the horn omits face 1 and face 0 lands in the endpoint; for `q = m`, the horn
index is the final vertex `m + 1` and is allowed. All degenerate simplices
remain in the subcomplexes and the pushout is in the full simplicial-set
category. No nonemptiness or nondegeneracy hypothesis, dimension bound, or
universe equality is imposed.

Searches performed before writing (all via the prescribed search wrapper or
read-only source searches):

- LeanFinder: "The simplicial prism Delta one times Delta m has a filtration
  by pushouts of right horns relative to its boundary and terminal endpoint".
  Eight hits: the three two-dimensional `horn₂*.isPushout` statements,
  Quillen generating classes, `horn.isColimit`, `IsStrictSegal`, and `S1`.
  None states this finite prism filtration.
- Loogle: `"horn", "IsPushout"`. Three hits,
  `SSet.horn₂₀.isPushout`, `horn₂₁.isPushout`, `horn₂₂.isPushout`.
  Their signatures assemble individual two-dimensional horns, rather than
  filter an arbitrary-dimensional prism.
- LeanSearch: "A filtration of a simplicial prism by pushouts of positive
  indexed horn inclusions". Eight hits; only the same low-dimensional horn
  pushouts, unrelated filtration declarations, a horn face identity, and
  Quillen fibration characterization. No exact match.
- Mathlib grep wrapper: `prism|shuffle|horn.*[Pp]rod` in
  `AlgebraicTopology/SimplicialSet`. Four hits, all general anodyne-extension
  documentation; no prism filtration declaration. I also read
  `ProdStdSimplex.lean`: it supplies chain coordinates, not this theorem.
- `rg` on the source project's `WeilConjectures` and side project's
  `lean/Sheaf` for `prism|Prism|rightPrism|right_prism|shuffle`: the source
  project has no match. The side project has other prisms (pinching, cone,
  Kan mapping, and bar constructions), and proof-plan references to this
  very node in `RightAnodyneProduct` and `RightFibrationContractibleFibers`.
  None declares this filtration. A separate grep for this node id in the
  upstream source has no match.
- Exact declaration-name search `right_prism_boundary|rightPrismBoundary`
  across Mathlib, upstream source and `lean/Sheaf`: no match.

No statement correction, dependency repair, new node, or disputed statement.
The node copy changes only `lean`. The prior failure came from treating the
existing Q70 stage-1 split/review as if it supplied a stage-2 Lean binding:
there was no `lean` record and no module in the retained sandbox. This delivery
preserves that reviewed split and adds the previously absent Lean statement.

## Second reading by Q14

I independently read the repository node, the sandbox node and Lean module,
both statement-dependency records and their source interfaces, and Kerodon
Lemma the project server (Tag 00TH), including its proof, at
https://kerodon.net/tag/00TH. This is a Kerodon reference, not the Stacks
tag with the same identifier. The source has no standing geometric or
coefficient assumptions: its parameter is any nonnegative integer. There
is no repair note for this item. No statement correction, new node, or
dependency module is present or needed.

My object/hypothesis/conclusion checklist, matched against the Lean:

1. Small simplicial sets in any universe: `SSet.{u}`, with `universe u`
   explicitly declared. `EnhancedDiagramsCones` imports the Mathlib
   simplicial primitives used by its dependency node; this statement needs
   no enhanced-category structure, cone object, or Kan hypothesis. PASS.
2. Every integer `m >= 0`: `(m : ℕ)`, without a positivity or finiteness
   assumption beyond this natural-number dimension. PASS.
3. The ambient degreewise product: `(Δ[1] ⊗ Δ[m] : SSet.{u})`.
   I read `Monoidal.lean` and `prodStdSimplex.objEquiv`: simplices are
   pairs of monotone maps, and operators act coordinatewise. The tensor
   notation here denotes exactly the cartesian product. PASS.
4. The boundary, including its dimension-zero convention: `boundary m`.
   Its Mathlib definition consists of nonsurjective monotone maps;
   `boundary_eq_iSup` gives the union of faces, and `boundary_zero` gives
   the empty subcomplex for `m = 0`. PASS.
5. A chain of simplicial subsets indexed from 0 through `m + 1`:
   `X : Fin (m + 2) → ...Subcomplex` and `hX : Monotone X`.
   I read `Subcomplex` and `homOfLE`: they are actual subfunctors and
   their inclusion maps. Adjacent stages are `X q.castSucc`, `X q.succ`.
   Monotonicity is exactly the required containment, not an extra
   strictness condition. PASS.
6. The prescribed initial subset: the first equality uses
   `(Subcomplex.ofSimplex (stdSimplex.obj₀Equiv.symm 1)).prod ⊤`
   joined with `⊤.prod (boundary m)`. I checked `obj₀Equiv`,
   `ofSimplex`/`ofSimplex_ι`, and `Subcomplex.prod`: this is the terminal
   vertex and its degeneracies times the full second factor, union the
   required boundary part. The lattice join is degreewise union. PASS.
7. The terminal stage is the entire prism:
   `X (Fin.last (m + 1)) = ⊤`. PASS.
8. For every index `0 <= q <= m`: `∀ q : Fin (m + 1)`.
   The witness `σ : Δ[m + 1] ⟶ Δ[1] ⊗ Δ[m]` is constrained on
   every vertex `j : Fin (m + 2)` by the displayed coordinate equality.
   `j.val ≤ q.val` and the two natural-number pairs reproduce exactly
   the node's two branches. In the second branch `j > q`, so `j - 1`
   has no unwanted truncation. Taking `.val` loses no Fin information.
   A simplex of this product is determined by its vertices, as the
   order-map description shows; naturality therefore determines the
   whole map from this formula. The existential does not replace the
   specified map by an unconstrained choice. PASS.
9. The recursive union: `X q.succ = X q.castSucc ⊔ Subcomplex.range σ`.
   The existing range construction is the degreewise image, with no
   replacement image notion. PASS.
10. The square has the specified horn inclusion, two stage-restricted
    vertical arrows, and the stage inclusion:
    `a : (horn (m + 1) q.succ).toSSet ⟶ (X q.castSucc).toSSet`,
    `b : Δ[m + 1] ⟶ (X q.succ).toSSet`, and
    `IsPushout (horn (m + 1) q.succ).ι a b
    (Subcomplex.homOfLE (hX (Fin.castSucc_le_succ q)))`.
    I read the horn definition: its missing face has index `q + 1`.
    I read `IsPushout`: it includes commutativity and the ordinary
    `IsColimit` universal property, consistent with the recorded
    `def-weil-pbc-category-colimit` interface. PASS.
11. The right vertical arrow is the codomain restriction of `σ`:
    `b ≫ (X q.succ).ι = σ`. The left vertical arrow is the horn
    restriction: `a ≫ (X q.castSucc).ι = (horn ...).ι ≫ σ`.
    Both are essential constraints and both are present. Quantifiers
    select one common chain, then the specified arrows for every `q`,
    in the node's order. PASS.

Edge cases: at `m = 0`, `Fin 2` gives precisely two stages and `Fin 1`
one attachment. The boundary is empty; the initial stage is vertex 1;
the shuffle has vertices `(0,0)`, `(1,0)`; and `horn 1 1` is vertex 1.
At `q = 0` the endpoint is the terminal endpoint, not the initial one.
At `q = m`, the index is the allowed outer horn `m + 1`, so the
statement has no hidden inner-horn restriction. Degenerate simplices
are included throughout. There is no empty indexing family to exclude
here, and no scheme, coefficient characteristic, or zero-object
hypothesis. The universe is arbitrary and no universe equality is
imposed.

Independent searches, using different wording from the worker:

- LeanFinder through `msearch.py`: "Triangulating the cylinder of a
  standard simplex relative to its boundary and final endpoint using
  successive right horn attachments". Eight hits, including `horn`,
  `horn₂₂.sq`, `horn₂₁.sq`, `horn.isColimit`, and horn face maps.
  These give individual horns and their colimits, not this filtration.
- Loogle through `msearch.py`: `"horn", "Monotone"`. No hits.
- LeanSearch through `msearch.py`: "The cylinder over an n-simplex
  relative to its boundary and terminal vertex admits a finite sequence
  of pushouts of horns with nonzero missing vertex". Eight hits,
  including the three `horn₂*.isPushout` declarations, `horn`,
  `horn_obj`, and general model-category cylinder constructions.
  I opened `HornColimits.lean`; these pushouts construct a single
  two-dimensional horn, rather than attach shuffle simplices to a prism.
- Read-only `rg` searches for `prism`, `shuffle`, `cylinder`, and
  `triangulat` in Mathlib's simplicial-set directory found no filtration
  declaration. I also opened `ProdStdSimplex.lean`; its chain equivalence
  is supporting data, not this statement.
- Read-only `rg` searches for `prism`, `rightPrism`, `right_prism`, and
  `shuffle` in upstream `WeilConjectures` found no matching statement.
  Searches in the shared project's `lean/Sheaf` found references in
  `RightAnodyneProduct` and `RightFibrationContractibleFibers`, other
  unrelated prism constructions, and tensor shuffle lemmas, not an
  existing declaration of this filtration. The upstream-name table
  has no occurrence of this node id. The sandbox's declaration is new.

No mismatch was found, so I left the Lean and node unchanged. The only
second-reader change is this review section. I checked mechanically that
the sandbox node differs from the repository node only in `lean`, that
`lean.statement` equals the file's signature verbatim, and that no Lean
line exceeds 100 characters. All variables are bound with `autoImplicit`
disabled. There are no definitions, private copies, local notations, or
proved helpers. The sole theorem has only `sorry` as its proof. Its
source/blueprint docstring follows all six node proof steps, including
the degreewise overlap argument and the pushout universal property.
