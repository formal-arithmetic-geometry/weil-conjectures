## Worker report

The delivery states `lem-sfb-poset-augmented-chain-prism`, without changing its natural-language statement, source, proof, or proof dependencies. It adds the missing general augmented strict-poset chain construction as `def-sfb-augmented-poset-chains`. Every definition has explicit data. Every theorem has only `sorry` as its proof, with its mathematical proof in its docstring.

The source read was Stacks `simplicial.tex`, lines 4739–4846: `equation-homotopy-to-homotopy` and Tag 019S, `lemma-homotopy-s-N`. This is the cancellation argument underlying the node, not a verbatim assertion of the augmented strict-poset version. I also read all eight proof steps and the existing independent stage-1 review. In our orientation the junction terms telescope to `g_* - f_*`, agreeing with the node. No correction or disputed statement is needed.

The namespace below is `AlgebraicTopology.AugmentedPosetChains`.

| Node hypothesis or clause | Lean rendering |
|---|---|
| R is any commutative ring | `(R : Type u) [CommRing R]`; no nonzero or characteristic restriction |
| P and Q are finite partially ordered sets, possibly empty | `{P Q : Type v} [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q]` in the main theorems; no `Nonempty` or chosen vertices |
| Integer-indexed module chain complex | `complex R P : ChainComplex (ModuleCat.{max u v} R) ℤ` from the added definition node |
| Degree n >= 0 free on strict chains of n+1 vertices | `Simplex P n` is the subtype of lists satisfying `List.Pairwise (· < ·)` and `(l.length : ℤ) = n + 1`; `chains R P n := Simplex P n →₀ R` |
| Degree -1 is R on the empty chain | At `n = -1`, the length equation forces length zero, so the basis has exactly the empty list; its finitely supported functions are canonically R with empty-chain coefficient as coordinate |
| Lower degrees are zero | The same length equation has no solution when `n < -1`, so the free module has empty basis and its only element is zero |
| Alternating deletion, including augmentation and empty boundary | `boundary R P i j` is zero unless `i = j + 1`; otherwise it is the linear extension of `∑ k ∈ Finset.range c.val.length, (-1 : R)^k • bracket R j (c.val.eraseIdx k)`; the length-one case is `[x] ↦ [∅]`, and the length-zero case is an empty sum |
| These are a chain complex | Named proof obligation `boundary_laws` supplies shape and square zero; `complex` constructs Mathlib's `HomologicalComplex` using these proofs and the explicit modules and boundary |
| Weak tuples with repetitions mean zero | `bracket R n l` is the unit basis vector if the list is strict and has the required degree, zero otherwise; repeated weak tuples cannot satisfy its strictness test |
| Every monotone map u induces the specified chain map | `f : P →o Q`; `mapComponent R f n` is the linear extension of `bracket R n (c.val.map f)`; `map_comm` asserts the chain-map equation in all integer degrees, and `map R f` constructs the actual Mathlib chain map using that proof |
| Empty generator is fixed | `List.map f [] = []`; the degree -1 generator is therefore fixed by the explicit `mapComponent` formula |
| Identities preserved | `map_id`: `map R (OrderHom.id : P →o P) = 𝟙 (complex R P)` |
| Compositions preserved | `map_comp`: for a third finite poset S and `f : P →o Q`, `g : Q →o S`, `map R (g.comp f) = map R f ≫ map R g` |
| f and g are monotone and f(x) <= g(x) for every x | `(f g : P →o Q) (hfg : ∀ x : P, f x ≤ g x)` in `prism_identity` |
| The displayed linear prism, not an arbitrary homotopy | `prismComponent R f g i j` is the linear extension of `∑ k ∈ Finset.range c.val.length, (-1 : R)^k • bracket R j (((c.val.take (k + 1)).map f) ++ ((c.val.drop k).map g))` when `0 ≤ i ∧ j = i + 1` |
| h at -1 and in lower source degrees is zero | The `0 ≤ i` guard makes `prismComponent` literally the zero morphism for every negative source degree |
| dh + hd = g_* - f_* in every integer degree | `prism_identity` quantifies `(n : ℤ)` and asserts `prismComponent R f g n (n+1) ≫ (complex R Q).d (n+1) n + (complex R P).d n (n-1) ≫ prismComponent R f g (n-1) n = (map R g).f n - (map R f).f n` |

The existing dependency `def-weil-pbc-module-chain-complex-homology` is a Mathlib leaf. I read its full record and the recorded source `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`: `HomologicalComplex.homology`, its `HomologicalComplex.Hom` chain maps, `ChainComplex`, and `HomologicalComplex.homologyMap`. I also read `ShortComplex.moduleCatLeftHomologyData` and `moduleCatHomologyIso` from `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`, confirming that the chain and homology conventions are the node's kernel/image conventions. The statement uses the existing Mathlib `ChainComplex` and morphisms; it does not introduce a separate complex or homotopy predicate. Other construction APIs used are `ModuleCat.of`, `ModuleCat.ofHom`, `Finsupp.single`, `Finsupp.linearCombination`, `List.Pairwise`, and `OrderHom` from their public imports. The added definition node is imported publicly by the item.

Edge cases checked directly from the formulas: P empty leaves only the degree -1 empty generator; Q empty forces P empty for any supplied map. At n = 0, h[x] is [f(x),g(x)], and its boundary is [g(x)] - [f(x)]. If f(x) = g(x), the prism tuple is killed and both endpoint terms agree. At n = -1, both h terms are zero and g_* - f_* is identity minus identity. Below -1 the source free module has empty basis. For a singleton poset, the sole nonzero differential is the identity between its vertex and empty generators. A map collapsing a strict edge sends it to zero, while its endpoint boundary images cancel; further composition cannot restore a strict image. The n = 1 prism has two terms with signs + and -, and its off-junction boundary faces cancel those of hd. Characteristic two, the zero ring, and degenerate comparable maps require no change. No linear order, decidable equality, nonempty poset, or nontrivial ring assumption was added. All variables and universes are explicitly bound, with auto-implicit disabled.

Searches actually run using `msearch.py NM lem-sfb-poset-augmented-chain-prism`:

- LeanFinder, `Pointwise comparable monotone maps of posets induce a prism chain homotopy on augmented strict chains`: eight hits including `CategoryTheory.SimplicialThickening.orderHom`, `SimplexCategory.II.monotone_map'`, `SSet.Augmented.StandardSimplex.shift`, and `AlgebraicTopology.DoldKan.hσ'`; none gives the item. A preliminary search with the longer comparable-maps phrasing was also run.
- Loogle, `"OrderHom", "Homotopy"`: zero hits.
- LeanSearch, `Free modules on strict chains of a poset with augmented deletion differential and signed prism operator`: eight hits, notably `ChainComplex.augment`, `Module.Free.mk` and `Module.Free.finsupp`; none constructs this complex and prism.
- LeanFinder, `The augmented chain complex of a poset has free modules on strictly increasing chains, the empty chain in degree minus one, and alternating deletion differential`: eight hits including `ChainComplex.alternatingConst`, `ChainComplex.augment`, `AlgebraicTopology.AlternatingFaceMapComplex.obj`, and `Rep.standardComplex.d_of`; no exact match.
- Mathlib grep, `augmented.*[Pp]oset|[Pp]oset.*[Cc]hain|orderComplex`, in `AlgebraicTopology`: zero hits. The initial prism grep was broader and returned unrelated prism usages; it was refined to this query.
- Direct `rg` with that pattern in the project's `lean/WeilConjectures` and `lean/Sheaf`: a sectionwise Cech cochain docstring, and the parent's docstring citing this prism. `grep -rn` of the item id in `lean/WeilConjectures` returned no declaration.
- DAG searches for strict chains, augmented strict posets and the proposed new id: no general definition node. `tools/blueprint_refs.py search 'augmented strict poset'` returned zero blueprint matches; `ancestor` returned None, so the new node preserves the inherited null ancestry and prepends this item to `via`.

I opened the candidate Mathlib normalized simplicial-chain API and Dold–Kan homotopy definitions. They concern a supplied simplicial object or its normalization; using them here would still require constructing the poset simplicial object, identifying its nondegenerates with strict chains, adding degree -1, and proving the displayed formula. They are not exact existing declarations for this item.

The parent `Sheaf.Combinatorics.ProductChainProperIntervalHomology` was read in full after its parallel landing appeared. Its `ProductChainProperInterval.complex` is specialized to Q and the proper part of a product of finite chains; it cannot instantiate an arbitrary finite poset or ring. Its Fin-indexed strict-chain basis and our list basis describe the same complex after that specialization, by listing the ordered vertices. No parent file or statement is edited. The parent can use the general prism through that basis identification during stage 3. Its ordinary proof-dependency import is left to the maintainer as required by stages/2-statements.md §3(7).

The previous worker's stale-dispatch refusal concerned the already completed stage-1 split. This packet only supplies stage-2 declarations. I found no repair note for the item.

Both modules compiled through `scompile.py` against the current server build, separately in dependency order, with no warnings or errors. The first attempt's nonexistent `Mathlib.Data.List.EraseIdx` import was replaced by `Mathlib.Data.List.Pairwise`; the clean compile took about two seconds per file. The named postponed theorems are `boundary_laws`, `map_comm`, `map_id`, `map_comp`, and `prism_identity`, attached to the definition node's construction obligation or the item's own clauses.

## New nodes

`def-sfb-augmented-poset-chains` supplies the general integer-indexed augmented strict-poset chain complex, basis and bracket convention that the item needs and that its sole prior dependency did not define. The source is the explicit augmented strict-poset adaptation of Stacks Tag 019S recorded in the item's statement and proof steps 1–2. The definition is given by actual finitely supported functions on strict lists and the actual alternating-deletion linear maps. Its named `boundary_laws` postpones only the proof that this specified boundary has the required shape and square zero, so its data is not chosen from an existence theorem. The node's statement includes that construction obligation. The recorded LeanSearch, LeanFinder, Loogle and grep searches are exactly the queries run above. The related specialized parent complex and Mathlib's general simplicial constructions do not give the general notion. No other new node or dependency repair is needed.

Dry-run repair: the server signature checker records a noncomputable declaration starting at the `def` keyword, excluding the modifier. The added node record now uses that exact signature; no Lean declaration or mathematical content changed.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
