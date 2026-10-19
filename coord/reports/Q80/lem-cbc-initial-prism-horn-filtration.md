## Worker report

The module `Sheaf.CategoryTheory.InitialPrismHornFiltration` states
`SSet.exists_initial_prism_horn_filtration`, with its whole proof `sorry`.
It introduces no definitions or helper theorems. Its docstring carries all four
DAG proof steps, including the absent missing face and the initial-edge condition.

Source checked: [Kerodon Lemma the project server, Tag 01DN](https://kerodon.net/tag/01DN),
assertions (1) and (2), and its full free-simplex proof. The statement agrees with
the DAG. No statement correction, disputed statement, or dependency fault was found.
The earlier archival-copy request remains outside this sandbox's authorized scope.

Clause-by-clause correspondence:

- Integers `m ≥ 0`, `n ≥ 2`: `(m n : ℕ) (hn : 2 ≤ n)`. Natural numbers encode all
  the permitted nonnegative integers, including `m = 0`. The universe `u` is arbitrary.
- Boundary, including the empty zero-dimensional boundary: Mathlib `boundary m`.
  Its definition is the nonsurjective ordinal maps, and `boundary_eq_iSup` identifies
  it with the union of proper faces. Every map to `[0]` is surjective, so `boundary 0`
  is empty in every degree. There is no new boundary definition.
- A finite sequence of simplicial subsets: `∃ (t : ℕ)
  (X : Fin (t + 1) → (Δ[m] ⊗ Δ[n] : SSet.{u}).Subcomplex) (hX : Monotone X)`.
  Mathlib's tensor product of simplicial sets is the degreewise Cartesian product.
  `Subcomplex` is the recorded simplicial subset, and `Monotone X` gives the inclusions.
- Prescribed initial stage: `X 0 = (boundary m).prod ⊤ ⊔
  (⊤ : (Δ[m] : SSet.{u}).Subcomplex).prod (horn n 0)`.
  `prod` is the external degreewise product of subsets, `⊔` their degreewise union.
- Entire final product: `X (Fin.last t) = ⊤`.
- Every step `1 ≤ s ≤ t`: `∀ s : Fin t`, using the predecessor `s.castSucc` and
  successor `s.succ`. These run through exactly the consecutive pairs `0,1` to `t-1,t`.
- Dimensions and horn indices: `∃ (q : ℕ) (hq : 2 ≤ q) (p : Fin (q + 1)), p.val < q`.
  The `Fin` binder supplies `0 ≤ p`; the strict inequality excludes the terminal horn.
- The attaching simplex map: `σ : Δ[q] ⟶ (X s.succ).toSSet`.
- Its horn factors through the old stage: `a : (horn q p).toSSet ⟶
  (X s.castSucc).toSSet`, together with the commutativity contained in `IsPushout`.
- The square is a pushout: `IsPushout (horn q p).ι a σ
  (Subcomplex.homOfLE (hX (Fin.castSucc_le_succ s)))`. The four arrows are the
  horn inclusion, the map to the old stage, the attaching map, and the old-to-new
  inclusion. `IsPushout` contains precisely commutativity and the span cocone's
  `IsColimit`, giving the specified colimit universal property.
- When `p = 0`, the two vertices map to `(0,0)` and `(0,1)`: the implication
  `p.val = 0 → ... ∧ ...` evaluates `σ ≫ (X s.succ).ι` in degree zero on
  `stdSimplex.obj₀Equiv.symm 0` and `stdSimplex.obj₀Equiv.symm ⟨1, by omega⟩`.
  The two right sides are the corresponding pairs of standard-simplex vertices.
  The proof terms only certify that vertex one exists using `hq` and `hn`.

Dependencies read and used:

- `def-cbc-enhanced-diagrams-cones`: `Sheaf.CategoryTheory.EnhancedDiagramsCones`
  explicitly uses Mathlib `SSet`, `stdSimplex`, `horn`, and the degreewise monoidal
  product. The recorded main declaration is `SSet.Enhanced.coneCategory`; this node
  uses the simplicial primitives described in the same module, rather than cones.
  I read that module's header, conventions, and the existing primitive signatures
  and docstrings. No copy of a notion is introduced.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit`, `Cocone`, and `IsColimit`. The pushout-specific
  interface is `CategoryTheory.IsPushout` from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`, whose
  `isColimit'` field asserts `Nonempty (IsColimit (PushoutCocone.mk ...))`.
- Proof dependency `def-weil-pbc-simplicial-set`: its Mathlib matches are `SSet`,
  `SSet.degenerate`, `SSet.nonDegenerate`, `SSet.Subcomplex`, and `SSet.Finite`.
  Their signatures and docstrings were read; `Mathlib.AlgebraicTopology.SimplicialSet.Finite`
  is imported for this proof-only dependency. The other two proof dependencies
  are already public statement imports.

Edge cases checked before writing: `m = 0` gives an empty boundary and a single
standard `n`-simplex with its zeroth horn as initial stage. `n = 2` is permitted;
its initial vertical edge exists and the next vertex used in the proof is present.
`t = 0` is allowed by the encoding, with no attachment indices, without imposing
an extra nonemptiness assumption; the asserted initial/final equalities determine
whether that case can occur. `q = 2` and `p = 0,1` are included, while `p = q` is
excluded exactly as in the node. Both endpoint vertices have explicitly justified
bounds. No universe restriction or injectivity hypothesis is imposed on `σ`.

Searches for an existing statement:

- `msearch.py leanfinder`: “A product of simplices relative to boundary times
  simplex and simplex times the zeroth horn admits a finite horn pushout filtration
  whose outer horn edges are the initial vertical edge”. Eight hits, individual
  two- and three-dimensional horn pushouts/fillers; no matching prism filtration.
- `msearch.py loogle`: `"horn", "IsPushout"`. Three hits:
  `SSet.horn₂₀.isPushout`, `SSet.horn₂₁.isPushout`, `SSet.horn₂₂.isPushout`.
  These construct individual horns and do not state the relative product filtration.
- `msearch.py leansearch`: “Finite horn attachment filtration of the product of
  standard simplices relative to the boundary and initial horn with specified
  initial edge”. Eight hits, mainly `SSet.horn.edge`, `horn.primitiveEdge`, and horn
  inclusion identities. No exact match.
- `msearch.py grep`: `prism|shuffle|horn.*[Ff]iltrat|[Ff]iltrat.*horn` under
  `AlgebraicTopology/SimplicialSet`. Five hits in `AnodyneExtensions/RelativeCellComplex`.
  I also read its `RankFunction.isPushout` and `relativeCellComplex`, and
  `AnodyneExtensions/UnionProd`'s `pairingCore`, `pairing`, and regularity/innerness
  declarations. These give rank-indexed coproduct attachments, requiring finite
  linearization and the additional initial-edge check, so do not match this theorem.
- `rg` of the upstream `WeilConjectures` source for prism/shuffle/horn filtration
  and the proposed declaration, and `grep -rn` for the item id: no match.
- `rg` in `lean/Sheaf` for initial prism/horn filtration/free simplex found
  `RightPrismBoundary` and `InvertiblePrismExtension`, both read. The former concerns
  a one-dimensional factor and positive-index horns; the latter uses this node to
  prove a map extension. Neither is this statement.
- `rg` in `dag/lean_names_upstream.json` for the proposed name, `01DN`, and initial
  prism: no matching declaration.

Validation: the prescribed `scompile.py` compiled the module cleanly, both as a
sandbox module and under its library module path. The final module, including its
proof-dependency import, is also compiled by `deliver2.py ... --no-push`. The worker
hands off only after that required dry run prints OK. The independent second reader
will add their own reading and deliver; this worker has not written a second-reading
section.

## Second reading by Q80

I reread Kerodon Lemma the project server (01DN) and the complete theorem in
`lean/Sheaf/CategoryTheory/InitialPrismHornFiltration.lean` independently.
The source's objects and hypotheses match the Lean as follows:

- The source integers `m ≥ 0` and `n ≥ 2` are `(m n : ℕ)` and `hn : 2 ≤ n`; this
  includes `m = 0` and imposes no extra finiteness, characteristic, or universe
  condition. The ambient universe `u` is arbitrary.
- The source simplices, horns, products, and simplicial subsets are Mathlib's
  `Δ[m]`, `Δ[n]`, `horn`, the degreewise tensor `Δ[m] ⊗ Δ[n]`, and
  `Subcomplex`. Mathlib `boundary m` is the nonsurjective-map boundary, so it is
  empty at `m = 0` as required by the source convention.
- The finite sequence is rendered by `∃ (t : ℕ) (X : Fin (t + 1) →
  (Δ[m] ⊗ Δ[n]).Subcomplex) (hX : Monotone X)`. `Monotone X` gives exactly the
  consecutive inclusions `X(s) ≤ X(s+1)`; the `Fin (t+1)` indexing includes the
  allowed `t = 0` case.
- The initial and terminal clauses are exactly
  `X 0 = (boundary m).prod ⊤ ⊔ ⊤.prod (horn n 0)` and
  `X (Fin.last t) = ⊤`, matching the source union and full product.
- `∀ s : Fin t` with `s.castSucc` and `s.succ` ranges exactly over each
  `1 ≤ s+1 ≤ t`. The witnesses `q`, `hq : 2 ≤ q`, `p : Fin (q+1)`, and
  `p.val < q` render `q ≥ 2` and `0 ≤ p < q` with no omitted endpoint case.
- The attaching map is `σ : Δ[q] ⟶ (X s.succ).toSSet`; the map `a` from
  `(horn q p).toSSet` to `(X s.castSucc).toSSet` is the source factorization of
  the horn restriction. `IsPushout (horn q p).ι a σ
  (Subcomplex.homOfLE (hX (Fin.castSucc_le_succ s)))` has precisely the source
  square's horn inclusion, horn-to-old-stage map, simplex-to-new-stage map, and
  old-to-new inclusion. Its `CommSq` component supplies commutativity and its
  `isColimit'` component supplies the required pushout/colimit universal
  property.
- The endpoint clause is rendered by composing `σ` with the inclusion
  `(X s.succ).ι` into the product and evaluating degree zero at the two standard
  vertices. Under `p.val = 0`, the equalities are exactly `(0,0)` and `(0,1)`;
  `hn` and `hq` provide the bounds needed for the displayed `Fin` witness for
  vertex `1`.

I found no mismatch between the node and the Lean signature: no hypothesis is
added, dropped, or strengthened, and no conclusion clause is weakened or
strengthened. In particular, the Lean uses the recorded Mathlib notions rather
than private boundary, horn, product, or pushout definitions. No source-based
statement correction, dependency repair, or file change was needed.

Edge cases checked were `m = 0` (empty boundary), `n = 2` (the least permitted
vertical dimension and the required next second-coordinate vertex), `q = 2`,
`p = 0` and `p = q - 1`, `t = 0`, and arbitrary `u`. The `Fin` binders retain
all nonnegative indices, and there is no hidden nonemptiness, injectivity, or
Noetherian assumption.

For duplicate searches I checked the project and upstream `WeilConjectures`
source with `rg` for `initial_prism`, `horn_filtration`, `01DN`, `prism`, and
`free simplex`, and read the nearby `RightPrismBoundary` and
`InvertiblePrismExtension` declarations. I also checked Mathlib's `Boundary`,
`Horn`, `Monoidal`, `SubcomplexColimits`, and `AnodyneExtensions` files, plus
LeanFinder/Loogle/LeanSearch results recorded by the worker. The existing
pairing and individual-horn declarations do not state this finite filtration or
its endpoint condition, so there is no duplicate notion. The prescribed
`scompile.py` check compiled the module cleanly with only the expected `sorry`
proof warning.
