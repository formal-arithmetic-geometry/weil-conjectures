## Worker report

The module `lean/Sheaf/AlgebraicGeometry/NowhereDenseDimZero.lean` states
`AlgebraicGeometry.dim_le_zero_of_isNowhereDense`. It binds a field `k`, schemes `X` and `Z`,
the structure morphism `f : X ⟶ Spec k`, and finite-type instances
`LocallyOfFiniteType f` and `QuasiCompact f`. The hypothesis `hX : X.dim ≤ 1` is the node's
dimension bound, using `Scheme.dim` from `Sheaf.AlgebraicGeometry.Dimension`. The morphism
`i : Z ⟶ X` with `[IsClosedImmersion i]` renders the closed subscheme, and
`hnow : IsNowhereDense (Set.range i.base)` renders that its underlying closed subset is nowhere
dense. The conclusion is the conjunction `Z.dim ≤ 0` and
`∀ z : Z, IsClosed ({z} : Set Z)`, including the empty case through `Scheme.dim`'s bottom
convention.

The dependency declarations used are `AlgebraicGeometry.Scheme.dim` from
`Sheaf.AlgebraicGeometry.Dimension`, Mathlib's `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.QuasiCompact`, and Mathlib's `AlgebraicGeometry.IsClosedImmersion`. The
nowhere-dense predicate is Mathlib's `IsNowhereDense` from `Mathlib.Topology.GDelta.Basic`.

Edge cases checked: `X = ∅` forces the closed subscheme to be empty; `Z = ∅` satisfies the
dimension and point clauses; a closed point such as `V(t) ⊂ Spec k[t]` is nowhere dense and has
dimension zero; taking a whole irreducible component in a reducible one-dimensional scheme is
excluded because its image is not nowhere dense.

Searches made:

- `msearch.py ... leanfinder "dimension of a closed nowhere dense subscheme of a one-dimensional scheme every point closed"`: related height and quasi-sober declarations, no matching theorem.
- `msearch.py ... loogle "IsNowhereDense, Scheme.dim, IsClosedImmersion"`: no hits (`Scheme.dim` unknown to Loogle).
- `msearch.py ... grep "IsNowhereDense.*Scheme.dim|dimension.*nowhere" Mathlib`: no hits.
- `rg` over `WeilConjectures` and `lean/Sheaf` for nowhere-dense dimension lemmas: only generic nowhere-dense topology facts, no matching statement.

No `STATEMENT-DISPUTED` issue or node fault found.

## Earlier second reading (a previous round; superseded)

Reading the node and module together, the field, finite-type, dimension, closed-immersion, and
nowhere-density hypotheses all occur in the Lean signature. The first conclusion clause is
`Z.dim ≤ 0`; the second is the pointwise closedness assertion. The module uses the same schemes
and the same underlying image `Set.range i.base` as the node, and does not add separatedness,
nonemptiness, or a characteristic assumption. The proof is `sorry` as required for stage 2.

## Second reading by E1

I independently opened the sandbox node and module, all three statement dependency nodes,
`lean/Sheaf/AlgebraicGeometry/Dimension.lean`, and the Mathlib declarations below. The Lean
signature says exactly what the node says; no signature or mathematical node change is needed.
There are no new definition nodes or dependency modules in this delivery and no
`statement_change` to review.

Object, hypothesis, and conclusion inventory (each verdict: matches):

- A field k: `{k : Type u} [Field k]`. No algebraic-closure, characteristic, or finiteness
  condition on the field.
- A scheme X over k: `{X Z : Scheme.{u}}` and `(f : X ⟶ Spec (.of k))`. The explicit morphism
  supplies the structure map; no separate Over instance or compatibility hypothesis is needed.
- Finite type of X over k (`def-weil-finite-type-morphism`): `[LocallyOfFiniteType f]`
  together with `[QuasiCompact f]`. I read FiniteType.lean:43 and QuasiCompact.lean:43,97:
  these are the affine ring-map condition and quasi-compact preimages, respectively. Their
  conjunction is precisely finite type, as the dependency's Mathlib record prescribes.
- Dimension at most one (`def-pc-dimension`): `(hX : X.dim ≤ 1)`. I read `Scheme.dim` in
  `Sheaf.AlgebraicGeometry.Dimension`: it is the supremum of `ringKrullDim` of the stalks,
  valued in `WithBot ℕ∞`, with the empty supremum equal to bottom. This is the node's local
  ring convention, including its explicit extension to the empty scheme.
- A closed subscheme Z of X (`def-weil-closed-immersion`): `(i : Z ⟶ X)` and
  `[IsClosedImmersion i]`. I read ClosedImmersion.lean:45: closed embedding of spaces and
  surjective stalk maps. This is the dependency's notion, not merely a closed subset or a
  reduced closed subscheme. Arbitrary nilpotents are permitted.
- The underlying subset is nowhere dense in X: `(hnow : IsNowhereDense (Set.range i.base))`.
  GDelta/Basic.lean:200 defines this as `interior (closure s) = ∅`. The range is the image
  in X of the underlying map of i, exactly the node's underlying subset.
- First conclusion: `Z.dim ≤ 0`, using the same local-ring dimension and empty convention.
- Second conclusion: `∀ z : Z, IsClosed ({z} : Set Z)`. Singleton closedness is in Z itself,
  with the point quantifier inside the conclusion after all hypotheses. Both clauses occur
  in one conjunction; no finiteness, affineness, or closedness-in-X conclusion is substituted.

Source reading: the referenced repository literature path is absent on this machine. I found
and read the local Stacks TeX copy `/home/ubuntu/c1-stacks-review/varieties.tex`, lines
9832–9869 (`lemma-degree-effective-Cartier-divisor`, Tag 0AYY), and lines 3720–3776
(`definition-algebraic-scheme` and `lemma-algebraic-scheme-dim-0`, Tag 06LH).
The former assumes proper X and effective Cartier D for its full degree statement. This node
isolates its dimension-drop inference for an arbitrary nowhere-dense closed subscheme:
properness supplies finite type in the source, and no separatedness or Cartier condition is
used in that inference. The node's finite-type generalization is valid by its component-chain
proof; adding properness would wrongly strengthen its hypotheses. Tag 06LH defines locally
algebraic as locally of finite type and proves such zero-dimensional schemes discrete, which
supplies the point-closedness clause. There is no hidden standing characteristic or
geometric-integrality assumption in either source lemma.

Edge cases: empty X forces empty Z; empty Z has dimension bottom and a vacuous point clause.
In dimension zero, a nonempty closed subset of the finite discrete space cannot be nowhere
dense, so only empty Z qualifies. `Spec k[t]` with Z = V(t) is the nonempty dimension-one test.
A whole component of `Spec k[x,y]/(xy)` has nonempty interior and fails hnow, as required.
Nonreduced X and Z are allowed. The arbitrary universe u covers schemes and fields at any
size (one common universe can contain all objects); no nonemptiness or small/finitary type
instance is imposed. There is no numerical n, index family, or zero module in this statement;
the empty component family has already been covered by empty X. All variables and the
universe are explicitly bound.

Independent searches, using different wording from the first worker:

- LeanFinder via msearch: "Krull dimension drops for a closed subset with empty interior in a
  Noetherian space of dimension one". Eight hits, including `topologicalKrullDim_subspace_le`
  and `IsInducing.topologicalKrullDim_le`, provide only the nondropping dimension inequality;
  none states the node.
- LeanSearch via msearch: "A closed nowhere dense subset of a one dimensional scheme has
  dimension at most zero". HTTP 500; unavailable, so no mathematical verdict from this tool.
- msearch grep: `((krullDim|dimension|dim_le).*(nowhere|interior))|` followed by
  `((nowhere|interior).*(krullDim|dimension|dim_le))`. Only Hausdorff/convex-dimension hits,
  no matching Krull-dimension theorem.
- Independent rg over all `WeilConjectures`, repository `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `nowhere`, `dim_le_zero_of_isNowhereDense`, and dimension
  of a closed subset: the source has generic stratification nowhere-density lemmas, not this
  result; the project has Cartier-divisor specializations and dimension-zero finiteness,
  neither of which supplies this general statement. No existing full-name collision found.

Mismatch and repair: H8 only. The original proof docstring compressed the argument without
naming its DAG dependencies. I expanded it into all three node proof steps, named every
used node, made the nonempty irreducible chain and component alternatives explicit, and
added the Tag 06LH source for the last step. The signature, imports, node, and Worker report
are retained. No hollow definition is introduced; the only theorem body remains `by sorry`.
The imports each provide a notion used in the signature. Compilation and delivery preflight
are run after this repair; the signature recorded in `lean.statement` remains verbatim equal
to the source signature.
