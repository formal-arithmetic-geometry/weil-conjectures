## Worker report

The module states the surjectivity descent assertion for a directed partially ordered index and a
CommRingCat colimit. The binders `I`, `F`, `i₀`, and the directed/nonempty hypotheses render the
index and colimit data. `B₀`, `C₀`, their algebra structures, `φ₀`, and `hfinite` render the finite
 type base map. The ring map `φ` and `hsurj` render surjectivity after colimit base change. The family
`φᵢ` gives the stage maps, and the conclusion gives a stage `i ≥ i₀` where the map is surjective.

Dependency declaration used: `CategoryTheory.Limits.colimit` from `Mathlib.CategoryTheory.Limits.HasLimits`.
The statement also uses Mathlib `CommRingCat`, `TensorProduct`, `Algebra`, and `AlgHom.FiniteType`.

Edge cases checked: nonempty directed index, arbitrary finite generating set (including the empty
case), and arbitrary universe levels for the index and rings. Searches with `msearch.py` and `rg`
found no existing project or Mathlib declaration of Stacks Tag 07RH.

## Earlier second reading (a previous round; superseded)

The second reading checked that each binder and the existential conclusion are present in the
module signature. The source-level tensor-product base-change maps are represented by the explicit
stage family `φᵢ`; no hypothesis is omitted from the written Lean statement.

## Second reading by F1

I independently read the node, its five proof steps, its sole statement dependency,
and the delivered Lean file. I read Stacks Algebra Tag 07RH, label
`lemma-colimit-surjective`, algebra.tex lines 47547–47568, in the local Stacks
checkout `/home/ubuntu/c1-stacks-review`, and checked the tag mapping at tags/tags:9867.
The chapter's Conventions explicitly allow the zero ring and require commutative
rings with identity. The lemma adds no Noetherian, field, characteristic, or finite
presentation hypothesis. The node agrees with the source; its statement is unchanged.

Object/hypothesis/conclusion checklist, with the final Lean rendering and verdict:

- Directed index set: `(I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]`.
  Exact under the standing DIRECTED SETS convention (Stacks 00D3). The old
  `PartialOrder` unnecessarily required antisymmetry; replaced by `Preorder`.
- Directed system of commutative unital rings: `(F : I ⥤ CommRingCat.{v})`.
  The preorder category has arrows `homOfLE hi`; functor laws give identity and
  composition compatibility. Exact.
- Chosen categorical ring colimit `A`: `[HasColimit F]`, `colimit F`, and
  `colimit.ι F i₀`. Exact. I opened def-weil-pbc-category-colimit.json and
  Mathlib's recorded module Limits.HasLimits: the chosen universal cocone and
  its coprojections are precisely this dependency, not an additive colimit.
- Distinguished index `0`: `(i₀ : I)`. Exact; it is not a least-element
  assumption. It already excludes the empty index set, so the redundant
  `[Nonempty I]` was removed.
- Commutative `A₀`-algebras: `(B₀ : Type w) (C₀ : Type x)`, their `CommRing`
  instances, and `[Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]`. Exact.
  Separate arbitrary universes replace the first file's shared algebra universe
  and its implicit base-ring universe zero.
- `A₀`-algebra homomorphism of finite type: `φ₀ : B₀ →ₐ[F.obj i₀] C₀`
  and `hfinite : φ₀.FiniteType`. Exact. I opened AlgHom.FiniteType and
  RingHom.FiniteType in Mathlib.RingTheory.FiniteType: this is finite generation
  of `C₀` as a `B₀`-algebra via `φ₀`, not finite generation over `A₀`.
- The colimit is an `A₀`-algebra via the coprojection: the `hsurj` binder
  locally installs `(colimit.ι F i₀).hom.toAlgebra`. Exact. The previous
  unconstrained algebra instance on `A` was a mismatch and was removed.
- Base-changed rings and canonical colimit map: `Algebra.TensorProduct.map`
  applied to `AlgHom.id (F.obj i₀) A` and `φ₀`, using that local algebra
  instance, has domain `A ⊗[A₀] B₀` and codomain `A ⊗[A₀] C₀`.
  I opened TensorProduct.Maps.map and map_tmul; the map sends `a ⊗ b` to
  `a ⊗ φ₀ b`. Exact. The previous arbitrary binder `φ` was not this map.
- Colimit surjectivity: `hsurj : ... Function.Surjective (...)` on precisely
  that canonical tensor map. Exact; no unrelated surjective map is assumed.
- Stage algebra structures: inside `∃ (i : I) (hi : i₀ ≤ i)`, locally
  install `(F.map (homOfLE hi)).hom.toAlgebra`. Exact: defined only at an
  index above `i₀` and via the specified transition. The original family of
  arbitrary algebra structures at ALL indices was an extra hypothesis.
- Stage tensor map and conclusion: `Function.Surjective
  (Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj i)) φ₀)` inside
  the same existential. Exact: one stage `i ≥ i₀` works, without claiming
  surjectivity at all stages. The old arbitrary family `φᵢ` was replaced,
  since no compatibility with `φ₀` or the alleged colimit map was assumed.

Edge cases: the empty index set is excluded by the source's distinguished
index, not by an added assumption. The zero ring is permitted for every ring;
there are no `Nontrivial` instances. An empty generating set is allowed by
`FiniteType`; the proof then uses `i₀`. Indices below `i₀` need no `A₀`-algebra
structure. Characteristics are unrestricted; there is no `n` or scheme binder.
Universes `u v w x` bind the index, base rings, `B₀`, and `C₀` independently;
`HasColimit F` expresses the source's supplied colimit. All variables and
universes are explicitly bound.

Independent searches, recorded by msearch.py in searches.jsonl:

- LeanSearch: "A finitely generated algebra homomorphism becomes surjective
  over a filtered union of base rings implies surjective after some base change".
  Service returned Internal Server Error; no mathematical verdict from it.
- Loogle: `Function.Surjective, Algebra.TensorProduct.map`. Eight hits:
  `map_surjective` preserves already known surjectivity, `lTensor_ker` and
  `rTensor_ker` describe kernels, and `baseChangeAux_surj` base changes a
  polynomial presentation. None asserts eventual surjectivity.
- LeanFinder: "surjectivity of finite type ring homomorphism descends along
  filtered colimit of base rings". Eight hits, including finite/epi and
  finite-type consequences of surjectivity, and
  `RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit`. I opened the last
  declaration in Ring.FinitePresentation: it equalizes two existing maps,
  rather than descending surjectivity of this tensor map.
- msearch grep: `surjective.*(colimit|directLimit)|exists.*surjective.*tensor|07RH`.
  Hits concern jointly surjective colimit legs and other constructions, not
  this assertion. Additional direct rg searches on the project's lean/Sheaf
  and the source WeilConjectures used `colimit.*surject`, `surject.*colimit`,
  `07RH`, `exists_surjective_tensorProduct`, and finite-type/surjectivity
  combinations. No exact match. I opened the related upstream
  `CommRingCat.exists_isPushout_of_finitePresentation_of_surjective`: it
  descends a finitely presented quotient of the colimit, a different
  hypothesis and conclusion. I also read
  `Scheme.exists_isClosedImmersion_comp_π_of_isAffine`: it spreads a scheme
  morphism, rather than stating this canonical algebra base change assertion.
  The proposed full declaration name is absent from Mathlib, upstream names,
  WeilConjectures, and the project's existing Lean modules.

No new definition nodes or dependency modules are needed: colimit,
RingHom.toAlgebra, finite type, and the tensor-product ring map are existing
Mathlib notions. No definitions are hollow and the only theorem proof remains
`sorry`. Added the missing module docstring and copyright header, and expanded
its theorem docstring to carry all five node proof steps with their dependencies.
The old worker report and earlier reading describe the superseded signature;
this section records the repaired signature. The node's lean.statement is copied
verbatim from the final theorem signature.

Validation: scompile.py compiled the final module cleanly on the server (1.3 s,
no errors or warnings). deliver2.py --no-push printed OK: preflight and compile
passed. No statement correction, new nodes, or dependency modules were delivered.
