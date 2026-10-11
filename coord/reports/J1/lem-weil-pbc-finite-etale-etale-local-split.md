## Worker report

The module `Sheaf.Paper.FiniteEtaleEtaleLocalSplit` states
`AlgebraicGeometry.finite_etale_etale_local_split`. Its hypotheses are a morphism
`f : Y ⟶ X` with instances `[IsFinite f]` and `[Etale f]`, and a point `x : X`.
The conclusion gives an étale neighbourhood `g : U ⟶ X` and point `u : U` with
`g.base u = x`; a finite index type `J` (`Fintype J`), schemes `V j`, and maps
`ι j : V j ⟶ pullback f g`; each `ι j` is both `IsOpenImmersion` and
`IsClosedImmersion`; their ranges are pairwise disjoint and cover the pullback;
and each composite `ι j ≫ pullback.snd f g` is represented by an isomorphism
`V j ≅ U`. The pullback is Mathlib's `CategoryTheory.Limits.pullback`, matching
`def-pc-fibre-product`; étale is Mathlib's `AlgebraicGeometry.Etale`, matching
`def-weil-etale-morphism`. The finite and étale hypotheses render the node's finite
étale assumption, and the finite coproduct decomposition is expressed by the
finite family of clopen, pairwise disjoint immersions covering the pullback,
with each component isomorphic over `U`.

Edge cases checked: `J` may be empty (allowing an empty finite étale cover), and
all scheme and index universes are explicit (`Scheme.{u}`, `Type u`). No
nonempty or cardinality hypothesis was added.

Searches for an existing statement or definition: LeanSearch query “finite etale
morphism of schemes is etale locally a disjoint union of copies of the base” found
only general `IsEtale` and finiteness declarations (no match); LeanFinder query
“finite étale morphism becomes a finite disjoint union of isomorphisms after base
change along an étale neighbourhood of a point” found only composition and
algebra-level results (no match); Loogle query “AlgebraicGeometry.IsFinite,
AlgebraicGeometry.Etale, CategoryTheory.Limits.Sigma.desc” returned none; grep of
Mathlib found only algebra-level finite étale results and no scheme splitting;
`rg` over `WeilConjectures/` and `lean/Sheaf` found no matching declaration.

## Earlier second reading (a previous round; superseded)

The statement was reread against the node clause by clause. `IsFinite f` and
`Etale f` encode “finite étale”; `g.base u = x` gives the required point over
`x`; `Fintype J` gives a finite set; clopen inclusions, pairwise disjoint ranges,
and range coverage encode the decomposition; and the final isomorphism clause
says each component projects isomorphically to `U`. No mismatch was found.

## Second reading by J1

I opened the node statement, its source place (Stacks Project, Etale Morphisms,
Lemma 04HN), the dependency records, and the Lean file. The item-by-item match is:

- The source objects are schemes `X`, `Y`, a finite étale morphism `f : Y ⟶ X`,
  and a point `x : X`; Lean has `{X Y : Scheme.{u}}`, `f : Y ⟶ X`,
  `[IsFinite f] [Etale f]`, and `(x : X)`. `IsFinite` and `Etale` are exactly the
  Mathlib declarations recorded by the convention and étale dependency nodes.
- The source conclusion supplies an étale neighbourhood `(U,u) → (X,x)`; Lean
  introduces `U`, `g : U ⟶ X`, `u : U`, and states `Etale g ∧ g.base u = x`.
- The finite disjoint-union decomposition is rendered by a finite index type
  `J : Type u` with `[Fintype J]`, schemes `V : J → Scheme.{u}`, and maps
  `ι j : V j ⟶ pullback f g`. The pullback is the recorded
  `CategoryTheory.Limits.pullback`, with its second projection used below.
- “Open and closed subschemes” is rendered by
  `IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j)` for every `j`.
- Pairwise disjointness is rendered by disjoint ranges of the underlying maps,
  `Disjoint (Set.range (ι i).base) (Set.range (ι j).base)` when `i ≠ j`.
- Covering of the pullback is rendered by
  `∀ z, ∃ j, z ∈ Set.range (ι j).base`.
- Each component maps isomorphically to `U` via the second projection, rendered
  by `∀ j, ∃ e : V j ≅ U, e.hom = ι j ≫ pullback.snd f g`.

Every hypothesis and conclusion clause is present with the same quantifier order;
I found no mismatch and made no change to the statement or module. The empty index
case is admitted by `Fintype J`; if the pullback is empty, `J` may be empty. Empty
schemes and zero objects are not excluded, and no characteristic, nonemptiness,
cardinality, or Noetherian hypothesis is introduced. The explicit universe `u`
allows the schemes and finite index type used by the declaration.

I repeated the existing-declaration searches: LeanSearch for “finite etale morphism
of schemes is etale locally a disjoint union of copies of the base”, LeanFinder for
“finite étale morphism becomes a finite disjoint union of isomorphisms after base
change along an étale neighbourhood of a point”, Loogle for
`AlgebraicGeometry.IsFinite, AlgebraicGeometry.Etale, CategoryTheory.Limits.Sigma.desc`,
grep of Mathlib, and `rg` over `WeilConjectures/` and `lean/Sheaf/`. These found only
general or algebra-level results and no existing scheme-level declaration. The
three dependency declarations were also opened: the convention node supplies the
scheme/morphism meanings, the étale node is Mathlib `AlgebraicGeometry.Etale`, and
the fibre-product node supplies Mathlib `pullback` and `pullback.snd`.

The module compiles cleanly with `scompile.py`; its only proof is `sorry`, as
required for a stage-2 statement.
