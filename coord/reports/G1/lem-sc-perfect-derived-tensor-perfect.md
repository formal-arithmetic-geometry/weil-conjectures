## Reviewer fix (R-pdt)

The delivery corrected the node's statement to "there exists T, a representative-based derived
tensor of K and L, which is perfect" and added a new definition node def-pc-derived-tensor-object
(`IsDerivedTensor`, a K-flat-representative relation, with a file-local `MonoidalCategory`
instance). Both are undone:

- `--revert-statement`: the base statement ("K ⊗^L L is perfect") is expressible without a
  derived tensor bifunctor, through K-flat representatives exactly as landed
  def-pc-derived-tensor-cohomology-vanishes (E1 a3ac25177), lem-pc-derived-pullback-tensor-qcoh
  (C1 089e8d1b6) and lem-pc-derived-pullback-tensor-product (K1 60a01cfa3) do. The existential
  form was also weaker than the source (it asserts perfectness of one chosen representative
  tensor, so a citer would need the independence of the representatives to use it).
- `--drop-nodes def-pc-derived-tensor-object` and its module DerivedTensorObject.lean: the lead's
  rule (C1/K1 drops of def-pc-scheme-derived-tensor, def-pc-scheme-derived-tensor-product) is no
  derived-tensor definition on `schemeDerivedCategory`; derived tensor is inlined by K-flat
  representatives.
- The theorem is now `AlgebraicGeometry.perfect_derivedTensor`: for `K L` perfect and K-flat
  complexes `P N` with `eP : Q(P) ≅ K`, `eN : Q(N) ≅ L`, `Scheme.IsPerfect X (Q(Tot(P ⊗ N)))`,
  the tensor being `SheafOfModules.monoidalCategory X.sheaf` passed explicitly to `curriedTensor`
  (no file-local instance). Since K-flat resolutions exist (lem-pc-kflat-resolution) this covers
  every pair K, L and is Stacks 09J5 for schemes.

Compiled: `SHEAF_GROUP=L tools/lean_file.sh lean/.sandbox/L/PerfectDerivedTensor.lean`, clean.
## Worker report

The module defines `AlgebraicGeometry.IsDerivedTensor`, the representative-based
meaning of a derived tensor product on the pinned library, and states
`AlgebraicGeometry.perfect_of_isDerivedTensor`. The item's statement was corrected
because the source notation `K ⊗ᴸ L` has no bifunctor in the pinned library; the
correction writes its K-flat representative meaning explicitly and retains the
perfectness conclusion.

The theorem binds a scheme `X`, derived-category instances on `X` and every open,
objects `K,L`, and hypotheses `Scheme.IsPerfect X K` and `Scheme.IsPerfect X L`.
Its conclusion is an existential `T`, a conjunction saying `IsDerivedTensor X K L T`,
and `Scheme.IsPerfect X T`. `IsDerivedTensor` renders the representative clauses
by complexes `P,N`, isomorphisms from their quotient objects to `K,L`, and equality
of `T` with the quotient of `CochainComplex.mapBifunctor P N (curriedTensor _)`.

Dependencies used: `Sheaf.AlgebraicGeometry.PerfectComplex` (`AlgebraicGeometry.Scheme.IsPerfect`),
`Sheaf.AlgebraicGeometry.DerivedCategory` (`AlgebraicGeometry.schemeDerivedCategory`),
and `Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct` for the existing monoidal
category setup and `CochainComplex.mapBifunctor`.

Edge cases checked: arbitrary schemes including empty schemes; empty and zero
complex terms are allowed by the existing `IsPerfect` definition; no finiteness,
separatedness, or nonemptiness hypotheses were added.

Searches: grep and repository `rg` found no scheme-level derived tensor bifunctor;
existing `DerivedPullbackTensorProduct.lean` explicitly records that no such
bifunctor exists. Loogle/LeanFinder searches recorded in the parent node found no
match. The new definition node records the direct grep search.

## Statement corrected

The citer `lem-sc-affine-perfect-map-lift` still holds: it needs that the tensor
object used there is perfect, and the corrected statement provides the corresponding
representative-based derived tensor object and perfectness conclusion.

## New nodes

`def-pc-derived-tensor-object` supplies the missing representative-based notion.

## Earlier second reading (a previous round; superseded)

The representative relation, universe binders, imports, dependency uses, and corrected citer were checked against the source and compiled together with both modules.

## Second reading by G1

I read the corrected node, its source place (Stacks Cohomology of Sheaves, Lemma 09J5,
Tag 09J5), the dependency node signatures, and both delivered modules.

The statement's objects and clauses match as follows:

- `X` is rendered by `X : Scheme.{uT}` in
  `perfect_of_isDerivedTensor`; this is the Mathlib scheme of `def-pc-scheme`.
- The derived-category structure on `D(𝒪_X)` is rendered by
  `[HasDerivedCategory.{wT} (SheafOfModules.{uT} (moduleRings X.toRingedSpace))]`,
  using `schemeDerivedCategory` from `def-pc-derived-category`.
- The derived-category structures on every open `U : X.Opens` are rendered by the
  explicit universal-open instance binder. This is required by `Scheme.IsPerfect`
  from `def-pc-perfect-complex` and does not add a geometric hypothesis.
- `K` and `L` are rendered as `(K L : schemeDerivedCategory X)`, and their
  perfectness hypotheses are exactly `(hK : Scheme.IsPerfect X K)` and
  `(hL : Scheme.IsPerfect X L)`.
- The existential conclusion is exactly `∃ T : schemeDerivedCategory X`.
  Its first conjunct is `IsDerivedTensor X K L T`, whose definition introduces
  complexes `P,N`, requires both `CochainComplex.IsKFlat (R := X.sheaf) P` and
  `... N`, requires nonempty isomorphisms `Q.obj P ≅ K` and `Q.obj N ≅ L`, and
  identifies `T` with `Q.obj (CochainComplex.mapBifunctor P N (curriedTensor _))`.
  Its second conjunct is exactly `Scheme.IsPerfect X T`.

The K-flat requirements were missing from the worker's representative relation.
I added them to `IsDerivedTensor`; this is required by the source's derived tensor
construction and by the neighboring `DerivedPullbackTensorProduct` module. I also
updated both node `lean.statement` records verbatim to the resulting declarations.
No other hypotheses or clauses were changed.

Edge cases checked: `X` is unrestricted (including empty schemes), `P` and `N` may
be zero or empty complexes, and no nonempty index, finiteness, separatedness,
Noetherian, characteristic, or universe restriction beyond the displayed universe
parameters is introduced. The open-instance binder ranges over all opens, including
`⊤` and `⊥`.

Searches: `rg` over `lean/Sheaf`, `WeilConjectures`, and the pinned Mathlib found no
scheme-level derived tensor bifunctor or perfect-tensor theorem; the existing
`DerivedPullbackTensorProduct.lean` explicitly says that no such bifunctor exists.
Loogle/LeanFinder searches recorded in the node found no usable declaration.

The corrected representative relation now states the source notion faithfully,
including K-flat representatives. The modules compile together with
`scompile.py` with no warnings or errors.
