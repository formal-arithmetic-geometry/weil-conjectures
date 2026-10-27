## Worker report

The item is stated by `AlgebraicGeometry.strictBirationalGroupLaw_realization` in
`Sheaf.AlgebraicGeometry.StrictBirationalLawRealization`. Its only proof is `sorry`.
The added definition module `Sheaf.AlgebraicGeometry.StrictBirationalGroupLaw` contains
real structure data and predicates, with no postponed proofs and no axioms.
The item's natural-language statement, proof, and proof dependencies are unchanged;
its statement dependencies gain `def-sfb-strict-birational-group-law`.

Source read: the BLR primary scan linked in the node, PDF pages 118-124 and 163-164:
5.1 Definitions 1-2 and Proposition 3; 5.2 Definition 1 and Theorem 3;
6.5 Corollary 2 and its descent argument. The strict definition requires all three
opens to be dense for both projections. The corollary covers arbitrary fields and
DVRs; finite type is inherited from 5.2 Theorem 3 and the construction used by its
proof. The local literature PDF is still absent; this delivery reads the online
primary scan, and makes no change to the read-only literature directory.

Hypotheses and clauses, in the order of the item:

- A field or DVR B: `(B : Type u) [CommRing B] [IsDomain B]` and
  `hB : IsField B ∨ IsDiscreteValuationRing B`. The domain instance is a common
  consequence of both alternatives, not a new mathematical restriction. `IsField`
  expresses fieldhood of the fixed commutative ring without choosing new operations.
- S = Spec B and X an S-scheme: `X : Over (Spec (CommRingCat.of B))`.
  All maps in `Over S` commute with structure maps; no arbitrary maps replace them.
- Smoothness: `[Smooth X.hom]`; separatedness: `[IsSeparated X.hom]`, whose
  Mathlib class is exactly closed immersion of `pullback.diagonal X.hom`;
  finite type: `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`.
- Every fibre nonempty: `hne : ∀ s : Spec (CommRingCat.of B),
  Nonempty (X.hom.fiber s)`. No section or rational point is assumed.
- Relative products: `X ⊗ X` is Mathlib's Cartesian monoidal product on `Over S`;
  its underlying scheme is `pullback X.hom X.hom`, with `fst` and `snd` its projections.
  Fibres are `Scheme.Hom.fiber`, and their embeddings are `Scheme.Hom.fiberι`.
- S-density: `IsFibrewiseDense f A := ∀ s, Dense ((f.fiberι s) ⁻¹' A)`.
  This is topological density on the scheme-theoretic fibre, not density merely on
  rational points, generic density, or scheme-theoretic dominance on the total space.
- The S-rational law with strictness: `m : StrictBirationalGroupLaw X` is given
  by an arbitrary chosen strict representative. Its fields are the domain over S,
  `inclusion : domain ⟶ X ⊗ X`, and `mul : domain ⟶ X`. The inclusion is an open
  immersion. The two actual maps are `lift (inclusion ≫ fst X X) mul` and
  `lift mul (inclusion ≫ snd X X)`; their open-immersion fields encode precisely
  isomorphisms D ≅ V and D ≅ W onto their open images, with V and W not chosen
  independently of these maps. All three images have density fields for each
  projection, giving the six required assertions. They imply S-density of the
  domain and both images here because X is smooth with nonempty fibres. Thus
  these charts represent the S-rational law and its two S-birational translations.
  No quotient or maximal domain needs to be constructed to quantify over every
  strict law: the theorem is stated for every representative chart of every law.
- Associativity wherever both composites exist: the `assoc` field quantifies over
  every `T : Over S` and `a b c d : T ⟶ domain`. The five premise equations say,
  respectively, that a and b share y, that c has coordinates (ma,z), and that d has
  coordinates (x,mb). Its conclusion `c ≫ mul = d ≫ mul` is (xy)z = x(yz).
  Testing all schemes, including nonreduced ones, asserts equality of morphisms.
- Existence of H and i: the first conjunct is `∃ H : Grp (Over S), ∃ i : X ⟶ H.X,
  m.Realizes H i`. A Mathlib group object provides the multiplication, inverse and
  unit with all associativity, unit and inverse diagrams; it does not assert
  commutativity, affineness, connectedness or properness.
- Smooth separated finite-type H: the first four clauses of `Realizes` are
  `Smooth H.X.hom`, `IsSeparated H.X.hom`, `LocallyOfFiniteType H.X.hom`,
  and `QuasiCompact H.X.hom`.
- Dense open embedding of the whole X, without shrinking: the next two clauses
  are `IsOpenImmersion i.left` and `IsFibrewiseDense H.X.hom (Set.range i.left)`.
- Multiplication restricts to m: the final clause is
  `m.mul ≫ i = m.inclusion ≫ (i ⊗ₘ i) ≫ μ[H.X]`, an equality of S-morphisms on
  all of the supplied domain D. For smooth X and separated H, equality of the
  rational laws is equivalent to this equality on the representative's domain.
- Any two such pairs: the second conjunct universally quantifies over arbitrary
  `H₁ H₂`, `i₁ i₂`, with `m.Realizes H₁ i₁` and `m.Realizes H₂ i₂`. There is no
  dependence on the witness chosen for the existence conjunct.
- Unique S-group isomorphism extending the chart identification:
  `∃! a : H₁ ≅ H₂, i₁ ≫ a.hom.hom.hom = i₂`. Here the three `hom` projections
  extract the underlying `Over S` morphism from the group isomorphism. Its inverse
  is also a group morphism because this is an isomorphism in `Grp (Over S)`.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field`, through the fixed-ring predicate `IsField`;
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`;
  `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over` and bundled `CategoryTheory.Over`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the dependency's
  recorded base-change conventions. As its lean.note explicitly instructs,
  scheme base changes use `Limits.pullback`, rather than its module-pullback def.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `Scheme.Hom.fiberι`;
  `Mathlib.AlgebraicGeometry.Pullbacks`: the Cartesian monoidal instance on `Over S`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, recorded by
  `def-sc-group-scheme`, and its bundled category `Grp`; the same group-object
  construction applies to `Over S`. `MonObj.mul` and `Grp` morphisms are reused.

The definition node cites the existing scheme-over-base and group-scheme nodes;
there is no replacement of their notions. The item retains all original dependencies.
Imports for recorded proof dependencies are included without `public`: strict
henselization triples, faithful flatness, strict-henselization DVR, descent datum,
invariant-open descent and morphism descent. The DVR module currently contains a
withdrawn declaration in its local source, so the import is only a retained proof
plan entry; the item does not use that unavailable declaration in its signature.
Other proof dependencies have no recorded module and are named in the six-step
proof docstring rather than re-stated. No import cycle was introduced.

Edge cases checked before finalizing:

- Empty X is excluded exactly by nonempty fibres over the nonzero field/DVR base.
  No emptiness is hidden by a generic-point-only density test.
- Reducible or disconnected X and H, dimension zero, finite fields and imperfect
  fields are permitted; no integrality, connectedness, characteristic or
  algebraic-closedness hypothesis occurs on them.
- The identity need not belong to X; the conclusion puts it in H. No section of X
  is required. The chart D need not contain the diagonal or all of X ×_S X.
- The density test on a fibre is the dense preimage under its canonical inclusion;
  an empty fibre would make that one condition vacuous, while `hne` prevents this
  for the input X. The six projection conditions are retained independently.
- The law may have many representatives. Changing its chart changes no asserted
  rational multiplication; the realization equation is checked on the chosen
  chart, and uniqueness concerns the resulting group, not equality of chart data.
- Associativity uses all scheme-valued points, not only field-valued points. Its
  five equations permit exactly the common domain and never assume either
  undefined iterated product exists.
- All schemes, fibres, products, and tests use universe u. In particular the test
  schemes range over the same size as X, so the universal common-domain scheme
  itself is allowed. There is no smaller independent test universe.

Searches actually run:

- msearch LeanFinder: "A strict birational group law on a smooth scheme over a
  field or discrete valuation ring has a unique group scheme realization".
  Eight hits: smooth-dimension multiplicativity and unrelated Weierstrass groups
  and scheme constructors; no realization or strict-law declaration.
- msearch LeanSearch: "strict birational group law with fibrewise dense translation
  charts on a scheme over a base". Eight hits include `Scheme.RationalMap.dense_domain`,
  `Scheme.PartialMap`, `IsOver` and `IsDominant`. Read the current
  `Mathlib/AlgebraicGeometry/Birational/RationalMap.lean`: its `PartialMap` assumes
  density in the total scheme. It supplies neither the six relative density
  conditions nor the translation-chart data. It therefore does not duplicate this
  strict-law structure. The old RationalMap module path is deprecated and unused.
- msearch Loogle: `AlgebraicGeometry.Scheme, GrpObj, IsOpenImmersion` returned zero
  hits with "unknown identifier 'GrpObj'"; this is an indexing limitation, not
  evidence of absence. Read the actual `GrpObj` source and reused it.
- msearch Mathlib grep: `StrictBirational|strict birational|birational.*law|[Ff]ib[er]+wiseDense`
  in AlgebraicGeometry: zero hits.
- rg of project `lean/WeilConjectures` and `lean/Sheaf` for strict/birational-law
  and fibrewise-density names: no matching definition or theorem. Broader density
  searches found only other geometric statements, not a predicate for this notion.
  Searching `lem-sfb-strict-birational-law-realization` in upstream Lean found no hit.
- DAG title/statement search found the existing strict-law lemmas but no definition
  node, and found `def-sc-group-scheme`, which is cited by the new node.
  `tools/blueprint_refs.py search 'strict birational'` returned zero blueprint nodes.
  `tools/blueprint_refs.py ancestor lem-sfb-strict-birational-law-realization` returned
  `None`; the new node preserves this ancestry and prepends the item to its via chain.

Validation: both delivered modules compiled, separately in dependency order, through
`scompile.py` against the server's live published build. No errors or non-sorry
warnings. All variables and universes are explicit. No statement correction or
STATEMENT-DISPUTED issue was needed.

## New nodes

`def-sfb-strict-birational-group-law` supplies the representative-level notion used
in the item's own inline definition: fibrewise density, strict translation charts,
associativity on the common domain, and the predicate of being a group realization.
The source is BLR 5.1 Definitions 1-2, 5.2 Definition 1, and 6.5 Corollary 2.
The LeanSearch, LeanFinder and Mathlib grep outputs are recorded verbatim in its
mathlib_searches; project, DAG and blueprint searches are described above. Mathlib's
absolute rational maps do not encode this relative strict chart, while group objects,
open immersions and scheme fibres are all reused from their existing declarations.
The new definition node adds no theorem and has no postponed proof or hollow data.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
