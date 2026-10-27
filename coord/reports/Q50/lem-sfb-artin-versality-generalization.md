## Worker report

The module `Sheaf.AlgebraicGeometry.ArtinVersalityGeneralization` states
`AlgebraicGeometry.ArtinVersality.isVersalAt_of_specializes`, with its proof `sorry`.
The source read was `literature/stacks-project/artin.tex`,
`lemma-generalization-versality` (Tag 0G2K), together with
`definition-RS-star`, `definition-limit-preserving`, and `definition-versal`.
The node statement and accepted proof split are unchanged. The one added statement
dependency, the already-landed `def-sfb-stable-pointed-moduli-groupoids`, owns the
existing general CFG and algebraic-space-diagonal vocabulary used here.

Hypothesis-by-hypothesis correspondence:

- A commutative Noetherian Lambda is `(R : Type u) [CommRing R]
  [IsNoetherianRing R]`. Its base is literally `Spec (.of R)`.
- S-schemes are `Over (Spec (.of R))`, using Mathlib's `Scheme`, `Spec`, and
  over-category. Scheme/test-ring/index universe `u` is explicit; total-category
  morphism/object universes `v,w` are independent and explicit. There are no
  auto-bound variables (`set_option autoImplicit false`).
- A category fibred in groupoids on this base is
  `F : BasedCategory.{v,w} (Over (Spec (.of R)))` and
  `hFibred : CategoryTheory.IsFibredInGroupoids F`. The latter requires lifting all
  base arrows and that every arrow is strongly cartesian, including uniqueness.
  This is the existing total-category encoding of coherent pullbacks, not a
  stack-descent assumption. The big fppf site has this underlying category; no
  sheaf condition on F is assumed in the node or in the theorem.
- Representability of every isomorphism presheaf by algebraic spaces is
  `hDiagonal : HasAlgebraicSpaceDiagonal F`. This existing definition tests fibre
  products of maps from two schemes. By 2-Yoneda these are their relative
  isomorphism presheaves over the scheme product; taking two objects over the same
  scheme and its diagonal gives the node's formulation, and conversely pullback
  of the two objects to that product gives these tests. Representation uses the
  existing `AlgebraicGeometry.AlgebraicSpace`, including the fppf sheaf condition,
  representable diagonal, and surjective etale scheme atlas.
- Strong Rim--Schlessinger is `hRS : IsRimSchlessingerStar F`. Its affine scheme
  square is the contravariant form of A -> B <- B'; `b : B -> B'` is a first-order
  closed thickening, exactly a surjection of coordinate rings with square-zero
  kernel. `IsPushout a b i j` identifies P with Spec of the ring fibre product.
  The shared object `x` and the two `Lift` arrows retain the specified comparison
  over B. The required pushout of total-category arrows gives existence of the
  glued object and unique gluing of compatible arrows, hence equivalence with
  the groupoid fibre product, not merely existence of isomorphism classes.
  Conversely the fibre-product equivalence gives this total-category pushout:
  pull any target object back to P and use full faithfulness and essential
  surjectivity. Base-map uniqueness follows from the base pushout. No test
  algebra here is restricted to being local, Artinian, or finite type.
- Limit preservation is `hLimits : IsLimitPreserving F`, the conjunction of
  `ObjectsDescend`, `ArrowsDescend`, and `ArrowEqualitiesDescend`. They quantify
  over every nonempty directed preorder `I : Type u`, affine inverse system in
  `Over S`, affine cone vertex, and its actual limiting-cone property. Objects
  descend with cartesian arrows over the cone projections. Arrows descend with
  all comparison equations to a common later stage. Equality of arrows at the
  limit holds after a later stage. Thus the condition includes all three clauses
  of the node. Objects from different stages may first be transported to a
  common stage by directedness and fibredness.
- U of finite type over S is `U : Over (Spec (.of R))` with
  `[LocallyOfFiniteType U.hom] [QuasiCompact U.hom]`; `x : Object F U` lies in its
  actual fibre `Functor.Fiber F.p U`.
- The finite-type conditions for both points are `hu` and `hu₀`, each the
  conjunction of `LocallyOfFiniteType` and `QuasiCompact` for the canonical map
  `U.left.fromSpecResidueField` of that point. These use the actual residue field
  of the stalk, not a separately chosen field or point lift.
- Specialization is `hsp : u ⤳ u₀`, in precisely the direction that u₀ belongs to
  the closure of the singleton u.
- Versality at either point is `IsVersalAt F U x ...`. It quantifies over all
  Artinian local rings A',A in universe u; the surjection q has nilpotent kernel.
  A surjective `r : A -> kappa(u)` marks the residue field; `r` and `r ∘ q`
  have maximal kernels, since their targets are fields and their sources local.
  Thus q respects these residue markings automatically. The base algebra
  structures are the scheme maps `s'` and `Spec.map q ≫ s'`. The map `a` is an
  S-map, and `Spec.map r ≫ a.left = fromSpecResidueField u` is precisely reduction
  to the given point with its residue marking. The cartesian arrows `b` and `c`
  encode a reduction of y' and its specified isomorphism to the pullback of x.
  The conclusion produces the S-map `a'`, the lifted pullback identification `d`,
  the equation that a' lifts a, and `b.val ≫ d.val = c.val`, so the isomorphism
  extends the specified one. No residue coefficient-field embedding is assumed.
- Finally `hx : IsVersalAt F U x u₀` is the premise and
  `IsVersalAt F U x u` is exactly the conclusion.

Every helper is a real abbreviation or Prop-valued definition in the owning node's
module; every declaration is listed in `lean.declarations`. The helpers generalize
an interface that otherwise exists only over Spec Z, and unpack notions explicitly
written in this node. They do not assert additional lemmas. The sole theorem has
`by sorry`, with all five accepted natural-language proof steps in its docstring.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; the existing algebraic-space module uses its over-site.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, and its representability/atlas predicates,
  reached through the reused diagonal definition.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.QuasiCompact` (the declaration
  is `AlgebraicGeometry.QuasiCompact`).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.fromSpecResidueField`, and `Scheme.Hom.residueFieldMap`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`,
  `isNoetherianRing_iff`. The size-convention node is metatheoretic and is realized
  by the explicitly bound universes rather than an extra hypothesis.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `CategoryTheory.HasAlgebraicSpaceDiagonal`;
  their definitions and the space/2-fibre representation helpers were read.
- `WeilConjectures.AlgebraicGeometry.Thickening`: `IsFirstOrderThickening`, whose
  defining condition is a closed immersion with square-zero ideal sheaf.
- Proof-only import `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`:
  `exists_limit_affine_transition`, whose signature and proof docstrings were
  read. The other three theorem proof dependencies have no recorded Lean
  declaration, so there is no module of theirs to import yet. They are cited
  by DAG ID in the proof docstring and are not needed to state this theorem.

Edge cases checked before writing: the empty U has no points, so the theorem has
no spurious point assertion; the zero base ring is allowed with the same vacuity;
u = u₀ gives the reflexive implication. No characteristic, reducedness, separatedness,
or coefficient field hypothesis is imposed. The trivial extension q = identity is
included in versality; arbitrary nilpotent extensions, including non-square-zero
ones, are tested. RS* includes identity thickenings but also arbitrary square-zero
surjections, with non-Artinian algebras permitted. Limit indices have the scheme
universe, are nonempty directed preorders, and all three descent clauses are retained.
The total category keeps automorphisms and specified isomorphisms throughout.

Searches actually run:

- `msearch.py ... leanfinder "The locus where a deformation family is versal is
  stable under generalization"`: eight hits on topological generalizing maps,
  local morphism properties and flat maps; no deformation-versality theorem.
- `msearch.py ... loogle "CategoryTheory.Functor.IsFiberedInGroupoids"`: zero hits,
  unknown identifier. The project uses its own correctly named
  `CategoryTheory.IsFibredInGroupoids` atop Mathlib's fibre/cartesian API.
- `msearch.py ... grep "Versal|RimSchlessinger|LimitPreserving" AlgebraicGeometry`:
  25 unrelated results (the search also matches universal-property wording);
  no relevant Mathlib result.
- `rg` on `lean/WeilConjectures` for the item ID and
  `IsVersalAt|RSStar|RimSchlessinger`: no matching declaration.
- `rg` on `lean/Sheaf` for the item, `IsVersalAt`, `definition-versal`,
  `definition-RS-star`, `IsLimitPreserving` and fibred-groupoid vocabulary found
  `ArtinRepresentableDiagonalCriterion`, `ArtinDeformationTestCategory`,
  `StackVersalFiniteResidueExtension`, `ProperCurveVersality` and
  `StablePointedModuliGroupoids`. Their relevant full signatures/docstrings were
  read. The first's `ObjectsDescend`, `ArrowsDescend`, `ArrowEqualitiesDescend`,
  `IsLimitPreserving`, `IsVersalAt` are fixed to Spec Z. Deformation-test-category
  versality is for formal objects on Artinian tests; proper-curve versality is
  for that specific moduli problem; neither is this arbitrary CFG statement.
  The general CFG and diagonal predicates are reused from the last module.
- A DAG search for the same source labels and notions found no separate general
  definition node to duplicate. `tools/blueprint_refs.py ancestor` reports the
  item's inherited null blueprint ancestor. No new node is needed: the helpers
  unpack the inline notions of the owning node, as explicitly authorized by the
  human's missing-helper instruction.

Validation: `scompile.py Q50 lem-sfb-artin-versality-generalization ...` compiled
the single delivered module both as sandbox and library module, cleanly (4.6 s
and 5.3 s). All lines are at most 100 characters. No statement correction,
STATEMENT-DISPUTED flag, dependency repair, or new node is required.

## Second reading by Q50

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
