## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.SmoothCotangentGenericIsomorphism` states
`AlgebraicGeometry.Scheme.Hom.smooth_curve_cotangent_generic_isomorphism`, with its proof
` sorry`. There are no helper declarations or new definitions. The node is unchanged except
for its `lean` record. No statement correction or disputed assertion is needed.

Read Stacks `curves.tex`, Tag 0C1C, `lemma-generically-etale`, proof paragraph 1;
`morphisms.tex`, Tags 02G1 (`lemma-smooth-omega-finite-locally-free`) and 02G2
(`definition-smooth-relative-dimension`); and the current blueprint
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-lem-wft-finite-map/lem-a1-finite-map-curve.proof.md`,
paragraph 3. The lemma isolates the rank-one and generic-point argument; it does not assert
that an arbitrary h is dominant or etale.

Hypotheses and clauses, in statement order:

- The field is `{k : Type u} [Field k]`; the two schemes are `{X Y : Scheme.{u}}` with
  explicit structure morphisms `pX` and `pY` to `Spec (.of k)`.
- `[IsIntegralCurve pX]` and `[IsIntegralCurve pY]` use the recorded curve definition:
  integral, separated, finite type (locally finite type and quasi-compact), dimension one.
  `[Smooth pX]` and `[Smooth pY]` add precisely the smoothness assumption.
- `(h : X ⟶ Y) (_w : h ≫ pY = pX)` is an arbitrary morphism over k. The underscore merely
  suppresses an unused-binder warning: the triangle equation is retained in the signature.
- Each of the first two conjunctions quantifies over opens of the corresponding scheme,
  assumes `IsAffineOpen U` and `(U : Set X).Nonempty` (respectively Y), and concludes
  `topologicalKrullDim (U : Set X) = 1` (respectively Y).
- `SmoothOfRelativeDimension 1 pX ∧ SmoothOfRelativeDimension 1 pY` renders the two
  structure morphisms' relative dimension, as a conclusion rather than an assumption.
- `((Scheme.Modules.tensorPullback h).obj pY.relativeDifferentials).IsInvertible` and
  `pX.relativeDifferentials.IsInvertible` assert exactly the two local rank-one
  trivializations, using the recorded definition of invertibility.
- The quantifier `a` ranges over every module-sheaf morphism from that actual tensor
  pullback to the actual source differential sheaf. No canonical-differential-only
  restriction is made. For every `η : X` satisfying `IsGenericPoint η Set.univ`, the
  first iff equates `a ≠ 0` with the nonzero linear stalk map induced by
  `PresheafOfModules.moduleStalkFunctor X.ringCatSheaf.obj η` on `a.val`.
  The second iff equates that same nonzero stalk map with existence of a nonempty affine
  open V on which `(Scheme.Modules.restrictFunctor V.ι).map a` is an isomorphism. The two
  iffs together give exactly the three-way equivalence. Integral schemes are sober and
  irreducible, so the generic point exists and is unique; this quantifier is not vacuous.
- The last clause quantifies over nonempty opens W and every `x : W`, equivalently a point
  of X belonging to W. It takes the stalk of `pX.relativeDifferentials.restrict W.ι`
  with `RingedSpace.moduleStalkFunctor`. `Nontrivial` states nonvanishing. The displayed
  `Nonempty` module isomorphism identifies it with the free module of rank one on
  `X.presheaf.stalk (W.ι x)`. Its left side uses `ModuleCat.restrictScalars` along
  `(W.ι.stalkMap x).hom`, the canonical identification of the ambient ring stalk with
  the open-subscheme ring stalk. Thus freeness is over the requested ambient O_{X,x},
  with the genuine scalar action, rather than merely an abstract additive equivalence.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`:
  `AlgebraicGeometry.IsVariety`, `AlgebraicGeometry.IsIntegralCurve` (full class fields).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` and
  `AlgebraicGeometry.SmoothOfRelativeDimension` (full class signatures and chart conditions).
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`; the proof plan also uses
  `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` imports the actual construction
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` in
  `WeilConjectures.AlgebraicGeometry.TensorPullback`. Its objects use inverse image,
  tensor extension of scalars and sheafification. The normalized adjunction is not needed
  as an extra hypothesis.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, with `exists_isoUnit`; its
  `IsInvertible.pullback` is a proof dependency.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, defined by closure of a singleton.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`, including its stalk-map construction. This is
  the dependency's recorded declaration and is used directly for the generic map.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor` bundles the same sheaf stalks over
  the commutative structure stalk ring, as recommended in the dependency's note.

The stated proof-dependency modules are imported. Additional proof-only Mathlib imports
provide integral germ injections/function-field stalks, basic-open unit loci, the prime
spectrum basic-open basis, and affine principal opens/ideal-sheaf closed subschemes. The
module docstring expands each of the node's six proof steps, including the affine shrinking
and both directions of the generic criterion.

Edge checks before drafting:

- Empty schemes cannot satisfy `IsIntegralCurve`; empty affine opens are explicitly
  excluded from the dimension conclusions. Empty W is explicitly excluded as in the node.
- For a = 0 all three equivalent conditions are false: the rank-one generic stalk is a
  nonzero vector space. In particular a zero map is not an isomorphism on a nonempty open.
- For h the identity and a the identity, all three conditions hold. Multiplication by t
  on the affine line is nonzero and becomes invertible on D(t), without being globally
  invertible; hence the conclusion has the intended generic, rather than global, scope.
- Constant h is allowed and still pulls a line bundle back to a line bundle. The theorem
  quantifies over arbitrary a, so it never asserts that dh is nonzero for such h.
- Frobenius in characteristic p has zero differential; this is compatible with the a = 0
  case. No perfect-field, characteristic-zero, projective or nonconstant hypothesis occurs.
- x can be the generic point and W can be any nonempty open, including X. No closed-point
  restriction is present. All universes and variables are explicitly bound; no extra size
  constraint is imposed on the field beyond the schemes' usual common universe.

Searches actually run using the prescribed msearch.py wrapper:

- LeanFinder: "Smooth integral curves have rank one cotangent sheaves and a nonzero map
  between line bundles is invertible on a nonempty affine open". Eight hits, including
  smooth charts and the smooth-locus formula; none states the full lemma.
- Loogle: `KaehlerDifferential, Module.Free`. Seven hits, including standard-smooth
  freeness and polynomial differentials; none supplies this sheaf/generic criterion.
- Mathlib grep in AlgebraicGeometry:
  `(genericPoint|generic).*(isIso|IsIso)|relativeDifferentials.*rank`. Zero hits.
- LeanSearch: "The cotangent sheaf of a smooth integral curve is invertible and a nonzero
  line bundle map is an isomorphism on a nonempty open". Eight hits about cotangent algebra
  and open immersions, with no match for the statement.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for cotangent-generic names,
  this exact node id, `nonzero.*generic` and `ne_zero.*generic`. Related hits include the
  parent `NonzeroDifferentialGenericallyEtale` and generic ideal/stalk results, not this
  full statement. Read the parent's full signature: it concerns only the canonical
  differential and existence of an etale open, not arbitrary module-sheaf maps. The exact
  node-id search in upstream WeilConjectures also finds no existing declaration.

Validation: the complete delivered file compiled via scompile.py Q83 with no errors or
unexpected warnings, as both sandbox and library module (1.9 s and 2.0 s respectively).

## Second reading by Q83

Performed a separate clause-by-clause reread of the finished node copy, source and Lean
signature. The explicit triangle `_w` is present even though the resulting line-bundle
assertion does not use it internally. Neither relative-dimension conclusion is assumed.
The final stalk is taken after restriction to W, with its scalar structure transported
back along the actual stalk map, and includes nonvanishing. The generic equivalences
quantify over every linear a, not merely dh; V is required to be both nonempty and affine.
No mismatch was found and no node correction was made. This is a worker self-check;
the independent mathematical reading is the maintainer's delivery review, as specified in
the dispatch brief. No independent agent review is claimed.
