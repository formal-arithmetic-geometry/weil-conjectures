## Worker report

The module `Sheaf.AlgebraicGeometry.RationalDerivedScalarInvertible` states
`AlgebraicGeometry.ProEtale.rationalDerivedScalar_invertible`. Its sole proof is `sorry`.
It does not introduce another coefficient ring, module category or derived category.

Clause-by-clause reading of the node:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite normed extension E/Q_ell: `(E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
- Arbitrary scheme: `(X : Scheme.{u})`; no Noetherianity, finiteness, characteristic,
  nonemptiness or boundedness assumption.
- The actual continuous coefficient ring: `Profinite.continuousCoefficientRingObj E`
  has sections `ULift C(S,E)`, pointwise operations and precomposition. This is the
  already published universe-generalized version of `continuousMapRingObj` reexported
  by the recorded condensed-ring module. Its original source module is imported directly
  to avoid unrelated compactification imports in the reexport chain. `condensedRingObj ... X` is exactly the
  recorded inverse image `p_X^*` with its transported ring structure. In particular,
  E_X is not defined as an abstract localization or a discrete constant ring.
- Internal modules: `Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
  (condensedRingObj ... X)` is the recorded Mathlib module-object category.
- Every ordinary unbounded derived object: K has `DerivedCategory` of that category
  as its type, using the published Grothendieck size convention. This is neither a
  bounded subcategory nor a derived-complete category.
- Integer n >= 0: `(n : ℕ)` represents exactly these exponents, including zero.
- Invertibility: `IsIso ((l ^ n) • 𝟙 K)` uses the natural-number multiple in the
  derived category's actual preadditive structure.
- The inverse from the constant ell^(-n): the existential witness `t` is constrained
  on EVERY profinite S, EVERY continuous function f and EVERY s in S by
  `((t.hom.app (op S) f).down) s = ((l : E)^n)⁻¹ * f.down s`.
  This is a full specification of pointwise multiplication by that constant;
  t is not an unconstrained or arbitrary comparison map. Composing its pullback
  with the coefficient unit gives exactly the scalar section b_X.
- Complex representative: witnesses C and `e : DerivedCategory.Q.obj C ≅ K`.
  The chain map B is specified in every integer degree q by
  `lambda.inv ≫ ((eta ≫ (upperStarFromPoint X).map t) ▷ (C.X q).X) ≫ ModObj.smul`.
  It is already a morphism in the category of complexes of internal modules, so
  its linearity and commutation with the differential are part of its type.
  The last two equations say that `e.inv ≫ Q.map B ≫ e.hom` is a two-sided inverse
  to the stated multiple of the identity. Existentially binding these fully
  specified witnesses states the node's representative description without
  introducing hollow definitions or separate helper notions.

Dependencies read and used:

- Read `Sheaf.Topology.ProfiniteCondensedRing`, `Profinite.CondensedRing`, and its public
  continuous-function API. Also read `WeilConjectures.CategoryTheory.RingObjects.Condensed.
  ContinuousMap` and the reexported `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`
  and `ContinuousCoefficientCommRing`. The source `ContinuousCoefficientUniverse`
  supplies the same continuous-function construction for E in Type u and is imported
  directly, so no Type 0 restriction is imposed.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.condensedRingObj`, `coefficientRing`,
  `isCommMonObj_condensedRingObj` and `upperStarFromPoint`.
- `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`, `ModObj`, their action,
  module morphisms, regular module and forgetful functor. These declarations are
  reexported by the coefficient framework.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`, the recorded
  derived-category convention module, reexports Mathlib `DerivedCategory` and Q.
  Only these ordinary derived-category definitions are needed in the signature.
- Proof input `Sheaf.AlgebraicGeometry.ProEtalePointPullback`,
  `AlgebraicGeometry.ProEtale.sfbPullbackFromPoint` and its specification, read in full.
- Proof input `lem-sfb-derived-localization-additive` is a Mathlib leaf:
  `DerivedCategory.instAdditiveCochainComplexIntQ` and
  `DerivedCategory.instEssSurjCochainComplexIntQ` in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` (read the instances and Q).

The source read was the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-thm-sfb-rationalization-comparison/thm-sfb-extend-scalars-localization.proof.md`,
the paragraph "F inverts W". The theorem docstring carries all three expanded
proof steps of this node, including additivity of point inverse image and Q.

Edge cases checked before writing: n=0 has scalar 1 and identity inverse; K=0
still has its identity isomorphism (even though that identity is the zero map);
the empty scheme is allowed; X may have characteristic ell, since invertibility
is in E, not in O_X; no lower or upper degree bound is imposed. The common
universe u permits arbitrary sizes by choosing a common universe for E and X,
and keeps the small pro-etale site's object/morphism levels unchanged.

Searches for an existing statement, all through the prescribed msearch.py:

- LeanFinder: "Multiplication by powers of ell is invertible on unbounded derived
  internal modules over continuous p adic field coefficients": eight hits, including
  BDeRham, perfectoid/adic-related ingredients; no statement on this derived module category.
- Loogle: "CategoryTheory.Mod, IsIso, nsmul": no hits (unknown identifier IsIso).
- LeanSearch: "Multiplication by a nonzero scalar is invertible on derived internal
  module objects": eight hits, including LinearEquiv.smulOfNeZero and units actions;
  these are ordinary algebraic modules, not the required internal derived category.
- Mathlib grep: `nsmul_isIso|isIso_smul_id|scalar.*[Ii]nvertible`: six unrelated hits
  in invertible algebras/localized modules.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for scalar invertibility and
  constantScalar found unrelated coefficient comparisons and private ordinary
  fixed-ring scalar maps. The exact item id has no occurrence in WeilConjectures.
- Additional rg in the module-object/pro-etale/category-theory trees for
  `rationalDerivedScalar_invertible|nsmul.*[Ii]so|[Ii]so.*nsmul|ell.*[Ii]nvertible`
  found no exact theorem. The upstream-name index was also checked by rg with no match.
  Existing rationalization statements restrict to bounded
  constructible objects and do not state this representative inverse formula.

Import repair after the first compile: importing the recorded condensed-ring reexport
also imported bounded-constructible base change and the unrelated compactification tree.
The wrapper timed out in `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`;
its automatic server fallback found a missing published object for
`WeilConjectures.Mathlib.Algebra.Category.Ring.Basic` while compiling ProjectiveSpace.
The delivered file therefore imports the SAME continuous coefficient construction from
its smaller source module `ContinuousCoefficientUniverse`. It registers the existing
theorem `CategoryTheory.Mod.isGrothendieckAbelian` as an instance, so the actual ordinary
derived category is available without the commutative-ring reexport's unrelated imports.
The theorem applies to all internal rings; no new instance proof, coefficient definition,
category, mathematical assumption or universe restriction is introduced.
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory` supplies the
published size convention. The generic `Profinite.CondensedRing` abbreviation is not
needed for this specific continuous-ring theorem.

No statement correction, new node or dependency-record repair is needed.

Validation: the prescribed `scompile.py Q85 lem-sfb-rational-derived-scalar-invertible`
compiled the final sandbox file in 1.9 s and the actual library module in 2.0 s,
with no errors or warnings. The transported ring instance uses the framework's
published `open scoped CategoryTheory.Obj` convention. The prescribed `deliver2.py --no-push` then passed preflight and per-file
compilation (dry-run commit d8d5b81309f).

## Second reading by Q85

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
