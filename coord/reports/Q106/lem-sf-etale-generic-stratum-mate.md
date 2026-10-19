## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleGenericStratumMate` states
`AlgebraicGeometry.Etale.immersionInternalHomIso`, with its sole postponed proof `sorry`.
Its three helper definitions construct the exceptional inverse image, the actual composite
adjunction, and right-ordered evaluation from existing canonical constructions. They belong
to this node; there are no new nodes or dependency repairs. The natural-language statement,
statement dependencies and proof plan in the node are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  All schemes have universe `u`, using the established small-etale size convention.
- The chosen factorization is `{S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)` with
  `[IsClosedImmersion i] [IsOpenImmersion j]`. The composite immersion is `i ≫ j`.
  There is no extraneous separatedness, finiteness, or complement assumption.
- `Rs_!` is the dependency's `immersionLowerShriek A i j`, definitionally ordinary
  `R(lowerStar i) ⋙ D(openImmersionLowerShriek j)`. Closed direct image is exact, so
  this is the stated `j_! i_*`, on the full unbounded categories.
- `Rs^!` is `immersionUpperShriek A i j`, definitionally `D(upperStar j)` followed by
  the right adjoint of ordinary closed derived direct image. The closed-ambient
  dependency supplies its `IsLeftAdjoint` instance. `immersionLowerUpperShriekAdjunction`
  is the composite of that adjunction and the existing exact open adjunction.
- The ordinary `Rs_*` is `R((i ≫ j)_*[ModuleCat.{u + 1} A])`, not a shriek functor or
  a constructible/bounded restriction.
- The category at each T is `DerivedCategoryModule A T`, definitionally
  `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`. This is the
  constant-coefficient module-sheaf encoding used by all the immersion projection inputs.
- The tensor is the recorded `derivedTensor` with `derivedTensorHom` on morphisms.
  Internal Hom is upstream `derivedHom`, the existing closed internal Hom for precisely
  that tensor and category. The general ringed-site dependency `derivedInternalHomOfUniverses`
  supplies its Hom-complex construction and is imported through the projection module;
  there is no second definition of internal Hom here. In this coefficient encoding,
  upstream `derivedTensorHomAdjunction` directly provides evaluation.
- The existential `θ` is an isomorphism of functors from `D(S)^op × D(X)` to `D(X)`.
  The first functor sends `(op P,M)` to `RHom_X(Rs_!P,M)`; the second sends it to
  `Rs_*RHom_S(P,Rs^!M)`. A natural isomorphism records naturality in both variables,
  including contravariance in P, rather than only objectwise isomorphism existence.
- The remaining quantifiers range over every `P`, `M`, `C` and every map `f : C ⟶ Rs_*H`.
  Here `H` is written out as `((derivedHom ... S).obj (op P)).obj
  ((immersionUpperShriek A i j).obj M)`; no local notation or let hides the object.
- The left side of the equality is `(f ≫ θ.inv.app (op P,M)) ⊗ 1` followed by
  `immersionHomEvaluation`, precisely the tensor-adjoint of `θ⁻¹ ∘ f`.
  Upstream tensor-Hom uses left tensor `P ⊗ -`; `immersionHomEvaluation` converts its
  counit to the statement's `RHom(P,M) ⊗ P` convention with the canonical signed symmetry.
- The first arrow on the right side is the dependency's actual `immersionProjectionMap`.
- The next arrow is `Rs_!` applied to `derivedTensorHom` of the adjoint of f and `𝟙 P`.
  The adjoint is `.homEquiv ... .symm f` for the existing
  `derivedUpperStarLowerStarAdjunction ... (i ≫ j)`, whose left side is exactly the
  `L(upperStar (i ≫ j))` used in the canonical projection map.
- The last two arrows are `Rs_!` of evaluation and
  `(immersionLowerUpperShriekAdjunction A i j).counit.app M`. Thus every arrow, its
  orientation, and the terminal exceptional counit match the displayed node formula.
- No boundedness or constructibility predicates occur. The inverse images are the
  exact constant-coefficient inverse images from the dependency, identified with their
  total left derived functors; `D(j^*)` in the exceptional functor acts termwise.

Dependency declarations read and used (directly or through the projection module):

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the recorded torsion definition
  and documentation identifying `Etale.DerivedCategoryModule`; the latter comes from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`; general ringed-site Hom-complex
  localization, already public-imported by the projection module.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact` (its full signature was also read
  in the local identically named pre-upsync Sheaf module).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.OpenClosedRecollement`:
  `Etale.exists_functorial_distTriang_openClosed`; its exact open functor is upstream
  `openImmersionLowerShriek`, and the used open adjunction is
  `Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction` from
  `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek`.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`.
- `Sheaf.AlgebraicGeometry.EtaleGenericImmersionProjection`:
  `Etale.immersionLowerShriek`, `Etale.immersionProjectionMap`,
  `Etale.immersionProjectionFormula` and the canonical `derivedTensorSymmetry` it imports.
- The proof-only imports are the recorded ringed closed symmetric-monoidal theorem,
  K-injective total derived theorem, Mathlib K-injective Hom bijection, preservation of
  K-injectives by right adjoints, and homotopy-category termwise adjunction.
  The projection import already imports the K-injective existence and open exactness inputs.

Sources opened: Stacks `sites-cohomology.tex`, lemma-internal-hom (08J9), and the current
main-20261015 blueprint `sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/`
`lem-weil-stratum-ambient-hom.md` and its proof. The latter supplies the immersion-specific
Yoneda adjunction chain; Stacks 08J9 supplies the tensor-Hom ingredient, not by itself
an assertion about immersion exceptional inverse image.

Edge cases checked mathematically before and after writing:

- Identity factorization: the composite adjunction and projection reduce canonically
  to the identity case, and the formula is the ordinary tensor-Hom evaluation formula.
- Purely open or purely closed factorization: one factor is the identity and the other
  gives the usual corresponding Hom/exceptional-adjunction formula.
- Empty S and the zero coefficient ring: the module category on S, respectively every
  coefficient category, is zero; both Hom objects and all displayed maps have the expected
  unique zero values. No Nonempty, nonzero-ring, or positive-dimension condition excludes them.
- Zero P, zero M, zero test C, arbitrary shifts and unbounded objects: every expression
  remains typed in the ordinary unbounded category; there are no amplitude restrictions.
- The tensor factor order was checked: evaluation's input is H tensor P, not P tensor H;
  the explicit symmetry accounts for the upstream left-tensor adjunction and its signs.

Searches for an existing statement:

- `msearch.py ... leanfinder "Internal Hom extension by zero immersion exceptional inverse
  image evaluation counit"`: 8 hits, chiefly scheme module restriction adjunctions and
  condensed internal-Hom point formulas; none gives this etale immersion comparison.
- `msearch.py ... loogle '"Adjunction", "internalHom"'`: two hits,
  `MonoidalClosed.internalHomAdjunction₂` and its unary-adjunction identity; reusable
  categorical ingredients, not the immersion statement.
- `msearch.py ... grep '(internalHom.*(counit|lowerShriek)|(counit|lowerShriek).*internalHom)'`:
  zero hits in Mathlib.
- `rg` in upstream `WeilConjectures`, local `lean/Sheaf`, and Mathlib for the node id,
  stratum/immersion Hom and all four proposed declaration names found no duplicate.
- Read upstream `Etale.Derived.TensorHom.derivedHomRightDerivedLowerShriekIso` in full:
  it uses the compactification shriek functor, assumes that functor's adjunction and a
  projection isomorphism, and does not state this factorization-specific normalized formula.
  Its `derivedHom` and tensor-Hom adjunction are reused; its different shriek object is not
  substituted for the specified ordinary closed/open composite.
- Live source was read with `scompile.py --source
  WeilConjectures.AlgebraicGeometry.DerivedCategories` because that migrated module is
  absent from the older slopmaster2 tree. This verified the current coefficient convention.

Validation: `scompile.py Q106 lem-sf-etale-generic-stratum-mate <module>` compiled both
sandbox and delivered module successfully (9.6 s and 9.9 s), with no warnings or errors.
No node faults or statement disputes were found. Delivery preflight is recorded below.

## Second reading by Q106

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
