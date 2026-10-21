## Worker report

Module: `Sheaf.Paper.BoundaryQDefiningCompositeComparison`.
Main declaration:
`AlgebraicGeometry.ProEtale.BoundaryComparisonOfCoefficients.boundary_q_defining_composite_comparison`.
The theorem is stated with `sorry`. The three map helpers are real definitions
of the displayed s, r and t_e; t_p is expanded directly in the conclusion. `BoundaryDefiningCompositeComparison` is a real Prop-valued definition packaging exactly
all the node's quantified inputs, hypotheses, square and conclusion at a generic existing
coefficient interface. The theorem specializes that predicate to ModuleCat A, under the
finite-ring and proper/quasi-compact geometric assumptions. The predicate adds no theorem
hypothesis: all its coefficient instances are synthesized in the specialization.
Nothing is proved.

Source read: main-20261015 blueprint,
`sec-six-functors/sk-thm-sf-pf-proetale/thm-sf-pf-proetale.proof.md`, entire comparison
paragraph, and this node's five-step agent-written expansion. That paragraph says that
exact comparison commutes with inverse image and derived tensor and identifies projection
maps. The node isolates the formal inverse-projection/symmetry/final-arrow calculation
conditional on its displayed square; it asserts no exceptional-adjoint existence.

Hypotheses and clauses, matched individually:

- Finite commutative A: `(A : Type (u + 1)) [CommRing A] [Finite A]`. This is the
  established coefficient universe for Scheme.{u}; every finite ring has such a lift.
  No nontriviality, characteristic, invertibility or field hypothesis is imposed.
- Schemes Z,T and proper i: `{Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i]`.
  Quasi-compactness of T is `[CompactSpace T]`, the topological meaning for a scheme.
- Ordinary constant-A module categories: the theorem specializes the generic helper
  formulas to `ModuleCat.{u + 1} A`. On the etale site the derived category is precisely
  `Etale.DerivedCategoryModule A W`; on the pro-etale site we use the equivalent fixed-ring
  presentation `DerivedCategory (Sheaf (Scheme.ProEt.topology W) (ModuleCat A))` already
  used by `siteComparisonDerivedPullbackPlus`. The finite coefficient node's
  `finiteCoefficientRealization` is the canonical exact equivalence to modules over
  its sheafified continuous-function coefficient ring; no new category is defined.
- C_W: `BoundaryComparison.comparison (ModuleCat A) W`, definitionally
  `(comparisonUpperStar (ModuleCat A) W).mapDerivedCategory`, the exact termwise
  comparison. Its bounded-below restriction is `siteComparisonDerivedPullbackPlus`.
- F_e,F_p: `BoundaryComparison.etaleImage` and `proetaleImage`, definitionally the
  ordinary lower-star functors' `rightDerivedFunctor`. No exceptional functor is bound.
- c: the component of the existing
  `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`. This is the canonical
  K-flat tensor comparison for the exact inverse image, not a supplied arbitrary iso.
- rho: `BoundaryComparison.pullbackSquare`; its orientation is
  C_T followed by Li_p^* isomorphic to Li_e^* followed by C_Z. Its definition explicitly
  conjugates `comparisonUpperStarCompUpperStarIso` by the canonical
  `leftDerivedFunctorIsoMapDerivedCategory` identifications for both exact inverse
  images. Thus Li^* is the ordinary inverse image i^* in these formulas.
- Signed symmetry: `β_` from the existing `DerivedCategory.braidedCategory` instance is
  used directly. Its source is
  `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided`; the module docstring
  explicitly describes the cochain Koszul sign (-1)^(pq), descent to the homotopy
  category and then to the derived tensor by its universal property. This is exactly
  the node's specified signed symmetry. No symmetry presentation, free swap or
  additional coherence condition is quantified.
- Natural comparison η: the binder is the natural isomorphism
  `comparison Z ⋙ proetaleImage i ≅ etaleImage i ⋙ comparison T`, on the whole
  unbounded categories as the node requests. It is not restricted to a particular mate.
- Canonical projection transformations: the etale expression uses the exact
  `Etale.rightDerivedLowerStarProjectionMap` component; the pro-etale expression uses
  `ProEtale.rightDerivedLowerStarProjectionMap`. Both are the ordinary-adjunction
  counit-defined projection map. No arbitrary projection component is supplied.
- B,M,Y,B': the four `DerivedCategory.Plus` binders specify exactly the four input
  bounded-below objects in the corresponding sites. `.obj` regards them as ambient
  derived objects. Intermediate derived tensors are never assumed bounded below.
- v: the iso from `(comparison Z).obj B.obj` to `B'.obj`.
- a_e,a_p: binders `ae`, `ap` have exactly targets Y.obj and C_T(Y.obj).
- Compatibility of final arrows: `_ha` is F_p(v.hom) followed by ap equals η_B
  followed by C_T(ae), exactly a_p o F_p(v) = C_T(a_e) o η_B.
- s: `boundaryDefiningSourceIso` is the canonical c_Z followed by rho inverse in the
  first variable and v in the second variable. Bifunctoriality identifies this with
  (rho inverse tensor v) o c_Z, without choosing any new monoidal comparison.
- r: `boundaryDefiningTargetIso` is the canonical c_Z followed by rho inverse in the
  second variable and v in the first variable. Bifunctoriality gives exactly
  (v tensor rho inverse) o c_Z. Both tensor orders are retained explicitly.
- The two IsIso binders apply only to π_e(B,M) and π_p(B',C_TM). There is no
  constructibility or finite-Tor-amplitude condition on B, and no projection-formula
  theorem is assumed. IsIso supplies the categorical inverses written `inv`.
- Projection square: `_hπ` reads from left to right using Lean's `≫`: tensor of F_p(v)
  with identity, then π_p, then F_p(r.inv), then η_(B tensor i_e^*M). The right side
  is η_B tensor identity, then c_T inverse, then C_T(π_e), exactly the node's square.
- t_e: `boundaryEtaleDefiningComposite` is F_e(sigma_(i_e^*M,B)), then inverse π_e,
  then sigma_(F_eB,M), then tensoring ae with identity in the first slot.
- t_p: the right side of the conclusion after F_p(s.hom) spells out F_p of the
  pro-etale Koszul braiding on (i_p^*C_TM,B'), inverse π_p(B',C_TM), the pro-etale
  Koszul braiding on (F_pB',C_TM), and tensoring ap with identity on C_TM.
  It uses the arbitrary compatible ap, with no exceptional counit specialization.
- Conclusion: the left side is η_(i_e^*M tensor B) ≫ C_T(t_e) ≫ c_(T;M,Y). The
  right side is F_p(s.hom) ≫ t_p. This is exactly the displayed conclusion with the
  node's right-to-left composition translated into Lean's left-to-right convention.
- The three helpers are generic in the coefficient category to avoid unfolding
  specialized module-category instance terms inside their definitions. The theorem
  fixes that category to ModuleCat A; all helper and predicate instance requirements are discharged
  by the existing module and site instances and are not extra theorem hypotheses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`; Mathlib `DerivedCategory.Plus`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, `finiteCoefficientRealization`,
  `finiteCoefficientComparison`, `finiteCoefficientDerivedComparison` and the
  realization equivalence. The fixed-ring presentation is the one the recorded
  derived comparison interface exposes; it is not a replacement coefficient system.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus` and its underlying termwise comparison.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `supportSiteComparisonCoefficientPullbackIso` and
  `supportSiteComparison_pullback_coherent`; the existing `pullbackSquare` uses their
  canonical module inverse-image comparison through its published upstream name.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`,
  the unique K-flat-normalized canonical tensor comparison. Its fixed-constant-ring
  realization is the upstream `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`
  of `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal`.
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided`:
  `DerivedCategory.braidedCategory` and the canonical component notation `β_`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `rightDerivedLowerStarProjectionMap` and its component/adjunction-mate docstrings;
  the pro-etale counterpart in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection`.
- `Sheaf.Paper.BoundaryExceptionalComparisonData`: `comparison`, `etaleImage`,
  `proetaleImage`, `pullbackSquare`. These ordinary functor abbreviations require no
  exceptional adjunction, even though that module also supplies exceptional formulas.
- Proof imports: `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons` and
  `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`. Their recorded
  theorems supply naturality and signed-symmetry coherence in proof steps 1,2,4.

Added only the already-landed owning node
`def-weil-boundary-exceptional-comparison-data` to stmt_deps, as permitted for reuse of
landed definitions. Its ordinary functor abbreviations and pullback square are reused;
its exceptional formulas are not hypotheses. No new node, dependency repair or statement
correction. No theorem about an exceptional right adjoint is invoked by the statement.

Edge cases checked by reading the actual formulas: trivial finite coefficient ring;
zero B, M, Y or B'; empty Z or T; identity and general proper i; arbitrary (including zero)
compatible final arrows; nonidentity v and η; signed swaps with odd degrees in both slots;
bounded-below B,M whose derived tensor need not be bounded below. The binders impose
no nonemptiness, nonzero, finite Tor dimension, constructibility, finite type over a
field, closed immersion or ambient exceptional-adjoint requirement. The projection
square is retained as an explicit assumption rather than inferred under extra finiteness.

Searches actually run through msearch.py:

- LeanFinder: "Naturality of tensor symmetry and inverse projection formula under etale
  pro etale comparison for a compatible arrow". Eight hits, led by
  `Scheme.Pullback.Triplet.tensorCongr_symm` and Kaehler differential tensor identities;
  none states this derived projection-square composite equality.
- Loogle: `CategoryTheory.Functor.Monoidal, CategoryTheory.BraidedCategory.braiding`.
  Hits `Functor.Braided.mk` and `BraidedCategory.ofFaithful`; neither states the item.
- grep: `projection.*comparison|comparison.*projection|braiding_naturality` in
  Mathlib/CategoryTheory/Monoidal. Twenty-five hits, including
  `BraidedCategory.braiding_naturality`; these are individual symmetry identities.
- LeanSearch: "A symmetric monoidal comparison transports the inverse projection formula
  symmetry and a compatible final arrow between derived categories". Eight hits for
  monoidal transport, Cartesian product comparison and symmetric structure transfer;
  no exact statement of the item.
- rg over lean/WeilConjectures and lean/Sheaf for the node id: no hits. Concept searches
  for projection/comparison, qDefining/definingComposite and untransposed found the
  recorded boundary maps and canonical tensor/projection definitions reused here,
  but no theorem with this statement. The source names index was also searched for
  the node id, with no hit. No mathematical notion was redefined.

Validation: the final scompile.py check passed for both the sandbox and library
forms in 24.4 and 23.3 s, with no errors or warnings. The definitions use the existing
β_ notation directly. The only postponed proof is the named main theorem. The
required deliver2.py dry run and delivery follow this check.

Additional worker clause check (not an independent review): I reread the full node
against the signature and definitions, checking the opposite tensor orders in r and s,
the direction of η and rho, π_p at the independent B', and the arbitrary compatible ap.
All are retained. The final version uses the canonical Koszul braiding directly, so it
requires no supplied symmetry presentations. Both _hπ and the conclusion were checked
in reverse order against the printed TeX because Lean composes left to right. The
helpers contain no sorry; only the main theorem has one. Dispatcher mode prohibits
other agents; the maintainer's independent review reads the delivery.

## Second reading by Q96

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
