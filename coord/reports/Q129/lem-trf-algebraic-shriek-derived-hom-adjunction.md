## Worker report

Module: `Sheaf.Algebra.Homology.AlgebraicShriekDerivedHomAdjunction`.
Main theorem: `ModuleCat.algebraicShriek_derivedHom_adjunction`, with its entire proof
`sorry`. Six helper definitions contain actual data. There is no new axiom, no hollow
object, no arbitrary map, and no change to the mathematical statement or proof plan.

Source read: `literature/stacks-project/dualizing.tex`, section Trivial duality for a
ring map, lemmas `lemma-right-adjoint` (0A70), `lemma-RHom-ext` (0A71), and the displayed
calculation in `lemma-relative-dualizing-algebraic` (0BZW), proof of (1)(c). The latter
uses perfection to prove invertibility later; this node concerns the adjunction and
the identity of the scalar map with biduality, which do not require perfection.
The node and both original statement dependencies were read, including their Lean
records and full source signatures/docstrings. No repair note exists for this item.

Hypotheses, objects, and clauses:

- A homomorphism of commutative rings is `{P A : Type u} [CommRing P] [CommRing A]
  (f : P →+* A)`. No Noetherian, finite-type, boundedness, flatness, or perfectness
  assumption is imposed. The shared universe covers any given pair of rings after
  increasing the ambient size; the small Hom universe for D(Mod) is the existing
  Grothendieck-module convention, `[HasDerivedCategory.{u} (ModuleCat.{u} P)]` and
  the analogous binder for A. All universes and variables are explicitly bound.
- The ordinary module derived categories are Mathlib `DerivedCategory (ModuleCat R)`;
  U is `(restrictScalars f).mapDerivedCategory`. This is the recorded abstract-derived-
  category definition, not an étale or completed coefficient category.
- C is the existing `ModuleCat.derivedCoinduction f`, constructed as the total right
  derived ordinary coextension functor. `coinductionComplexFunctor f` uses actual
  `ModuleCat.coextendScalars f`, whose action is `(a • h)(b) = h(b*a)`.
  `derivedCoinductionModel f I` is the canonical comparison for every K-injective I.
  The witness hJ states that the coinduced I is K-injective, so the A-Hom model is valid.
- RHom is the upstream closed internal Hom `ihom`, i.e. the K-injective total right
  derived Hom, with the ordinary unbounded derived tensor structure. The original
  generic ringed-site definition is imported through its recorded module. The
  ordinary-module presentation is the native closed construction, already used by
  the project's ordinary module Hom/evaluation API. There is no private replacement.
  The families eP and eA have hom maps equal to `coinductionHomComparison`, the
  transpose of Q's canonical tensorator followed by the signed evaluation. Hence
  these are canonical model comparisons, not arbitrary isomorphisms of objects.
- The isomorphism natural in both X and Y is the *natural isomorphism* θ between
  `coinductionHomLeft f` and `coinductionHomRight f`. Their objects are exactly
  U(RHom_A(X,C(Y))) and RHom_P(UX,Y). Their maps come from the existing internal-Hom
  bifunctor, coinduction, and restriction. Naturality is part of the type `≅` of functors.
- T is an isomorphism of the actual product total Hom complexes, for every E and I,
  without any boundedness assumptions. The first coordinate equation says
  `T(z)(x) = (coinductionEvaluation f I)(z(x)) = z(x)(1)`. The inverse equation says
  `eval₁(a • T⁻¹(z)(x)) = z(a • x)`, equivalently `T⁻¹(z)(x)(a) = z(a*x)`, by the
  displayed coextension action. These equations quantify over *every* cochain degree r,
  input degree p, target degree q, and equality p+r=q, and every element x and scalar a.
  This includes the inverse formula, not merely evaluation on chain maps.
- The model equation for θ says that after the canonical coinduction comparison,
  eA, exact-restriction localization factorization, Q(T), and eP, one obtains θ.
  The final precomposition is the exact-restriction comparison on E, so the target
  is RHom_P(U(QE),QI), rather than a silently substituted source representative.
- κ identifies UC(Y) with RHom_P(A[0],Y). Its hom component is explicitly θ at A[0]
  composed with the canonical unit-Hom identification `MonoidalClosed.unitNatIso` and
  `singleFunctorObjUnitIso`; its normalization is therefore fixed by θ and T.
- D is C(P[0]); n is every integer. The last clause takes K = D[n], Y = P[0][n],
  and s = `coinductionHomShift f P[0] n : C(P[n]) ≅ D[n]`. This is the canonical mate
  of the exact restriction shift under the explicitly constructed adjunction.
  `coinductionHomScalarFormula` starts with U of the scalar map
  `singleFunctorObjUnitIso.hom ≫ MonoidalClosed.curry' (𝟙 K)` and then applies θ.
  This is the same scalar map construction already used by the consumer
  `AlgebraicGeometry.algebraicShriekScalarMap`, without importing that downstream theorem.
- The right side of that formula is `MonoidalClosed.curry (Koszul-braiding ≫ ihom.ev)`
  precomposed in the Hom variable by `U(s.inv) ≫ κ_Y`. This is precisely canonical
  coefficient biduality, not an existential morphism with the correct codomain.
  It is written before cancelling equal shifts: its inner dual is RHom_P(A,P[n])
  and its coefficient is P[n]. The canonical identifications
  RHom_P(A,P[n]) ≅ RHom_P(A,P)[n] and
  RHom_P(H[n],P[n]) ≅ RHom_P(H,P) give the node's displayed target
  RHom_P(RHom_P(A,P),P). This is an equivalent expression of the stated equality
  under canonical shift identifications, retaining the literal D[n] on its left.
  The proof docstring records the factor (-1)^(n*r) on Hom degree r; scalar action
  has r=0, so evaluation is exactly `a ↦ (h ↦ h(a))` for every integer n.

The helper `coinductionHomEvaluation` selects the evaluation witness of the already
landed `projective_hom_evaluation_model`. Its pure-tensor coordinate formula determines
all components uniquely, for *all* complexes; the bounded-projective conditions of that
node occur only in its later model-isomorphism clause, never in evaluation itself.
This uses the permitted choice from a theorem determining the object, not choice of
an undetermined object. Every new definition uses an existing construction or this
uniquely characterized evaluation; only the main theorem is postponed.

Dependency declarations used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and localization factorization.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` (the generic recorded interface;
  ordinary modules here use the already existing native closed presentation).
- `Sheaf.Algebra.Homology.ModuleHomComplex`: `CochainComplex.moduleHomComplex`;
  `Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel`:
  `CochainComplex.projective_hom_evaluation_model` fixes signed evaluation.
  Their already landed nodes are added to stmt_deps, as allowed by the current brief.
- `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`: only the proof-free
  construction declarations `ModuleCat.coinductionComplexFunctor`,
  `coinductionEvaluation`, `derivedCoinduction`, `derivedCoinductionModel`,
  `derivedCoinductionAdjunction` are used. Their data are built from existing
  upstream derivation and adjunction APIs; its theorem `derivedCoinductionAdjunction_spec`
  is *not* used. That theorem's DAG proof depends on the present item, so it is not
  added as a statement dependency. Its future proof import of this module must be
  omitted under the standard import-cycle exception. This is reuse of constructions,
  with no mathematical dependence on the downstream theorem.
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`,
  `...DerivedCategory.Monoidal.Closed`, and `...DerivedCategory.FlatModel`:
  the native derived closed structure and `DerivedCategory.singleFunctorObjUnitIso`;
  `Mathlib.CategoryTheory.Monoidal.Closed.Basic`: `MonoidalClosed.internalHom`,
  `curry`, `curry'`, `pre`, `unitNatIso`, `ihom.ev`;
  `Mathlib.CategoryTheory.Shift.Adjunction`: `Adjunction.rightAdjointCommShift`.
- All stated proof dependencies are imported non-publicly at their recorded modules:
  HomComplex, K-injectivity, K-flat resolutions with independent coefficients,
  KInjectiveHomComplex, QuasiIsoHomComplexMap, HomTensorTotal, RingedSiteDualityMaps,
  the Mathlib K-injective localization bijection, and independent-coefficient tensor descent.
  The eight-step docstring follows the node's complete proof in order.

Edge cases: checked zero complexes, zero rings, identity ring maps, non-flat quotient
maps, unbounded sources and targets, n=0 and negative n. The counit and inverse formulas
remain meaningful for each of these. No summation is interchanged with a product.
The scalar map is not asserted invertible; such an assertion would be false without
perfection. In degree zero and for P=A, the final equation reduces to ordinary scalar
multiplication followed by `h ↦ h(a)`. No node fault or disputed statement was found.

Searches actually run with `msearch.py Q129 <item>`:

- LeanFinder: “For a commutative ring map derived coinduction yields a natural internal
  derived Hom adjunction compatible with double dual evaluation”. Eight ordinary
  coextension/restriction hits, including `restrictCoextendScalarsAdj`; no full theorem.
- Loogle: `ModuleCat.restrictCoextendScalarsAdj`. One exact ordinary adjunction hit;
  read its signature and the coextension action/evaluation source.
- LeanSearch: “Derived Hom for modules over commutative rings coinduction adjunction”.
  Eight generic derived-adjunction and representation coinduction hits; no enriched
  ordinary-module statement with the biduality normalization.
- Mathlib grep: `derivedHom|derivedCoinduction|coextendScalars` in `Algebra`.
  Seven hits for ordinary coextension and enough injectives, no full theorem.
- Direct rg of upstream `WeilConjectures` and shared `lean/Sheaf` for derived Hom,
  coinduction, scalar action, and biduality found the construction modules above,
  the module Hom/evaluation API, and the downstream relative-perfect theorem.
  Direct search for this item id in upstream and `dag/lean_names_upstream.json`
  found no matching declaration. Native InternalHom, derived Closed, FlatModel,
  Shift.Adjunction, and ChangeOfRings signatures/docstrings were opened and read.

Validation: scompile.py compiled both sandbox and library module cleanly before the
final proof-import completion. The final delivery is compiled again by the prescribed
wrapper and delivery dry run; only the main theorem's expected sorry is permitted.

## Second reading by Q129

The dispatcher explicitly forbids starting other agents, so this section is an honest
second reading by the same worker; the maintainer supplies the independent reading.
I reopened the node and final module and matched: arbitrary commutative P→A, ordinary
unbounded D(Mod), exact U, coinduced A-action, K-injective model, bifunctor naturality,
evaluation at one, inverse on every homogeneous cochain, the canonical scalar map on
D[n], and transposed braided biduality with both equal shifts. The normalization of eP,
eA, θ, and κ prevents arbitrary object isomorphisms from standing in for these maps.
The original draft's direct function coercions on coinduced carriers did not elaborate;
they were replaced by the *existing* degreewise counit, whose definition is evaluation
at one. The inverse formula evaluates a•h at one, hence still says h(a). A second typing
issue required specifying the ambient ordinary module derived category on the nested
currying expression. These changes do not change the node's statement. All six helper
definitions contain full data. Only the main theorem is sorry. No statement correction,
new node, or dependency repair was needed.
