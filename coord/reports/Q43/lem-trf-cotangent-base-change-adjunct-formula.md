## Worker report

The module Sheaf.RingTheory.CotangentBaseChangeAdjunctFormula states
Algebra.CotangentResolution.cotangent_base_change_adjunct_formula with sorry.
Its seven helper definitions implement the objects and canonical maps already
introduced by this node. No independent notion or dependency repair is needed.
The node changes only in lean; the mathematical statement is unchanged.

Clause-by-clause correspondence:

- The four commutative-ring homomorphisms form `q : f ⟶ g` in
  `Arrow CommRingCat`: `f.hom : A → C`, `g.hom : A' → C'`, `q.left : A → A'`,
  `q.right : C → C'`, and `q.w` is commutativity.
- `C : Coherence` is the already recorded cotangent-resolution interface.
  `C.standard f`, `C.standard g` and `C.standardMap q` are exactly P, R and t.
  The interface fixes their terms and operators by explicit polynomial formulas.
- `squareTensorAugmentation q (C.standard f)` is P'. Its algebra is the
  pointwise pushout along A → A'; commutative-ring pushouts are ring tensor
  products. Its augmentation is the pushout descender from epsilon followed
  by q.right and g.hom, so it sends p tensor a' to f(epsilon(p))a'.
  `hP` is precisely the assumed polynomial-resolution condition.
- The recorded `differentialComplex (C.differentials ...)` gives K, K', K(R)
  with the existing negative alternating-complex convention. Its differential
  terms use Mathlib's actual Kahler differentials and ordinary module tensor.
- `hK` is the recorded quasi-isomorphism-preserving tensor K-flat predicate.
  `hflat` quantifies `Module.Flat` over every integer-indexed term of K.
- Q is `DerivedCategory.Q`. `L`, `epsilon`, `hL` specify a universal total
  left derived pair for ordinary extension of scalars. This is the same
  pair transported by the one-point identification, quantified invariantly
  under its unique counit-compatible isomorphism, rather than a new choice
  of scalar extension. The conclusion supplies cK as an isomorphism and fixes
  its forward map to `epsilon.app K`; it cannot be an arbitrary isomorphism.
- `squareTensorComplex` is K tensor_C C', in Mathlib's symmetric factor order
  C' tensor_C K. `squareTensorUnit` is the ordinary tensor/restriction unit,
  hence x maps to 1 tensor x in that order.
- `squareTensorInclusion` is p maps to p tensor 1. `squareTensorTheta` is the
  ordinary chain adjunction adjunct of its differential map, so on generators
  it sends b' tensor (c tensor dp) to f(c)b' tensor d(p tensor 1). This is
  exactly the displayed theta formula with the tensor factors reversed.
- `squareTensorToTarget (C.standardMap q)` is h. Its data is the actual pushout
  descender: h(p tensor a') = t(p)a'. Its `AugmentedMap (𝟙 g)` type contains
  simplicial naturality, base compatibility and augmentation compatibility.
  hP and `C.standard_resolution g` say both endpoints are polynomial resolutions.
  No arbitrary algebra map is supplied as an assumption.
- `squareTensorDifferentialMap` is K(h), composing the recorded differential
  map with the canonical cancellation of restriction along the identity.
- cP' and cR are `C.comparison ... hP` and
  `C.comparison (C.standard g) (C.standard_resolution g)`.
  The first morphism-equation conjunct is QK(h) followed by cR = cP'.
- `cotangentMap C q` is gamma, the existing standard functoriality map.
  The next conjunct expresses its representation by Q(u), restricted Q(theta),
  restricted QK(h), and restricted cR. `mapDerivedCategoryFactors.inv` inserts
  exactly the localization/restriction comparison required to type this equation.
- `a` and `normalized` specify the normalized derived extension/restriction
  adjunction at K: its unit followed by the computation map equals Q(u).
  This is clause (1) of the cited normalized adjunction, transported to ordinary
  modules. These binders specify the adjunction in the node, and do not impose
  a condition on the square beyond its stated hypotheses. Quantifying over
  universal pairs avoids fixing one presentation of the transported functor.
- Beta is `(a.homEquiv _ _).symm (cotangentMap C q)`.
  The final two conjuncts say beta = cK;Q(theta);QK(h);cR and
  beta = cK;Q(theta);cP', respectively. Lean writes composition left to right.
- There is no assumption of theta invertibility, of derived multiplication
  invertibility, of a flat ring homomorphism, or of boundedness. All variables
  and the ring universe are explicit (`autoImplicit false`); the derived-category
  sizes follow the previously recorded Coherence interface.

Dependency declarations read and used:

- lem-trf-cotangent-resolution-coherence:
  Sheaf.RingTheory.CotangentResolutionCoherence, `Augmentation`, `AugmentedMap`,
  `IsPolynomialResolution`, `Coherence`, `differentialComplex`, `differentialMap`,
  `cotangentComplex`, `cotangentMap`, and `restrictComplex` in
  Algebra.CotangentResolution. Its comparison normalization is retained explicitly.
- def-weil-pbc-kahler-differentials:
  Mathlib.RingTheory.Kaehler.Basic, `KaehlerDifferential`, `.D`,
  `.linearMapEquivDerivation`, used by the existing differential models.
- def-pc-module-kflat-complex:
  WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat,
  `CategoryTheory.MorphismProperty.kFlat`, the predicate in hK.
  The public KFlat import exposes the complex specialization.
- def-weil-abstract-derived-category:
  Mathlib.Algebra.Homology.DerivedCategory.Basic, `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`.
- lem-trf-one-point-derived-ring-identification:
  Sheaf.TraceFormula.OnePointDerivedRingIdentification,
  `CategoryTheory.OnePointDerivedRingIdentification` and
  `CategoryTheory.one_point_derived_ring_identification`. Its scalarExtension
  clause specifies the counit-compatible transport of the universal pair.
  The public import also exposes the existing singletonExtendScalarsAdditive
  instance and cochain tensor instances, avoiding another additive instance.
- def-weil-pbc-module-tensor-product:
  Mathlib.LinearAlgebra.TensorProduct.Defs, `TensorProduct`; ordinary scalar
  extension and its unit are `ModuleCat.extendScalars` and
  `ModuleCat.extendRestrictScalarsAdj` from Mathlib's ChangeOfRings.
- lem-pur-sheaf-ring-derived-coefficient-adjunction:
  Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction,
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`, imported for the proof
  of the representative normalization and adjunct calculation.
- def-weil-pbc-flat-ring-map:
  Mathlib.RingTheory.RingHom.Flat, `Module.Flat` and `RingHom.Flat`;
  only module flatness is assumed, as the node says.
- def-weil-pbc-simplicial-object:
  Mathlib.AlgebraicTopology.SimplicialObject.Basic,
  `CategoryTheory.SimplicialObject`, whose morphisms are natural transformations.

Source read: literature/stacks-project/cotangent.tex, section-functoriality
(Tag 08QL, lines 867 onward) and lemma-flat-base-change-cotangent-complex
(Tag 08QQ, lines 985 onward). These give the standard map and induced adjunct;
the four-step assembly in the node is retained in the theorem docstring.

Edge cases checked by reading the constructions: identity square; zero target
ring C'; A=C and the empty polynomial-variable case; arbitrary infinite
polynomial variable sets; nonflat maps such as Z → F_p. Pushouts and the
ordinary tensor adjunction remain defined in every case. Only hP, hK and hflat
are mathematical hypotheses, as in the node. No extraction of a false flatness
conclusion or inversion of theta occurs. Positive terms are already zero by
negativeComplex. No STATEMENT-DISPUTED issue found.

Searches (2026-10-24):

- msearch.py leanfinder: "The derived scalar extension adjunct of cotangent
  functoriality equals the map on polynomial differential resolutions": eight
  hits, including Algebra.Extension.CotangentSpace.map_cotangentComplex,
  map_comp_cotangentComplex and presentation/H1 formulas. Reading
  Mathlib/RingTheory/Extension/Cotangent/Basic.lean:53–114 shows these are
  presentation-level linear maps, not the full derived formula. No exact match.
- msearch.py leansearch: "The derived tensor adjunct of cotangent complex
  functoriality is computed on polynomial resolutions": eight hits, including
  Functor.leftDerived, ProjectiveResolution.isoLeftDerivedObj, Tor,
  Adjunction.derived and Algebra.Extension.cotangentComplex. No exact match.
- msearch.py loogle: `"cotangent", "adjunction"`: zero hits.
- msearch.py grep: `cotangent.*adjunct|cotangent.*adjunction|simplicial.*cotangent`:
  zero Mathlib hits.
- rg of the item's id and `cotangent.*adjunct|cotangent.*Adjunct` in
  lean/WeilConjectures and lean/Sheaf: nearby cotangent base-change and
  sheaf-comparison docstrings, no statement of this formula.
  CotangentFlatBaseChange.lean defines an actual adjunct but only states its
  invertibility under a stronger derived-multiplication hypothesis, not this
  formula; importing that downstream node would also reverse the intended DAG.
- rg of `cotangent_base_change_adjunct_formula|squareTensorAugmentation|squareTensorTheta`
  in dag/lean_names_upstream.json, lean/WeilConjectures and lean/Sheaf: no hits.
- Additional source searches found the existing singletonExtendScalarsAdditive
  instance; the draft duplicate was removed and the existing public import reused.

Validation: scompile.py compiled the complete module against current server
sources in 3.9 seconds, exit 0. Its local attempt ran out of device space;
the wrapper's automatic server confirmation succeeded. The only postponed proof
is cotangent_base_change_adjunct_formula; every helper has concrete data.

## Second reading by Q43

A second pass by the same worker, as this dispatch explicitly forbids starting
other agents; the maintainer supplies the independent review. I reread the node
and final module together, checking q's orientation, the tensor augmentation,
all three differential complexes, the K-flat and termwise-flat binders, the
unit and theta formulas, the identity restriction on K(h), both canonical
comparisons, gamma with restricted target maps, and both beta equations.
The draft introduced a duplicate scalar-extension additive instance; I removed
it and reused the instance exposed by the one-point dependency. The canonical
computation map is explicitly fixed to epsilon.app K, and the normalization
premise fixes the adjunction's unit, so neither is arbitrary. The comparison
with the standard target is retained even though its normalization is the
identity. No clause was removed, no mathematical hypothesis added, and no
statement correction or new DAG node is required.
