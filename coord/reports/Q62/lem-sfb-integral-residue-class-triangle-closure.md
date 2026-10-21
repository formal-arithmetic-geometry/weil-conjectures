## Worker report

The module `Sheaf.Paper.IntegralResidueClassTriangleClosure` states
`AlgebraicGeometry.ProEtale.integralResidueClass_triangle_closure`, with its proof
`by sorry`. Its two real Prop-valued helper definitions unpack P and its first
residue-origin clause, both explicitly introduced in this node. These are helpers
of the owning statement, not independent replacement notions. Nothing is proved.
No new DAG nodes, dependency repairs, or statement corrections are supplied.

Source read: current main-20261015 blueprint,
`sec-six-functors-basics/sk-lem-int-integral-heart/sk-lem-int-integral-heart-triangulated.proof.md`,
paragraph (1), up to the triangulatedness assertion and before its boundedness and
truncation assertions. The node deliberately isolates the stability argument from
those later geometry-dependent assertions. Its seven proof steps are reproduced
in the theorem docstring, including all three positions via rotation.

Hypothesis and object correspondence:

- Scheme and fixed small site: `X : Scheme.{u}`, with `Scheme.ProEt.topology X`
  throughout `AdicCompletion.Modules`. No site is replaced or selected afresh.
- Size convention: the explicit universe `u` gives schemes and E in `Type u`,
  site objects in `Type (u+1)` and morphisms in `Type u`, and additive coefficient
  sheaves in `Ab.{u+1}`. The standard existing unbounded derived category is used.
  The ordinary coefficient ring is `ULift.{u+1}` of the same residue ring; this
  raises its carrier size without restricting the site or changing scalars.
- Prime: `(l : ℕ) [Fact l.Prime]`.
- Finite extension: `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. There is no extra norm or embedding assumption.
- Valuation ring, chosen uniformizer, and residue: the existing
  `Padic.coefficientExtensionAbsoluteValue`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, and `coefficientExtensionRing l E 1`.
  The last is literally O_E modulo the first power of the uniformizer ideal.
- Continuous integral coefficient ring R_X: `AdicCompletion.ring l E X`, the
  `condensedRingObj` pullback of `DerivedNakayama.integerRing l E`; its modules
  are `AdicCompletion.Modules l E X`. No constant integral ring is substituted.
- Ambient K: `DerivedCategory (AdicCompletion.Modules l E X)`, unbounded, with
  all ambient morphisms. No boundedness or finite-Tor assumption is imposed on K.
- K_1 with its residue-module structure:
  `(AdicCompletion.derivedReduction l E X 0).obj K`. The API indexes positive
  exponent n+1 by n, so index 0 is precisely residue reduction. This functor is
  `(Mod.extendScalars (AdicCompletion.quotient l E X 0)).leftDerivedFunctor`;
  its output is in the derived category of modules over the actual residue ring,
  rather than merely integral modules after forgetting residue scalars.
- Completeness: the existing `IsDerivedComplete l E X K`, with exactly its
  canonical augmentation/derived quotient tower meaning.
- Bounded constructible etale origin: `integralResidueEtaleOrigin l E X K`
  uses `isBoundedConstructibleFiniteCoefficient`, without reimplementing its
  boundedness, finite stratifications, finite stalk modules, or etale inverse image.
  Its definition is `ObjectProperty.map` along `finiteCoefficientDerivedComparison`,
  so it asserts existence of a bounded constructible etale A and the required iso.
- To apply that recorded predicate to the internal residue-module K_1, the helper
  existentially quantifies the existing `FiniteDiscreteOrdinary.Encoding` and
  transports K_1 by `e.fixedDerived.functor`, then
  `finiteCoefficientRealization.mapDerivedCategory`. Encoding is NOT an arbitrary
  equivalence: its ringIso is normalized on every constant scalar, its forward
  ordinary functor equals `sectionEncoding`, its fixed functor equals
  `fixedRestriction`, and fixedDerived is the actual termwise derived functor.
  These equations pin the underlying action transport. All such encodings give
  the same essential-image predicate up to canonical isomorphism. No data is
  chosen from `Nonempty`; e is bound only inside a Prop-valued definition.
  Existence adds no geometric condition: the finite residue quotient has its
  discrete quotient topology, and `encoding_exists` provides this normalized
  encoding for every X. The helper installs finiteness using the recorded
  `Padic.finite_coefficientExtensionRing`, and uses bottom/discrete topology only
  for the ordinary ULift residue target. The internal ring keeps its actual
  quotient topology from the spectral absolute value.
- P itself: `integralResidueClass` is the conjunction of those two clauses.

Conclusion correspondence, in order:

1. P(0): first conjunct, with `ZeroObject` scoped zero notation.
2. Isomorphism invariance: for every K, L and `e : K ≅ L`, `P K ↔ P L`.
3. Every integer shift: `∀ K (n : ℤ), P (K⟦n⟧) ↔ P K`.
4. Ambient distinguished triangle: `T : Pretriangulated.Triangle ...` and
   `T ∈ distTriang ...`; no triangle in a previously restricted category is used.
5. All two-out-of-three implications are explicit: (1,2) implies 3, (1,3)
   implies 2, and (2,3) implies 1.
6. The last conjunct states the requested particular consequence separately:
   P(T.obj₁) and P(T.obj₃) imply `IsDerivedComplete ... T.obj₂` and
   `integralResidueEtaleOrigin ... T.obj₂`.
7. There are no Noetherian, dimension, finite-type, base-field, or invertibility
   assumptions on X, and no assumption that l differs from a characteristic.

Recorded statement-dependency interfaces read and reused:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `def-weil-size-convention` is metatheoretic; universes are explicit as above.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, exporting the coefficient constructions.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `upperStarFromPoint`, via the completion
  category and reduction constructions.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  the recorded unbounded derived convention; here the ordinary Mathlib
  `DerivedCategory` localization on the existing module categories is sufficient.
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`: `IsDerivedComplete`,
  `AdicCompletion.Modules`, `.finiteRing`, `.quotient`, `.derivedReduction`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `finiteCoefficientRealization`, `finiteCoefficientDerivedComparison`,
  `isBoundedConstructibleFiniteCoefficient`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  existing relative derived tensor/closed structure, used by scalar extension.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `DerivedChangeOfRingsCochainModel`,
  `nonempty_derivedChangeOfRingsCochainModel`; its K-flat, exact derived-scalar
  extension convention agrees with the canonical internal scalar extension above.

The recorded modules for all proof dependencies are imported as proof imports
unless their exports occur in our helper definitions. Mathlib triangle morphism,
exact derived functor, homology comparison, triangulated category and sheafification
interfaces are already transitively available. The completion-triangle module
landed while this worker was running and its now-recorded module is also imported.
`FiniteDiscreteOrdinaryEquivalence` is the published public source of Encoding
for this compile: an additional direct Encoding import initially caused a duplicate
`Encoding.ordinary` declaration in published artifacts, and was removed as instructed.
The server source of that equivalence module was read with `scompile.py --source`.

Edge cases checked mathematically: the empty scheme and zero complex; n=0 and
negative shifts; split/zero triangles, and each of the three possible missing
vertices; E=Q_l; l=2; schemes in characteristic l; unbounded ambient K;
non-Noetherian and non-quasi-compact schemes. None is excluded. Finite residue
coefficients, rather than a claim about constructibility of the continuous integral
ring, are what make the origin closure argument apply on arbitrary X. The global
finite-stratification condition comes from the recorded origin predicate and is
not replaced by affine-local constructibility or finite Tor amplitude.

Searches actually made:

- msearch.py leanfinder: "Derived complete proetale complexes with bounded
  constructible etale residue reduction are closed under zero shifts and
  distinguished triangles". Eight hits: generic derived category triangulation,
  t-structure bounds, and Q/single-functor bound lemmas; no exact statement.
- msearch.py loogle: `"ObjectProperty", "IsTriangulated", "inverseImage"`.
  Two hits, generic inverse-image triangulated-subcategory instances; no
  completeness-plus-residue-origin theorem.
- msearch.py grep: `derived.complete.*(cone|triangle)|etale.*origin.*triang`.
  Zero Mathlib hits.
- msearch.py leansearch: "The intersection of derived complete complexes and
  complexes whose residue reduction has bounded constructible etale origin is
  triangulated". Eight generic triangulation, localization and t-structure hits;
  no statement on this P.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  item id, `integralResidueClass`, `integral_residue_class`: no exact statement.
  Further searches for `IsDerivedComplete`, residue/triangle combinations and
  `AdicCompletion` found the existing completion, integral-model and criterion
  interfaces. IntegralModels restricts coefficient presentations/geometric
  hypotheses; IntegralCriterionReductions uses all positive reductions and a
  common interval. Neither is the arbitrary-X, first-etale-residue class here.
- Read the actual finite-discrete Encoding and ordinary finite coefficient
  realization interfaces instead of introducing another coefficient equivalence.

No statement dispute or node fault was found. The definitions have real bodies;
the only postponed proof in the delivery is the named main theorem. Server compile
of sandbox and library module passed cleanly (6.6 s and 8.4 s before adding the
newly landed completion proof import); final preflight recompiles the final file.

## Second reading by Q62

This is a separate clause-by-clause self-audit, not a claim of independent-agent
review: the dispatcher expressly prohibits starting another agent and assigns
independent review to the maintainer. I reopened the node, its source paragraph,
and the delivered module. I checked every binder and all four conclusion groups
against the correspondence above. The only exposed scalar transport is the
constant-section-normalized Encoding, and it is used under an existential in Prop,
so no arbitrary object is selected. I checked that the target topology is discrete
only after ordinary residue realization, while the internal quotient topology and
continuous integral coefficient object are retained. I checked that each of the
three missing-vertex cases is present, the shift statement is an iff for every
integer, the middle-vertex consequence retains both conjuncts, and no geometry or
boundedness assumption has slipped into the theorem. The initial compile found
missing scopes for the zero object and Triangle; these were corrected by opening
`ZeroObject` and `CategoryTheory.Pretriangulated`. The redundant direct Encoding
import was removed after the published-artifact duplicate diagnostic. No mathematical
statement was changed. The maintainer's independent review remains authoritative.
