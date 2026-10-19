## Worker report

Item: lem-coef-finite-point-internal-hom-evaluation. The module
`Sheaf.Paper.FinitePointInternalHomEvaluation` states
`WeilConjectures.finitePointInternalHomEvaluation`, with `sorry` as its whole proof.
Its six helper definitions have actual data. No node statement or dependency list
is changed, and there are no new or repaired dependency nodes.

The source read is the opening paragraph of main-20261015's
`sec-six-functors/sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md`.
The node's five proof steps are reproduced in the theorem docstring, including
the finite quotient, exact reconstruction, K-flat/K-injective Hom calculation,
finite-Tor closure, signed evaluation and derived naturality steps.

Clause-by-clause rendering:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Global finite-field datum and algebraic closure k | `D : FiniteFieldDatum.{u}`, with the site of `Spec (.of D.k)` |
| Prime ell distinct from p | `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p` |
| Finite extension E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` |
| Valuation ring, uniformizer, positive quotient level | The dependency's `Padic.coefficientExtensionRing l E (n + 1)` uses exactly its valuation ring and chosen uniformizer; `n : ℕ` runs over all positive exponents by this successor indexing |
| C in bounded constructible finite-Tor complexes | `finiteTorConstructibleCategory l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))` |
| c = Fib_s C | `finitePointFibreTensorSource D l E n`, the existing finite-Tor inclusion followed by `pointFiniteSections ... .mapDerivedCategory` |
| The coefficient sheaf B = (A_n)_s | `finitePointCoefficientUnit`, the unit of the existing intrinsic derived tensor, i.e. the coefficient sheaf in degree zero |
| Identity-point dualizing object | `finitePointComparisonOmega` is exactly the identity-adjoint formula `nu^* Rnu_* B`, conjugated through `sfIntrinsicDerivedEquivalence` |
| Normalization is the comparison counit | `finitePointComparisonNormalization` maps `(derivedComparisonAdjunction ...).counit.app ...` through intrinsic realization, followed by realization's own counit isomorphism |
| This normalization is invertible | The first conjunct is `IsIso (finitePointComparisonNormalization D l E n)` |
| Derived sheaf internal Hom into omega | `finitePointSheafDual` uses `finiteIntrinsicDerivedInternalHom`, whose definition is the recorded `derivedInternalHomOfUniverses` on the actual small pro-etale site |
| Point tensor and unit comparisons | `pointFiniteTensorComparison ... S` and `S.unitIso`, constrained by `PointFiniteSourceConstraints` and `PointFiniteTensorCanonical` |
| Canonical evaluation-transpose map | `finitePointDualPairing` is inverse tensor comparison, sections of sheaf evaluation followed by normalization, then unit comparison. `finitePointInternalHomKappa` curries this pairing after the recorded Koszul braiding |
| Target RHom_A(c,A) | Mathlib/upstream `(ihom c).obj (𝟙_ _)`, over the same lifted coefficient ring used by the recorded fibre |
| Kappa is an isomorphism | `∀ C, IsIso (finitePointInternalHomKappa ... C (h C))` |
| Natural in C | The second final conjunct quantifies every `f : C ⟶ C'` and equates sections of contravariant sheaf Hom followed by kappa with kappa followed by `MonoidalClosed.pre` of the fibre map |
| Characterized by evaluation | The last conjunct is `(kappa ▷ c) ≫ DerivedCategory.perfectTraceEvaluation c = finitePointDualPairing ...` |

The tensor comparison is an existential witness with the already recorded
canonical normalization predicate, rather than an extra hypothesis of the
lemma or a new monoidal structure selected from mere existence. The map kappa
itself is a concrete composite and transpose. Its source's finite-Tor membership
witness `h` is supplied in the conclusion; it imposes no additional condition on C.
That membership is the proof's application of finite constructible Hom on the
zero-dimensional point. Proof irrelevance removes any dependence on its proof.

For the identity compactification, the node explicitly specifies identity etale
compact support and the identity as its normalized etale right adjoint. Accordingly
omega is written using the node's explicit `nu^* Rnu_* B` formula. This computes
the exceptional-inverse-image dependency in those identity-adjoint coordinates;
it does not assume that pro-etale sheaves are just sets, replace omega by B, or
select an arbitrary isomorphism with B. The realization equivalence and its
counit are the recorded coefficient presentation transport.

The fibre lives in modules over `ULift.{u + 1, u} A`, precisely as in
`pointFiniteFibre` and the tensor comparison dependency. The site retains object
universe `u + 1` and morphism universe `u`; no equality between these is imposed.
The Hom-first evaluation is the existing `perfectTraceEvaluation`, which uses
the same Koszul braiding and coefficient closed evaluation for every derived
module object; no perfectness hypothesis is introduced by that definition.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (and its imported
  `CoefficientExtension`): `Padic.finite_coefficientExtensionRing`,
  `Padic.coefficientExtensionRing`, valuation ring and uniformizer constructions.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`
  and `finiteTorConstructibleCategory`.
- `Sheaf.Paper.FiniteCoefficientPoint`: finite clause `pointFiniteFibre` and
  the exact ambient functor `pointFiniteSections` from `PointSectionsFiniteness`.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: `sfFiniteExceptionalAt`,
  whose literal finite-level formula is Rnu_*, etale right adjoint, nu^*;
  its publicly imported intrinsic interface gives `sfIntrinsicDerivedEquivalence`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteIntrinsicClosed`,
  `finiteIntrinsicDerivedInternalHom`, `finiteIntrinsicEvaluation`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` (through the intrinsic Hom).
- `Sheaf.Paper.PointFibreDerivedTensor`: `pointFibreDerivedTensor`,
  `PointFiniteSourceConstraints`, `PointFiniteTensorCanonical`, and its imported
  `PointFiniteTensorData`, `pointFiniteTensorComparison`, `unitIso`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `proEtaleSiteComparisonModules`, realized by the same comparison functors;
  the imported fixed-coefficient derived comparison gives
  `AlgebraicGeometry.ProEtale.derivedComparisonAdjunction` and its counit.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`:
  `isIso_compactSupportComparisonUnit`, used in the normalization proof plan.

Additional proof-only modules are imported without `public`: ExtensionIntegersDvr,
Etale.Derived.LowerShriek, ComparisonPullbackExact, PointProEtaleSectionsExact,
PointSectionsReconstruction, KFlatResolutionIndependentCoefficients,
PointDerivedHomEvaluation and FiniteConstructibleHom. The connected-constant-H0
node currently has no recorded Lean declaration and hence no module to import.
No import cycle was introduced.

Edge cases checked before and after writing:

- `n = 0` here denotes the first positive exponent, A_1, not the zero quotient.
- The zero object and all shifts are allowed; the hypothesis uses the existing
  intrinsic finite-Tor predicate without a selected Tor interval or model.
- C equal to the coefficient unit gives its coefficient-valued dual, with the
  actual comparison counit still present in the evaluation pairing.
- A two-term complex `[A --varpi--> A]` is allowed, so the statement is not
  restricted to cohomology modules that are projective.
- Naturality includes zero maps, identities and arbitrary localized derived
  morphisms, not just maps of chosen complexes.
- The opposite ordering of the two evaluation factors is explicitly handled by
  the canonical Koszul braiding; no sign convention was silently dropped.
- All finite extensions E are quantified, rather than just E = Q_ell or one
  chosen algebraic-closure subfield. Both the prime condition and ell != p remain.

Searches for an existing statement (all through the authorized search paths):

- `msearch.py`, LeanSearch: `derived internal Hom point sections evaluation
  comparison coefficient modules`. Eight results: smooth sheaf evaluation,
  presheaf sections evaluation, scheme evaluation and `LightCondensed.ihomPoints`;
  none states the finite pro-etale derived comparison with the specified counit.
- `msearch.py`, LeanFinder: `derived internal Hom on proetale algebraically closed
  point evaluation comparison`. Eight results, all scheme/ringed-space evaluation
  naturality; none matches.
- `msearch.py`, Loogle: `CategoryTheory.ihom, CategoryTheory.DerivedCategory`.
  No result; the latter identifier is unknown to the search service.
- `msearch.py`, grep in CategoryTheory:
  `rightDerivedGlobalSections.*[Ii]hom|[Ii]hom.*rightDerivedGlobalSections|point.*[Ii]nternalHom`.
  Zero hits.
- `rg` over upstream WeilConjectures, project `lean/Sheaf`, the upstream names
  index and Mathlib: the item id and the new declaration names have no matching
  existing declaration. Point/internal-Hom concept searches find generic
  PointDerivedHomEvaluation and coefficient trace/Hom APIs; these are reused,
  and do not already state the node's normalized map assertion.

Validation: the prescribed single-file scompile.py compile and deliver2.py dry
run are run for this module. No library build or direct repository write is used.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
