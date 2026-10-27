## Worker report

Item: lem-sf-strict-direct-image-scalar-comparison. The module states the scalar
compatibility theorem, retaining the strict-diagram realization, normalized
reconstruction, ordinary tensor/direct-image normalization, and raw rational maps.
All helper definitions contain actual data; the sole postponed theorem has the
node's eight-step proof in its docstring. The theorem asserts existence of a fully
normalized comparison system, not an arbitrary unnormalized natural isomorphism.

Hypotheses and clauses, checked with the node and Lean file open:

- Prime: `(l : ℕ) [Fact l.Prime]`. Field and invertibility: `(k : Type u)
  [Field k] (hl : IsUnit (l : k))`. No finite-field hypothesis is imposed.
- Algebraic closure: `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]`. The closure universe v is independent of u.
  `Index l Ω` ranges over every finite intermediate extension. The published
  `Coefficient.{u}` model is the existing small field model; its specified
  `coefficientInclusion` is used for every inclusion. This uses the landed
  def-weil-algebraically-closed-coefficients, added to stmt_deps.
- Schemes: `Scheme.{u}`, both `Over (Spec (.of k))`; structural maps have
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`. Together the first
  two express finite type, and `f.IsOver` expresses a morphism over k.
- Coefficients and categories: existing coefficient-extension valuation rings,
  chosen uniformizers, completed integral sheaves, and
  `sfIntegralConstructibleCategory` throughout. These are the intrinsic bounded
  constructible, derived-complete categories. No replacement category is defined.
- The strict realization is retained in `IntegralModel`: `Representatives` is
  the existing flat-term K-flat class restricted to constructible localizations;
  `strictReduction` curries the existing unrestricted reduction functors and
  transitions. `strict_identification` identifies the entire strict diagram,
  including transitions. `realization` applies Q, total derived direct image in
  the strict diagram category, then total derived limit. It is a natural
  isomorphism on representatives, not a collection of levelwise identifications.
  The positive-index conventions are inherited from the existing reduction
  functors (index n means the positive quotient n+1).
- `diagrams : CompletedCoefficientPushforward.ComparisonData` retains its finite
  coefficient comparisons, restriction comparisons, derived universal units,
  strict limit comparison, and normalized augmentation. `structureMap` fixes the
  actual completed coefficient map. `ambient_unit` fixes the comparison with
  `sfCompletedDerivedDirectImage` by its universal derived unit.
- `reconstruction` is the natural comparison F_E → I_E. Its normalization is
  the exact augmentation followed by the recorded strict limit comparison on
  every good representative. The augmentation premise spells out its quotient
  sections after the strict identification, including all site objects and
  degrees. It is not uniqueness from evaluated projections.
- `additive` and `linear` state R_E-linearity of I_E. `scalars` is the constant
  scalar square for the published constant-section action on the ambient derived
  category; thus it uses the completed, rather than discrete, coefficient sheaf.
- `ordinary` and `ordinary_tensors` fix the ordinary completed scalar/direct-image
  map on sheafified tensor generators. `AmbientComparison.ambient` and `IsAmbientNormalization` fix
  its total-derived comparison by the unit/counit square. The direction is
  C_X F_E → F_L C_Z, so the integral comparison uses its inverse.
- `integralComparison` has direction S_Z ⋙ I_L ≅ I_E ⋙ S_X, namely
  I_L S_Z → S_X I_E in mathematical composition order.
  `IsIntegralNormalization` is the node's conjugation formula with the recorded
  `completedScalarComparison` χ and reconstruction ψ. It is expressed as the
  square before cancellation of the invertible χ_Z, which is equivalent on these
  complete inputs. The unit clause in `HasIntegralLaws` uses the prescribed identity coefficient
  transport followed by `sfIntegralScalarUnit`.
- `rational` takes values in the existing raw `Stage` categories, not a Karoubi
  envelope. The object clause of `HasComparisonLaws` leaves the integral representative as the object;
  `IsRationalMaps` sends every pure localized tensor a ⊗ g to a ⊗ I_E(g).
  The identity clause of `HasComparisonLaws` fixes the comparison with localization to the literal
  identity on each object. These equations specify the actual rationalization.
- `theta` is a natural isomorphism between the specified rational transition
  composites. The component clause of `HasComparisonLaws` makes its components the literal localized
  integral comparisons. The two `NatTrans.CommShift` clauses of `HasComparisonLaws`, with
  `reconstruction_shift`, record compatibility with integer shifts, using the
  existing normalized transition shifts.
- The unit clause of `HasComparisonLaws` is precisely the equality under the prescribed `unitor`.
  The cocycle clause of `HasComparisonLaws` is the node's displayed equality with its order unchanged:
  θ_M/L(T_L/E K), then T_M/L(θ_L/E), then a_X, equals I_M(a_Z), then θ_M/E.
  Here `associator` is the published coefficient-inclusion transport of
  `sfRationalScalarComp`. No full-faithfulness clause occurs.

Dependency declarations used (modules are public statement imports, and the
recorded proof dependencies are plain proof imports):

- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  Padic.finite_coefficientExtensionRing and its valuation-ring/quotient data.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and ProEt.topology.
- Sheaf.Paper.CompletedIntegralConstantMapOfUniverses:
  integralConstantToCompletionOfUniverses and the completed coefficient sheaves.
- Sheaf.Paper.SfIntegralConstructible: sfIntegralConstructible and its full category.
- Sheaf.Paper.SfDerivedDirectImage: sfCompletedCoefficientMap,
  sfCompletedModuleDirectImage, sfCompletedDerivedDirectImage; the recorded
  SfIntegralDirectImage supplies objectwise Roos data, while this item's
  IntegralModel retains the additional functorial strict realization required here.
- Sheaf.Paper.FiniteDirectImageComposition: finiteDirectImageComposition. Its
  recorded declaration covers finite coefficients; the needed strict integral
  realization is explicitly retained as owning-node helper data in IntegralModel.
- Sheaf.Paper.SfIntegralDirectImageConstructible:
  sfIntegralDirectImage_constructible and its intrinsic constructible predicates.
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations:
  proEtaleConstantRingDerivedPullback; ordinary completed direct image is the
  completed-coefficient specialization already published in SfDerivedDirectImage.
- Sheaf.Paper.CompletedCoefficientPushforwardComparison:
  CompletedCoefficientPushforward.comparison and ComparisonData, including its
  normalized strict total-derived direct image and derived limit.
- Sheaf.Paper.SfIntegralConstructibleLinear: sfIntegralConstructible_linear,
  sfIntegralCoefficientLinear, sfIntegralConstructibleLinear.
- Sheaf.Paper.IntegralScalarExtensionUniverses:
  integralScalarExtensionOfUniverses.
- Sheaf.Paper.PbcScalarExtension: pbcCoherentScalarExtension. Its general ambient
  comparison is specified here in the completed-sheaf presentation by the ordinary
  tensor generator and derived unit/counit equations, rather than replaced by an
  arbitrary map or by an assumed isomorphism.
- Sheaf.Paper.FiniteFreeCompletedScalarComparison:
  completedDerivedScalarExtension, completedOrdinaryScalarExtension,
  completedScalarCounit, completedScalarTensorSection, completedScalarComparison,
  and finiteFreeCompletedScalarComparison.
- Sheaf.Paper.SfRationalizationKaroubi: sfRationalConstructibleCategory,
  sfRationalConstructibleLocalization.
- Sheaf.Paper.SfScalarExtensionComposition: sfIntegralScalarUnit,
  sfRationalScalarComp and sfRationalScalarUnit.
- Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients: Stage, integralTransition,
  transition, associator, unitor, and their fixed shift structures; its publicly
  imported AlgebraicallyClosedCoefficients provides Index, Coefficient and
  coefficientInclusion. Using p=0 in this existing interface is a proof-only
  parameter choice; it imposes no characteristic restriction on k.

Edge cases: zero objects and zero morphisms are included by the full category and
pure-tensor formulas. Empty schemes are permitted; no nonemptiness hypothesis is
added. Identity inclusions E=E are covered explicitly, and the cocycle quantifies
over weak inclusions, so E=L, L=M, and E=L=M are included. The characteristic of k
may be zero or any characteristic different from l. Closure and site universes
remain independent. There is no degree bound, cohomological-dimension hypothesis,
properness assumption, or finite-field datum. No statement correction or
STATEMENT-DISPUTED issue was identified.

Searches: msearch.py leanfinder, query “Strict reduction tower derived direct image
is linear and commutes coherently with finite coefficient scalar extension and
rationalization”, returned eight unrelated tensor/cotangent/adic algebra hits and
no strict-tower comparison. msearch.py loogle, query
“CategoryTheory.Functor.Linear”, returned the basic linear functor API, not the
comparison. msearch.py grep, query “directImage.*[Ss]calar|[Ss]calar.*[Dd]irectImage”
in CategoryTheory, returned no match. rg on lean/WeilConjectures and lean/Sheaf for
the item id and strict-direct-image/scalar comparison names found no existing
statement; related declarations above were read and reused. The proposed namespace
WeilConjectures.SfStrictDirectImageScalar did not exist. The current blueprint at
literature/blueprint/latest was read; its current closed-unit proof no longer has
the historical scalar paragraphs named in this supplemental node's source. This
delivery retains the node's detailed statement and proof rather than modifying it
on that account.

## Second reading by Q43

The dispatcher explicitly forbids starting another agent and assigns independent
review to the maintainer. Accordingly this is a second pass by the same worker,
not a claim of an independent worker review. I reread the node and full signatures
against the clause list above. The important checks were the direction of β versus
the integral comparison, the order of all three cocycle factors, identity
inclusions (including repeated fields in a triple), the raw rational Hom formula,
and independence of the algebraic-closure universe. During elaboration I corrected
the RingCat/CommRingCat structure-map transport and the parenthesization of the
constant-scalar square. The augmentation normalization compares the entire strict
chain diagram, not just its evaluated inverse-limit projections. No additional
hypothesis or weakening was introduced.

The final helper organization separates comparison data from its large law types:
`IsAmbientNormalization` fixes the universal derived square; `IsIntegralNormalization`
fixes conjugation; `HasIntegralLaws` adds the integral unit; `IsRationalMaps` fixes the
pure-tensor action; and `HasComparisonLaws` packages objects, localized components,
shifts, units and cocycle as a conjunction. The final existential theorem includes
both data records and all these predicates. This refactoring changes no equation.
`stageLocalization` names the published localization with its existing `Stage`
target; `stageLocalizationShift` is the existing `sfRationalLocalizationCommShift`,
not a new choice. The two broad CompletedCoefficientPushforward instance overrides
are temporarily disabled and restored with their original priorities at the end to avoid a phantom universe in instance search; the published
standard sheaf-module and derived-category instances remain the same.
