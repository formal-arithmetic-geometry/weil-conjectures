## Worker report

Group Q03; stage 2; 2026-10-22. Item: lem-sf-rational-localization-triangle-orthogonality.

The delivery states `WeilConjectures.sfRationalLocalizationTriangleOrthogonality` in
`Sheaf.Paper.SfRationalLocalizationOrthogonality`. Its proof is `sorry`. The conclusion
is `Nonempty (SfRationalLocalizationOrthogonality l E D i j)`; every field below is
therefore asserted by the theorem, rather than assumed. The structures only package
the assertion. The three helper maps are composites of published canonical maps;
no new object or map is chosen from an unspecified existence theorem.

The earlier BLOCKED disposition was not a stage-2 tool failure: Q57's independently
reviewed merge (ledger 2026-10-22 04:48) completed stage 1, and left no `lean` record.
This delivery preserves that reviewed split, including every proof step and its
review record. It supplies the still-missing stage-2 statement.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Global finite-field datum k = algebraic closure of F_q, characteristic p | `D : FiniteFieldDatum.{u}`, with its recorded fields and algebraic-closure instances; base schemes are over `Spec (.of D.k)`. |
| Prime l different from p | `(l : ℕ) [Fact l.Prime]`, `(hl : l ≠ D.p)`. |
| Finite E / Q_l, R and t | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`; the integer ring and uniformizer are exactly `Padic.coefficientExtensionIntegers l E` and `Padic.coefficientExtensionUniformizer l E`, not arbitrary coefficient choices. |
| X separated and finite type over k | `[X.Over (Spec (.of D.k))]`, `[LocallyOfFiniteType (X ↘ Spec (.of D.k))]`, `[QuasiCompact (X ↘ Spec (.of D.k))]`, `[IsSeparated (X ↘ Spec (.of D.k))]`. |
| i closed, j the complementary open | `(i : Z ⟶ X) (j : U ⟶ X)`, `[IsClosedImmersion i]`, `[IsOpenImmersion j]`, `hij : Set.range j.base = (Set.range i.base)ᶜ`. |
| Integral C_T is derived-complete with constructible positive reductions and one uniform interval | The existing `sfIntegralConstructibleCategory l E T`, whose defining predicate is `sfIntegralConstructible`, at all three schemes. No second definition is introduced. |
| Rational category is the raw localization, same objects and tensor Hom, no Karoubi completion | Existing `sfRationalConstructibleCategory l E T`, `sfRationalConstructibleLocalization l E T`, `sfRationalCoefficientEquiv l E`. Rational objects' `.obj` is their very integral object, including torsion objects. |
| Inherited geometric hypotheses needed by recorded APIs | Fields `primeUnit`, `openOver`, `closedOver`, `openIsOver`, `closedIsOver`, the four inherited finite-type/quasi-compact fields, `openQuasiCompactMap`, and `invertibleX/U/Z` are conclusions inside the package. They add no theorem assumptions. The IsOver fields force the inherited structure maps. |
| Actual integral/rational i*, j* | Existing `constructibleIntegralPullback l E i/j` and `rationalDerivedPullback l E i/j`, without substituting alternative adjoint functors. |
| Actual integral j! and rational j! | Existing `sfCompactSupportFiniteIntegralFunctor` and `sfCompactSupportFiniteFunctor`, with precisely `Compactification.ofIsOpenImmersion j`, i.e. (j,id_X). Their fixed object values and action are those of the recorded compact-support definition. |
| Actual integral closed direct image | Existing `FrobeniusExchange.directImageFunctor l E D.k primeUnit i`. Its underlying functor is reduction, actual derived direct image of the whole strict system, and total limit; `FrobeniusExchange.directImage_roos` identifies that very object with the recorded `SfIntegralDirectImage` tower. It is not selected as an unspecified right adjoint. |
| Actual rational closed direct image | Field `closedRationalImage`, fixed on every object and pure tensor by `closedPush.objects/tensors`. These clauses uniquely determine the rationalization of the preceding actual integral action. No definition chooses this functor from mere existence. |
| Four exact R-linear integral counterparts and exact E-linear rationalizations | `closedPull`, `openPull`, `closedPush`, `openPush : SfRationalizedExactFunctor ...`. Its `integralAdditive`, `integralLinear`, `integralShift`, `integralExact`, `rationalAdditive`, `rationalShift`, `rationalExact`, `objects`, `tensors`, `shifts`, `scalar` fields give all parts. The E action is written through the inverse of the canonical localized-coefficient equivalence; `scalar` quantifies over every rational arrow. The `shifts` square compares the rational shift map with Q of the integral shift map and both canonical Q shift comparisons. |
| Specified integral open counit and closed unit | `openIntegralAdjunction`, `closedIntegralAdjunction`, `openCounitNormalization`, `closedUnitNormalization`. The two normalization equations hold in the coherent-system derived category before evaluating any quotient. They fix the open counit by the exact derived system-open counit, and the closed unit by the actual system pullback/direct-image unit. The canonical operation-reduction counit and pullback-to-reduction comparison are retained. |
| Integral open normalization is the recorded compact-support one | `sfLocalizationOpenRealization` first applies the published projection-normalized `FrobeniusExchange.compactRealization` for (j,id), then total limit of the identity direct-image comparison. `sfLocalizationSystemDirectId` is `Adjunction.rightAdjointUniq` for the actual identity adjunction and `integralComparisonSystemUnit`, so this step cannot introduce an arbitrary automorphism. |
| Rational j! adjoint to j*, and i* adjoint to i_*, including all units/counits and arbitrary rational morphisms | `openRationalAdjunction`, `closedRationalAdjunction` are actual Mathlib `Adjunction` values, hence natural on every morphism of the rational categories and satisfying both triangle identities. Fields `openUnit`, `openCounit`, `closedUnit`, `closedCounit` identify every component with Q applied to its specified integral component. HEq handles the literal object-equality transports, not alternative vertices. |
| Open rational counit and closed rational unit are Q(epsilon_R), Q(eta_R) | Specifically `openCounit` and `closedUnit` at every integral K. |
| Every specified distinguished integral completion maps to a distinguished rational triangle | `triangles` quantifies over each integral K and each boundary `δ`, assumes the integral triangle with the actual integral counit and unit is distinguished, and gives a distinguished triangle with the actual rational counit and unit. Its last clause fixes `δE` by HEq to Q(δ) followed by the canonical Q shift comparison. It does not select another integral completion. |
| Arbitrary independent rational N on U, M on Z, every integer m | `orthogonality : SfRationalCrossHom ...` quantifies over independent N,M and `(m : ℤ)`. No same-K or nonnegative-shift restriction appears. |
| Canonical Hom_X,E(j!N[m],i*M) = Hom_X,R(j!Ntilde[m],i*Mtilde) tensor_R E | `SfRationalCrossHom` asserts the uniquely specified additive equivalence, with the exact two Hom types. Its pure-tensor equation first transports by `openPush.objects`, Q's inverse shift comparison, and `closedPush.objects`, then sends `a tensor f` to `f tensor sfRationalCoefficientEquiv a`. This is the recorded `sfRationalHomCoordinates` normalization specialized to the operation/shift vertices, with no new definition of rational Hom. |
| The displayed Hom tensor E group is zero | Both the rational Hom and the displayed integral-Hom tensor E are `Subsingleton`; each is an additive group, so this says precisely that it is zero. |

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, its field and algebraic-closure instances.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`, reexporting the integer ring, chosen uniformizer and quotient constructions from `CoefficientExtension` (the finite-level finiteness is needed in the documented proof, not an extra hypothesis).
- `def-weil-scheme-morphism-properties` is explicitly a convention node with no declaration. Its named notions here are Mathlib `Scheme.Over`, `IsClosedImmersion`, `IsOpenImmersion`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` and `Scheme.Hom.IsOver`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`, `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`, its canonical shift comparison, `sfRationalCoefficientEquiv`, `sfRationalHomCoordinates` and its pure-tensor normalization. This imports the existing integral triangulation and linear structure.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`, `rationalDerivedPullback` and its object/pure-tensor characterization. The node's primary recorded common-stage internal-Hom theorem is not needed for this rational pullback specialization; its signature and docstring were read, and the same record lists the pullback declarations actually used.
- `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage`, `sfDirectImageTerm`, `sfDirectImageTransition`, and its canonical projection-adjoint reduction comparison, used through the normalized system realization.
- `Sheaf.Paper.QcqsCompactSupportRealization`: `SfQcqsCompactSupportRealizationSpec`, `sfQcqsCompactSupportRealization`; used by the published `compactRealization`'s unique projection normalization, without rewriting it.
- `Sheaf.Paper.SystemOperationExchangeRealization`: `FrobeniusExchange.models`, `.reduction`, `.realize`, `.operationReduction`, `.systemDirect`, `.systemAdjunction`, `.systemDerivedOpen`, `.systemDerivedOpenAdjunction`, `.directImageFunctor`, `.directImage_roos`, `.compactRealization`. This reuses `integralComparisonPullbackCounit` and `integralComparisonSystemUnit` from their recorded comparison modules.
- `Sheaf.Paper.CompactSupportFiniteAction`: `sfCompactSupportFiniteIntegralFunctor`, `sfCompactSupportFiniteFunctor`, with the fixed linear and pure-tensor actions.
- Mathlib `CategoryTheory.Adjunction.rightAdjointUniq`, `.ofNatIsoLeft`, `.id`; `Functor.CommShift`, `Functor.IsTriangulated`; `Triangle.mk`, `distTriang`; tensor products and additive equivalences.

The two last operation-definition node IDs were added to stmt_deps because their
published normalized actions occur in the signature helpers. Both already have Lean
records. A read-only dependency traversal found no path from either back to this
item. All existing stmt_deps and every statement/proof field are preserved. There
are no new nodes, dependency module repairs, or statement corrections.

Edge cases checked: U empty, Z empty (including either identity immersion), X empty,
zero N or M, independent N and M not induced by one K, arbitrary and negative m,
E = Q_l, torsion objects that become zero after localization, and arbitrary sums of
fractions that have no integral representative. There are no nonempty, dimension,
cohomological-dimension, torsion-free, finite-Tor, or integral-lift hypotheses. All
universes are explicit; the common scheme/coefficient universe follows the recorded
intrinsic categories, rather than identifying the pro-etale object's u+1 with its
morphism universe u. No hollow data definition and no disputed statement were found.

Searches (through msearch.py and read-only rg/grep):

- LeanFinder, `Raw rational localization of constructible adic sheaves preserves open closed localization triangles and orthogonality`: OK, eight hits. They include affine-Zariski localization, localCohomology.ofDiagram/diagram, ModuleCat.Tilde.Localizations, and `CategoryTheory.Functor.isHomological_of_localization`; no exact normalized constructible open/closed theorem.
- Loogle, `"distinguished", CategoryTheory.Adjunction`: OK, zero hits.
- Mathlib grep, `rational.*orthogon|rational.*localization.*triangle`, subdirectory CategoryTheory: OK, zero hits.
- LeanSearch, `Rationalization of open closed constructible sheaf localization preserves adjunction units and cross object orthogonality`: OK, eight hits, including `CategoryTheory.Adjunction.localization_unit_app`, `.localization`, `.derived`, `.derived'`, `.Localization.η/ε`, the sheaf module direct-image adjunction unit, and the topology sheafification localization unit. These are generic tools, not this node's statement.
- `rg -n 'rational.*orthogon|rational.*localization.*triangle|rationalLocalizationTriangleOrthogonality'` in both `lean/WeilConjectures` and `lean/Sheaf`: found `SfOpenClosedTriangleAllStages` and `SfLocalizationAllStages`. I read both relevant interfaces. The former's `SfRecollementConclusion` gives only same-K vanishing and existence of composite presentations; it does not give all four normalized functors and adjunctions, every specified completion, or independent-object Hom tensor coordinates. The latter is the different supported/exceptional localization triangle. Neither is an exact existing match.
- `grep -rn 'lem-sf-rational-localization-triangle-orthogonality' lean/WeilConjectures`: no hits.
- Name collision rg for all newly introduced full-name components in `lean/Sheaf`, `lean/WeilConjectures` and `dag/nodes`: no existing declaration or definition node with these helper names. The helpers only express this node's own assertion and its canonical normalization maps; no independent mathematical notion is duplicated.

Validation: scompile.py compiled the module separately in sandbox and library module
modes with no errors or warnings (48.0 s / 43.3 s before the final proof-import/docstring
addition). The final module, including all proof imports and documentation, also passed
scompile.py cleanly in sandbox mode (38.4 s) and library-module mode (42.5 s).
The prescribed delivery preflight is run on the final packet.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
