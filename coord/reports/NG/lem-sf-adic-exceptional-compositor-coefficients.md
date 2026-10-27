## Worker report

The delivery states `WeilConjectures.AdicExceptionalCompositor.adicExceptionalCompositorCoefficients` in `Sheaf.Paper.AdicExceptionalCompositorCoefficients`. Its proof is `sorry`; no mathematics is proved. The separate definition module `Sheaf.Paper.AdicExceptionalCompositorCoefficientsData` packages the precise system realization conclusions. Its new definition node is described below. Every definition has actual data, and the only postponed theorem is the item's theorem.

Hypotheses and coefficient conventions:

- `D : FiniteFieldDatum` and `B : D.CoefficientDatum` give the algebraic closure of the finite field, the prime and the different-characteristic assumption. `FieldStage B.l` retains a field, its Q_l-algebra structure and finite dimension. Integral rings, chosen uniformizers and quotient rings are exactly `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and `coefficientExtensionRing` used by the dependencies.
- `X Y Z : SixFunctorSpace D` are the existing finite-type k-spaces. The three `IsSeparated ...obj.hom` instances are explicit theorem hypotheses. The separated, locally-finite-type and quasi-compact instances on the two underlying maps render separated finite-type f and g. The composite is `(f ≫ g).hom.left`, with the existing composition instances.
- `P Q R : ConstructibleExceptionalCoefficients.System` are the specified constructible adjunctions, including their counits, finite-Tor finite categories, derived-complete integral categories, raw rational categories and common-finite-stage categories. No unrestricted ambient exceptional adjoint is assumed.
- `S` gives the recorded six-operation data at each finite field and positive exponent. `A : LeftCompositors ... S` renders the canonical alpha of the node: its finite and integral fields equal the canonical lifted compactification compositors, and its rational/common fields retain the actual localization/component equations. The three compactifications are arbitrary, not extra geometric hypotheses. `exceptionalIso` is literally `conjugateIsoEquiv` applied to alpha inverse, with the prescribed composite adjunction.

System clauses:

- `domain` is the intersection of the existing `FiniteAdjunctionDiagram.domain` with `IntegralSystemRealization.Good`. This is the ordinary derived category of actual module sheaves on the coefficient sequence site, not diagrams in derived categories. `Good` includes normalization, common finite cohomological and Tor intervals, and `Nonempty (Origins ...)`. `Origins` retains actual etale antecedents, their evaluated-fiber isomorphisms, their transitions, and both origin/transition squares. The finite-Tor predicate is retained literally as well, so restriction of evaluation uses the dependency's existing witness rather than a new Tor-amplitude implication theorem.
- `Reconstruction` contains the reduction/total-limit calculus and its restricted equivalence. Its `reduction` and `limit` fields are equalities with the actual functors after full inclusions. The `unit` and `counit` fields identify the actual maps, not merely objects.
- `SystemOperation` provides F, G and F adjoint to G as conclusion data. `left` identifies F with the actual strict-system proper/open support functor. `finiteLeft`, `finiteRight` and `finiteCounit` are the two evaluation identifications and preservation of the specified counit. Their integral counterparts preserve the actual integral counit under total limit.
- `Realization.alpha` is an actual natural isomorphism. `canonical` identifies its left map with `FiniteFreeCompactComposition.compositor`, including the canonical triangle word and graph common-refinement transports. Thus proper/open interchange and nesting are the actual maps in this existing word. `finiteLeft`/`integralLeft` identify its evaluations and total-limit map with alpha at the corresponding stages.
- `Realization.finiteRight`/`integralRight` state the component equations identifying the actual system conjugate with the finite/integral conjugates under the specified comparison isomorphisms. These quantify over every system object, so they identify natural maps, not only isomorphism classes. The conjugate is a natural isomorphism by its very type. `reductionBeforeLimit` is naturality of the actual reconstruction counit on that system map; it is an equality in the full derived-system category, as required for integral reduction.

Coefficient clauses:

- `RightEquation` is exactly the displayed equation, in Lean's left-to-right composition convention: `TX.map c_s ≫ bx = bf ≫ Gf_t.map bg ≫ c_t`. It quantifies over every L in the source constructible coefficient category.
- `RingEquations` is precisely integral reduction to every positive exponent and completed extension for every field embedding. `FieldEquations` is the conjunction of raw rationalization, every rational field embedding, and common-finite-stage inclusion. The field objects and maps are the actual dependency functors; no finite evaluation is applied to rational or common arrows.
- Two independently recorded restricted scalar functors at the same endpoint are canonically identified using `scalarIso`: lift their two ambient derived-extension realizations through the fully faithful full-subcategory inclusion. `sharedLeft` and `sharedRight` transport the q and b comparisons along this unique identification. The square therefore uses the recorded normalized coefficient mates, with no artificial equality of independently chosen restrictions.
- `SystemScalar.actual` identifies the whole-system functor with `integralComparisonDerivedSequenceScalar`, the actual universal cochain-normalized derived change of rings on the sequence site. `limit` identifies it with the prescribed completed scalar functor under the two reconstruction equivalences.
- `SystemComparison.counit` fixes the actual system right comparison by its counit mate equation. `leftLimit` and `rightLimit` identify both maps with the specified integral q and b. Thus the theorem does not assume coefficient commutation as a hypothesis.
- `SystemChange` concludes existence of tX, tY, tZ and the three system comparisons. `leftEquation` is the system compact-support scalar/composition square; `equation` is the displayed exceptional square itself as an equality of actual derived-system morphisms before total limit. `rightLimit`, `integralRight` and `SystemScalar.limit` identify its total-limit equation with `RingEquations`.
- `RamifiedScalar` uses `ramifiedRings` at exponent `e*(n+1)` and actual quotient transitions. `he` is the recorded ramification ideal equality, not an equality of uniformizers. `commutes` is the actual quotient square. `scalar` is `SemilinearSections.ScalarSystems` on precisely these ring sheaves and maps; its change-of-rings model and tensor/restriction adjunction retain their universal cochain counits. `comparison` is an isomorphism of entire derived functors from this finite-free system tensor to the specified whole-system scalar after cofinal restriction.
- `CofinalRestriction.ordinary` is fixed on every section, every morphism and every horizontal/vertical restriction by the literal subsequence `e*(n+1)-1`; its derived functor is exact localization. `cofinality` includes every target exponent. This retains ramification, including e=1, and neither replaces the target level en by n nor posits arbitrary finite-level lifts.
- `Coherence.realization` chooses the system realization simultaneously for all finite coefficient fields; `extensions` supplies the ramification index and actual system-change data for every embedding, including identity embeddings. All these are existential conclusion data. The theorem concludes the coefficient equations and `Nonempty Coherence` together.

Dependency declarations used (modules and names):

- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: the recorded coefficient and derived-category framework of `sk-def-sf-setting`.
- `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum`, `SixFunctorSpace` and their canonical support compositors.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `conjugateEquiv`, `conjugateIsoEquiv` (the mathlib match of the conjugation dependency).
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and its public data module: `FieldStage`, `Stage`, `C`, `Operation`, `Comparison`, `Scalar`, `RingStage`, `Allowed`, `System`, `rationalization`, `rationalScalar`, `commonInclusion`.
- `Sheaf.Paper.ConstructibleExceptionalCompositor`: `LeftCompositors`, `exceptionalIso`, finite/integral alpha and the map-property framework. The pure definitions are cited through definition ownership records, not the compositor theorem.
- `Sheaf.Paper.CartesianSectionAdjointMates`: the actual system-adjunction and finite-mate-evaluation framework; `FiniteAdjunctionDiagram.domain` from its public data dependency.
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`: canonical system composition realization and its public `IntegralSystemRealization.Good`, `Origins`, `scalarRings`, `scalarTransitions`.
- `Sheaf.Paper.FiniteFreeCompactComposition`: `support`, `compositor` with proper/open and graph-refinement words.
- `Sheaf.Paper.IntegralComparisonSequenceSystems`: `integralComparisonDerivedSequenceScalar` and its actual quotient ring map/cochain normalization.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`: recorded `originComposition`, used through the canonical finite compositor interface. Proof-dependency modules with Lean records are imported plainly in the theorem module. The two proof-only nodes without Lean records are not treated as missing statement notions: no declaration of either is used in the signature.

Edge cases checked: positive exponents are `ℕ+` or n+1, so exponent zero is not silently included. Identity embeddings and e=1 remain in `Coherence.extensions`. Empty schemes and zero systems are admitted; bounds are existential ordered finite intervals and no nonemptiness hypothesis is imposed. Arbitrary finite ramification is retained with positive e and cofinality at every target exponent. Rational and common-stage equations quantify over their actual categories, including all localized/common-representative morphisms. No finite evaluation faithfulness or claim that arbitrary families of derived arrows lift is present. Coefficient/sheaf universes use the existing small pro-etale site (objects u+1, morphisms u), with coefficient rings lifted to u+1; no equality of those universes is imposed.

Searches:

- msearch LeanFinder: “The conjugate of compact support composition is compatible with coefficient change and derived inverse limit realization”; eight adic-completion hits, no exact theorem.
- msearch Loogle: `CategoryTheory.conjugateEquiv, CategoryTheory.conjugateIsoEquiv`; four application lemmas for the existing conjugation equivalence.
- msearch Mathlib grep: `conjugateIsoEquiv|conjugateEquiv_apply_app` in `CategoryTheory/Adjunction`; existing Mates/Unique/CompositionIso declarations, reused.
- msearch LeanSearch: “Compatibility of the conjugate exceptional composition natural isomorphism with completed scalar extension of strict adic systems”; eight hits, including `conjugateEquiv_comp`, no scheme/system theorem.
- rg of `lean/WeilConjectures`, `lean/Sheaf`, and upstream declaration index for exceptional composition/system realization: found and reused the constructible compositor and actual coefficient/system interfaces above. Exact item-id search upstream found no declaration.
- `tools/blueprint_refs.py search 'adic exceptional compositor realization'`: no blueprint definition match. DAG grep found the theorem item and related finite/system statements, but no node for its combined realization datum. The existing `Good`, `Origins`, finite-adjunction domain, scalar functors and support maps are reused rather than redefined.

No statement correction and no STATEMENT-DISPUTED issue. The sole sorry has the complete natural-language proof in its docstring. Validation uses scompile.py on every delivered module and deliver2.py preflight/dry run.

## New nodes

`def-sf-adic-exceptional-compositor-realization-data` defines the node-specific reconstruction, adjunction realization, canonical compositor realization and coefficient-square predicates. Its own module is `Sheaf.Paper.AdicExceptionalCompositorCoefficientsData`. Its source is the newest blueprint Verdier-exchange proof's final compatibility sentence, expanded using the recorded ordinary strict-system framework. It adds no mathematical existence theorem and no copy of an underlying category or scalar construction. The three search kinds, DAG/blueprint search and source searches above are recorded in its mathlib_searches. The item cites it directly; it cites the landed underlying interfaces. The ramified-system helpers now have their own definition module and node; the final coherence helpers remain in the theorem module.


`def-coef-system-compact-support-compositor`: Let C be a tower of commutative coefficient rings with adjacent transition maps. Use the actual semilinear system operations [def-sp-semilinear-constant-ring-operations] and their unit/counit-normalized comparisons [def-sf-semilinear-proper-open-comparisons], [def-coef-semilinear-proper-open-mate]. For a compactification c=(j,p) [def-weil-compactifications-refinements], define support C τ c to be J_j followed by R_p. Define refinement by the open-unit gamma and proper compositor. Define change between compactifications using the canonical graph common refinement, inverting the second refinement on its isomorphism domain. Define triangleWord by proper/open interchange and the open and proper compositors of a compatible compactification triangle. For composable quasi-compact maps and compactifications cf,cg,cfg, compositor is change to the canonical compactification triangle, triangleWord, then change back to cfg, on each actual derived system object. These are specified maps before finite evaluation or inverse limit. Its recorded module is `Sheaf.Paper.FiniteFreeCompactComposition`; the published definitions are reused with existing:true. Source: the current blueprint complement and final compatibility sentence, as recorded in source. The recorded LeanSearch, LeanFinder/Loogle, Mathlib grep, project-source and DAG/blueprint searches found no existing definition owner of this complete notion.

`def-pur-finite-compact-support-realization-map`: For the finite quotient coefficient ring at exponent n+1 [def-weil-l-adic-coefficient-extension] and the actual ringed compact-support construction [def-pur-integral-compact-support-coefficient-data], define finiteImageIso to identify image at that finite ring with the intrinsic compact-support candidate [def-compact-support-direct-image-detailed]. The open factor is localization of the unique comparison of the two ordinary open adjunctions under the canonical inverse-image coefficient transport; the proper factor is the right-derived image of the identity transport between their ordinary direct images. Thus this is the prescribed proper/open comparison, preserving the open unit and the separately derived proper unit, on all derived objects and morphisms. Its recorded module is `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`; the published definitions are reused with existing:true. Source: the current blueprint complement and final compatibility sentence, as recorded in source. The recorded LeanSearch, LeanFinder/Loogle, Mathlib grep, project-source and DAG/blueprint searches found no existing definition owner of this complete notion.

`def-sf-exceptional-compositor-coefficient-data`: Fix the setting [sk-def-sf-setting], operations [sk-def-sf-operations], and normalized constructible adjunction systems [lem-sf-constructible-exceptional-adjunction-coefficients]. Reuse the finite compact-support compositor and its exceptional conjugate [def-sf-finite-exceptional-compositor-maps]. For composable separated finite-type maps f:X→Y and g:Y→Z and systems P,Q,R, define integralInclusion as the finite-Tor integral full-subcategory inclusion. Define integralLeft as the normalized comparison of P with the specified integral compact-support functor. Define integralAlpha by pasting integralLeft for g and f, the inverse specified compact-support compositor [thm-sf-comp-composition], and inverse integralLeft for gf, lifted through the fully faithful inclusion. Define LeftCoefficientEquation as equality on every object of the two paths made from a left compositor and three specified left scalar comparisons. Given six-operation data S at each finite field and positive exponent, LeftCompositors consists of alpha at every coefficient stage and compactification triple, with finite alpha equal to finiteAlpha, integral alpha equal to integralAlpha, and LeftCoefficientEquation for the prescribed rationalization and common-finite-stage maps. This is a data type and does not assert its existence. Its recorded module is `Sheaf.Paper.ConstructibleExceptionalCompositor`; the published definitions are reused with existing:true. Source: the current blueprint complement and final compatibility sentence, as recorded in source. The recorded LeanSearch, LeanFinder/Loogle, Mathlib grep, project-source and DAG/blueprint searches found no existing definition owner of this complete notion.

`def-sf-integral-compact-support-realization-map`: Fix the finite-field datum [def-weil-finite-field-fiber] and completed coefficients. For normalized system operations [def-sf-integral-system-operations] and their realization data [def-sf-integral-system-realization-data], a compactification c=(j,p), and an integral constructible object K, define directIdentification from the total limit of the system compact-support word on the reduction of K to the prescribed integral compact-support object. Its factors are the canonical proper/limit conjugate and the open reduction mate of [def-sf-integral-system-canonical-bridge], the inverse reconstruction unit (inverseOrZero on its isomorphism domain), and the prescribed strict-quotient integral realization [def-weil-integral-rational-qbar-compact-support]. This fixes a morphism independently of any composition comparison theorem. Its recorded module is `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge`; the published definitions are reused with existing:true. Source: the current blueprint complement and final compatibility sentence, as recorded in source. The recorded LeanSearch, LeanFinder/Loogle, Mathlib grep, project-source and DAG/blueprint searches found no existing definition owner of this complete notion.

`def-sf-ramified-scalar-cochain-normalization`: Given the actual ramified system scalar realization and its ordinary tensor-unit normalization [def-sf-ramified-system-scalar-realization-data], define RamifiedScalarNormalization to mean the following equality on every normalized system M, every cochain complex C and every identification M≅Q(C): the ramified comparison followed by the universal scalar counit equals the whole-system scalar counit, exact cofinal-localization factorization, and localization of the ordinary comparison, in that order. Thus the map is specified before total limit and not inferred from equality of its finite components. Its recorded module is `Sheaf.Paper.AdicRamifiedScalarCochainNormalization`; all definition data is written in full in this delivery. Source: the current blueprint complement and final compatibility sentence, as recorded in source. The recorded LeanSearch, LeanFinder/Loogle, Mathlib grep, project-source and DAG/blueprint searches found no existing definition owner of this complete notion.

`def-sf-ramified-system-scalar-realization-data`: Fix the actual coefficient fields, normalized domains and system scalar realizations of [def-sf-adic-exceptional-compositor-realization-data]. For E→L with positive ramification index e and its recorded ideal equality, define the ramified tower at n to be the quotient at e(n+1), with its actual quotient transition. A CofinalRestriction datum is literal ordinary restriction to the subsequence e(n+1)-1 on every section object, section map and horizontal and vertical restriction, retaining exactness. A RamifiedScalar datum uses the actual compatible ramified ring maps and the universal derived scalar tensor/restriction adjunction of [def-coef-semilinear-derived-calculus]. Its comparison with whole-system scalar change is normalized before localization: the ordinary comparison sends a scalar-unit generator at e(n+1)-1 to the scalar unit of its actual quotient transition to n. Include cofinality at every target exponent. These data assert no existence. Its recorded module is `Sheaf.Paper.AdicRamifiedScalarRealizationData`; all definition data is written in full in this delivery. Source: the current blueprint complement and final compatibility sentence, as recorded in source. The recorded LeanSearch, LeanFinder/Loogle, Mathlib grep, project-source and DAG/blueprint searches found no existing definition owner of this complete notion.

## Second reading by NG

The dispatcher brief assigns independent review to the maintainer; no second worker was started. A final self-audit compared the node clause by clause with the delivery files: it added the explicit separated-space hypotheses; replaced a levelwise-only domain by the existing compatible-origin/common-bound domain; retained the identity and ramified cases; added rightLimit so realization identifies the actual b maps; restricted ring equations to exactly the two integral changes in the node; and retained the entire pre-limit equation and literal cofinal restriction on maps. This is not represented as an independent reading.


## Repair of immutable head ee56a91e3c6f

H2 is repaired by definition ownership. The original seven statement dependencies on current
main are retained byte for byte. The extra edge to
lem-sf-constructible-exceptional-compositor has been removed. Both the item and the realization
data cite def-sf-exceptional-compositor-coefficient-data for LeftCompositors, integralAlpha,
integralLeft and LeftCoefficientEquation. Its finite ingredients cite the already landed
N9 definition node def-sf-finite-exceptional-compositor-maps. No existential conclusion of the
constructible compositor theorem is being used to type P, Q, R or A. The realization data
now cites def-coef-finite-adjunction-system-data for the cartesian record;
def-sf-integral-system-realization-data and def-sf-integral-system-canonical-bridge for integral
operations; and def-coef-system-compact-support-compositor for the actual support word. None
of the three theorem edges singled out in H2 remains in the new definition node.

H3 is repaired by OperationNormalization, required for each of f, g and gf in Realization.
Its cartesian field is literally FiniteAdjunctionDiagram.Realization, from the dependency's
data module. F and G are equalities of functors after cartesianInclusion, not freely chosen
isomorphisms; the adjunction unit and counit are HEq to cartesian.adjunction. finiteLeft is
cartesian.supportEvaluation after the specified P.ring.left and canonical finiteImageIso;
finiteRight is cartesian.exceptionalEvaluation after P.ring.finiteRight. Thus both evaluations
are pinned as maps, rather than being constrained only by a mate equation.

supportPresentation is a real construction: transport the dependency's open adjunction
through the section-identity CanonicalBridge.pull and use leftAdjointUniq; transport its proper
adjunction through that same pull comparison and use rightAdjointUniq. Their composite lands
in exactly FiniteFreeCompactComposition.support. OperationNormalization.left identifies U.left
with cartesian.supportIso followed by that constructed presentation. In particular twisting
opx.left by minus one while changing alpha no longer satisfies the normalization. The
cartesian record and the canonical presentation now control the system compositor itself.

The reconstruction calculus is equal to IntegralSystemRealization.calculus. Its reductionObject
field is equality of the actual reduction object obtained from reduction and calculus_eq;
this is proof data, and chooses no new map. OperationNormalization.integralLeft is the precise
whole-system map: total limit of U.left, inverse operationSupportPresentation, the actual inverse
reconstruction counit and equality of reduction coordinates, then
IntegralCompactificationBridge.directIdentification. The latter is the existing whole-system
proper-limit conjugate/open-reduction/inverse-unit/strict-quotient realization. The integral
right identification is uniquely determined by integralCounit, with this fixed left map and
the fixed adjunctions; no finite-evaluation faithfulness is invoked. Consequently the finite
and integral right-compositor equations concern the dependency's maps, not maps engineered
only to make mate calculus work.

SystemScalar.actual_eq pins T on the ambient full subcategory and actual_canonical makes
actual exactly eqToIso of that equality. limit_canonical pins the limit map to actual,
the inverse reconstruction counit, and the inverse of IntegralComparisonScalarModel.realization;
that model retains its ordinary pure-tensor and universal cochain normalization. For
SystemComparison, leftLimit and rightLimit now uniquely determine left and right: equiv.inverse
is fully faithful, and all other factors are these fixed realization maps and the dependency's
prescribed q and b. These are therefore canonical lifts, with no residual scalar twist.
The counit equation is a further required compatibility, rather than their only normalization.

RamifiedScalarNormalization additionally fixes the ordinary comparison on scalar-unit
generators using the literal quotient transition from e(n+1)-1 to n. comparison_model identifies
the derived comparison on every complex presentation by the universal cochain counits.
This retains arbitrary positive ramification and includes e=1, all identities and all cofinal
levels. It is required by SystemChange.normalizedX/normalizedY/normalizedZ. The ramified data
is extracted into its own definition module so each file respects the 60-second compile limit.

The displayed RingEquations and FieldEquations are unchanged. No hypothesis or clause of the
item's mathematical statement changed; the separated-space binders moved to the geometry
section solely so that all dependent realization structures can use them. No statement_change
is needed. The source remains literature/blueprint/latest; the complement uses exactly the
compact-support compositor and its adjunction mate, with compatibility inherited from those
ingredients. No definition contains sorry, and the sole theorem proof remains sorry.

Additional new definition ownership records (all existing:true; no copied Lean definitions):

- def-sf-exceptional-compositor-coefficient-data: the recorded LeftCompositors and its integral
  and coefficient-equation ingredients in Sheaf.Paper.ConstructibleExceptionalCompositor.
- def-coef-system-compact-support-compositor: support, refinement, change, triangleWord and
  compositor in Sheaf.Paper.FiniteFreeCompactComposition.
- def-sf-integral-compact-support-realization-map: the actual directIdentification in
  Sheaf.SixFunctors.IntegralCompactificationComparisonBridge.
- def-pur-finite-compact-support-realization-map: finiteImageIso in
  Sheaf.Paper.IntegralCompactSupportCoefficientComparison.

The new def-sf-ramified-system-scalar-realization-data owns the extracted
Sheaf.Paper.AdicRamifiedScalarRealizationData module: ramifiedRings, ramifiedTransitions,
CofinalRestriction, RamifiedScalar, RamifiedOrdinaryNormalization and RamifiedScalarNormalization. This is the previously
item-owned notion with its ordinary and universal cochain map normalization made explicit.

Repair searches used msearch LeanSearch (normalized adic support composition), LeanFinder
(canonical strict-system compositor), Loogle (Adjunction.leftAdjointUniq), Mathlib grep
(LeftCompositors|supportPresentation|systemLeft|systemRight), rg of both project source trees,
DAG definition-owner scans and blueprint_refs.py search compositor. Full queries and returned
hits are recorded in each new node. They found generic adjunction infrastructure, the existing
N9 finite owner and the exact published definitions above, but no existing definition owner
for these remaining notions. The ordinary and derived ramified normalization is node-specific
and not an existing scalar extension copied privately. All native scalar, site, tensor and
adjunction notions are the dependency declarations.

The ramified normalization is split into ordinary generator normalization and derived counit normalization to keep the generated record projections small. No mathematical clause is removed by this interface split.

`def-sf-ramified-scalar-cochain-normalization` separately owns the derived predicate in Sheaf.Paper.AdicRamifiedScalarCochainNormalization; the ordinary generator normalization remains in AdicRamifiedScalarRealizationData. This final separation preserves both equations while reducing per-file elaboration.

Validation: scompile.py compiled all four delivered files separately in dependency order with no errors or warnings. The initial dry-run metadata check caught a signature truncated at a named-argument :=; the JSON record now contains the full signature up to the body delimiter.
