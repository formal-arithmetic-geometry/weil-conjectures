## Worker report

The two modules define the finite-operation realization data and state their existence with the full compatibility package. The theorem module states the finite-operation realization in the ordinary unbounded derived
category of strict semilinear systems on the coefficient sequence site. Every theorem
has proof `sorry`; definitions contain actual categorical data and composites.
Positive exponent n+1 is represented by the natural index n throughout, consistently
with all recorded coefficient-system and finite-exceptional dependencies.

The current main-20261015 finite-exceptional statement and proof and the first two
paragraphs of the integral-exceptional-adjoint proof were read. The item's additional
coherent-system obligation is implemented directly on the ordinary derived sequence
site, following its repaired eighteen-step proof; no higher-category adjoint-mates
or dg right-adjoint interface is introduced.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Algebraic closure of the fixed finite field, characteristic p | `D : FiniteFieldDatum.{u}`, base `Spec (.of D.k)` |
| Prime ell different from p | `(l : ℕ) [Fact l.Prime]`, `hl : l ≠ D.p` |
| Finite coefficient extension, its valuation ring and uniformizer quotients | `E : Type u`, `Field E`, `Algebra ℚ_[l] E`, `FiniteDimensional ℚ_[l] E`; all rings and ring maps are the recorded `Padic.coefficientExtensionRing`, sequence ring sheaves and quotient maps |
| X and Y separated finite type over k | `Over (Spec (.of D.k))`, structural `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` instances on both schemes |
| f separated finite type over k | `f : X ⟶ Y`, `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` |
| Fixed compactification f = pj | `c : Compactification f`, using its actual `i`, `g`, `Z`, `comm` |
| Strict semilinear category and its ordinary derived category | Existing `coefficientSequenceModules` and `coefficientSequenceDerived` |
| R, L, I, H from the evaluation calculus | `CoefficientDerivedSystemCalculus`, `coefficientSequenceLimit`, `coefficientSequenceInternalHom`, `coefficientSequenceGlobalHom`; main theorem supplies recorded resolution coherence |
| Full normalized subcategory with every level bounded constructible and finite Tor | `domain`: `IsNormalizedCoefficientSequence ... M ∧ ∀ n, FiniteExceptional.domain ... (eval_n M)`; `ObjectProperty.FullSubcategory` |
| No common level bound | No bound is quantified outside `∀ n`; no `LevelBounds`, integral-model, or uniform lower-bound predicate is used |
| Actual system compact support Rp*j! | `Support.functor`, exact ordinary extension localized followed by universal right-derived proper image; `Realization.supportIso` identifies F on objects AND maps |
| Actual exceptional system functor | `Realization.G` with `F ⊣ G`, hence actual natural unit, counit and triangle identities |
| Finite evaluations of F and G | `Realization.supportEvaluation`, `exceptionalEvaluation`, using recorded `FiniteExceptional.F` and `.G` |
| Every quotient map is canonical | `transition` uses the realization's `quotientRestrictionX/Y` proof fields and is the adjunct of the system's actual transition under the recorded scalar adjunction; `supportTransition` uses finite `.q`, `exceptionalTransition` uses its finite mate `.b` for every n ≤ m |
| Integral compact support equals L F R as a functor | `IntegralSupport.iso` on the existing integral constructible category, using `reducedConstructible` and the existing reduction functor |
| Specified finite integral projections | `IntegralSupport.projections`, an equality with the specified `sfCompactSupportFiniteReductionIso` and scalar-adjunction unit |
| Omega is E_a applied to the coefficient unit, using the same realization | `coefficientUnit` is the actual sequence ring module in degree zero; `DualizingOperation.realization` is a structure-map `Realization`; `.omega` is literally `.G.obj (normalizedUnit ...)` |
| Finite dualizing objects and canonical transitions | `DualizingSpec` identifies the actual evaluations with `integralDualizingFiniteTerm` and their transitions with the adjunct of `integralDualizingFiniteComparison` |
| D(M) = I(M,Omega), and dual stays in N | `dual`; `Duality.dualPreservesX`, `.dualPreservesY` |
| E_f is naturally D_X f* D_Y | `dualFormula`, `Duality.iso` of functors into the actual ordinary derived system category |
| Tensor-Hom transpose and pairing identity on systems | `Geometry.tensor_model`, `.tensor_unit`, normalized system signed symmetries, `Support.projection`, `structuralTrace`, and the explicit `Duality.pairing` equation before any evaluation |
| Same finite relative trace and dual formula | `Duality.finiteTrace` uses `DualizingOperation.finiteOmega`, defined through the exceptional evaluation and the section-normalized regular unit; `Duality.finiteFormula` equates each evaluated component of `iso` with `FiniteExceptional.dualFormulaIso` |
| Total limit Omega is prescribed dualizing construction, same projections | `DualizingSpec`: actual normalized tower, level/transition and coherent-tower comparisons, Roos derived-limit triangle, `IntegralDualizingLimitPresentation`, limit isomorphism, and the equation with every `coefficientSequenceProjection` |
| Natural enriched isomorphism in D(Tow Ab) | `Enriched.iso : mappingSource ≅ mappingTarget`, with codomain `DerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{u+1})` |
| Actual pre-limit map, not an evaluation-defined lift | `Realization.enrichedMap` is explicitly the projection/geometric-counit/evaluation/exceptional-counit transpose; `globalMap` applies derived sections to its inverse and the sections/direct-image comparison; `Enriched.component` fixes the natural transformation to that composite |
| Inverse and transpose identities | `Enriched.internalIsIso`, `Enriched.iso` with both inverse identities, and the closed-structure transpose used in `enrichedMap`; no inverse-limit functor appears in these definitions |
| Simultaneous resolution normalization | The proper image has the universal `CoefficientDerivedImage` certificate and its cochain transpose; tensor has `TensorComparisonModel` plus its ordinary unit equation; `SectionsPush.model` derives the unique sectionwise global-sections map using the actual derived units |
| Canonical finite enriched adjunction transported from etale | `Enriched.finiteIso` and `.finiteEvaluation` identify the finite values of this same evaluation/counit-transpose construction; `.finiteHom` also identifies its H⁰ action with the recorded etale-normalized `FiniteExceptional.adjunction`. The construction of the map is the internal derived transpose, independently of this H⁰ check |
| Same finite units and counits | `Realization.unit` and `.counit` are equations with the recorded finite adjunction, not existence of unrelated adjunctions |
| No integral exceptional functor or integral adjunction | None is defined or asserted. The integral data consist only of already defined compact support and the prescribed dualizing total-limit presentation |

Dependency declarations read and used (umbrella nodes retain their individual named interfaces):

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties`: umbrella reference; its recorded constituent Mathlib scheme morphism properties are used directly.
- `def-nagata-compactification`: `WeilConjectures.Compactification.Defs`, `AlgebraicGeometry.Compactification`.
- `lem-coef-derived-system-evaluation-calculus`: `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`.
- `def-coef-normalized-dvr-tower`: `Sheaf.Paper.NormalizedDVRTower`, `WeilConjectures.NormalizedDVRTower`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- `def-weil-pbc-constructible-complexes`: `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`, `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `lem-sf-proetale-constructible-origin`: `Sheaf.Paper.ProEtaleConstructibleOrigin`, `AlgebraicGeometry.ProEtale.constructible_proEtale_origin`.
- `def-weil-integral-rational-qbar-compact-support`: `Sheaf.Paper.QcqsCompactSupportRealization`, `WeilConjectures.sfQcqsCompactSupportRealization`.
- `def-weil-exceptional-inverse-image`: `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`, `WeilConjectures.ConstructibleExceptionalCoefficients.System`.
- `lem-coef-finite-exceptional`: `Sheaf.SixFunctors.FiniteExceptional`, `WeilConjectures.FiniteExceptional.finite_exceptional`.
- `prop-coef-integral-dualizing`: `Sheaf.SixFunctors.IntegralDualizing`, `WeilConjectures.prop_coef_integral_dualizing`.
- `prop-asd-internal-adjunction`: `WeilConjectures.SixFunctors.Etale.Derived.TensorHom`, `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIsoOfFinite`.
- `lem-sf-class-compact-support-comparison`: `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`, `AlgebraicGeometry.ProEtale.compactSupportSiteComparison`.
- `thm-weil-pbc-site-comparison`: `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`, `AlgebraicGeometry.ProEtale.isIso_compactSupportComparisonUnit`.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`, `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.

Additional implementation interfaces, already present in the library, are
`integralComparisonSequenceDirectImage`, `integralComparisonSequencePullback`,
`integralComparisonDerivedSequencePullback` and their compositor from
`Sheaf.Paper.IntegralComparisonSequenceSystems`; `SemilinearSections.TensorComparisonModel`
from `Sheaf.Paper.SemilinearSystemModels`; `SheafOfModules.CoefficientDerivedImage`
from `Sheaf.Paper.CoefficientSystemDerivedComparison`; the exact derived open
adjunction from `Sheaf.SixFunctors.OpenTensorNormalization`; and the representative
signed tensor coherence from `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`.
The local records assemble these existing interfaces for this node's maps; they
introduce no replacement coefficient category, internal Hom, scalar tensor, or finite
exceptional operation.

Searches actually performed:

- LeanFinder, “Functorial realization of finite exceptional inverse image on derived coefficient systems enriched adjunction”: eight general derived-adjunction hits, no coherent finite realization.
- Loogle, “CategoryTheory.Adjunction, CategoryTheory.NatIso”: no hit; the service reported the unrecognized `NatIso` identifier.
- Mathlib grep, “coefficient.*(Exceptional|Adjunction)|FiniteAdjunctionDiagram”: no match.
- LeanSearch, “Derived strict coefficient systems proper direct image open extension tensor projection counit transpose”: eight generic derived counit/module adjunction hits, no realization of this statement.
- LeanFinder, “Full category normalized derived coefficient systems whose each level is bounded constructible finite Tor without a uniform bound”: eight general derived t-structure/single-functor hits, no such domain or theorem.
- Repository rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id and coefficient exceptional/system adjunction and duality terms: existing finite exceptional, integral-exceptional, strict-system-adjoint and compactification-system interfaces, but no declaration containing this whole statement. Read their interfaces rather than substituting an integral exceptional assertion.
- DAG and blueprint search for “coefficient system projection”: no blueprint node under that search phrase. Existing proper/open system-calculus nodes were also inspected; they do not provide the normalized finite exceptional/enriched/dualizing realization asserted here.

Edge cases checked: the zero object and empty schemes are admitted; every index
is a positive coefficient exponent via n+1, including n=0; quotient identities
m=n and arbitrary composites n≤m≤r are included; no quotient-flatness assumption
is introduced; arbitrary independent cohomological and Tor intervals at different
levels are admitted; f need not be smooth, open, proper or of finite Tor dimension;
only the specified open/proper factors have those properties; ell=p is excluded
exactly as in the node. All universes are bound explicitly and retain site object
universe u+1 and site morphism universe u with coefficients in u (module values u+1).
No statement correction or disputed mathematical assertion was required.

Validation: every compile is through the prescribed `scompile.py`; final compilation
and delivery-preflight results are recorded below once completed.

## Second reading by NC

The dispatcher explicitly forbids starting another agent. This is an honest second
pass by the same worker, not a claim of an independent worker review; the delivery
is supplied for the maintainer's independent reading. The node, current blueprint
sources and module were reopened, and the hypothesis/clause table above was checked.
The second pass checked in particular that the full domain has no uniform bound,
that F/G and both enriched arrows are functorial system operations rather than
families of objects, that quotient transitions use `.q` and `.b`, that the duality
identity is an equality before evaluation, and that both total-limit clauses retain
the specified projections. It also separated finite enriched map construction from
its additional H⁰-adjunction check, and bound the finite mapping codomain universes
explicitly after an elaboration failure. The structure-map over-base instance is
the identity-law instance, with no added hypothesis. Every remaining theorem proof is
`sorry` with a named declaration and a natural-language proof in its docstring.
The returned definition-module helper sorries have been removed as detailed below.

## New nodes

`def-coef-finite-adjunction-system-data` defines the full normalized per-level finite-Tor
category and the data of an actual finite-operation realization, including its quotient
squares, adjunction and actual enriched projection/evaluation/counit arrow. It asserts
no existence of these data and no invertibility of the enriched arrow; those remain
in the item's theorem. Its module is `Sheaf.SixFunctors.FiniteAdjunctionSystemData`.
The current blueprint finite-exceptional proof defines the finite functors, their
coefficient mates and the enriched adjunction; this node gives the strict-system
realization-data interface needed by the item's coherent refinement. The existing
ambient system adjoint interfaces use different coordinate categories or domains,
and the existing proper/open calculus does not define this normalized finite-Tor
adjoint-pair datum. Searches before introducing it: LeanSearch and LeanFinder with
“Normalized strict coefficient systems finite Tor constructible at each level and
functorial finite compact support exceptional realization data” returned respectively
Dold-Kan/general sheaf and t-structure/support results; Mathlib grep
`Normalized.*Coefficient|Finite.*Exceptional|Strict.*System` returned eight unrelated
text hits. Repository rg in DAG nodes, WeilConjectures and Sheaf and blueprint_refs
search “finite adjunction system” found no such definition. The module's helper
records use the existing universal derived-image and K-flat model definitions.
The definition and all its hypotheses and clause correspondences were included in
the second reading. The new definition node owns the realization-data module; the original statement node owns the existence and compatibility theorem. No existence assertion or clause is dropped.

Validation update: the prescribed scompile.py compiled BOTH delivered files cleanly, including their private dependency order: FiniteAdjunctionSystemData 38.4 s, FiniteAdjunctionDiagramRealization 38.0 s. Only the expected sorry warnings are present. Temporary #check/prefix diagnostic files were removed.

Final reading: expanded the local `let` in `Duality.pairing` so the system pairing statement remains directly usable by downstream proofs. Added the stated proof-dependency modules as non-public imports, as required by stages/2-statements.md §3.7. The initial complete dry run passed preflight and compilation (024a069bab); validation is repeated after these final edits.

Final preflight follows the route-pivot gate: the proof-only import `Sheaf.Paper.EtaleCoefficientSystemAdjoint` is omitted because the current gate identifies its strict-interface node as dropped. No declaration in this delivery uses that import; the ordinary system construction remains in the stated conclusion. Both modules compiled cleanly through scompile.py after the pairing expansion (26.3 s and 18.2 s).


## Repair of H3 return at a7fdec736324

The saved packet's initial prescribed dry run passed at 50121fb195; that was a
baseline check, not a repair or a delivery. The packet was then substantively
changed to address both numbered points. No live source or launcher script was
edited, and the two delivered modules are still owned by the same two DAG nodes.

1. `Duality.finiteFormula` now explicitly identifies evaluation of `iso.hom.app N`
   with `FiniteExceptional.dualFormulaIso.hom.app (evaluation N)`. Its intervening
   maps are the recorded `SX.fiberHom`, `SY.fiberHom`, the canonical geometric
   inverse-image evaluation, and `DualizingOperation.finiteOmega`. The latter is
   now a definition, not a free field: evaluate the same structural exceptional
   operation and apply it to the exact localization of the regular-module unit
   comparison. `DualizingOperation.unitEvaluation_sections` fixes that ordinary
   unit comparison on every section. `pullDualNormalized` supplies normalization
   of the actual pullback of the system dual, with no cohomological/Tor bound.
   `finiteTrace` uses these defined omega comparisons. The simultaneous sign
   change of compactComposition, iso and finiteOmegaX from the return is therefore
   unavailable: finiteOmegaX is no longer free, and changing iso alone changes
   the explicit equation with the unique FormulaNormalized finite comparison.

2. `Realization.supportEvaluation_canonical` fixes supportEvaluation to evaluation
   of supportIso followed by `Support.evaluation`. That definition composes the
   actual proper/open comparisons and the published `DirectEvaluation` and
   `OpenEvaluation` of `Sheaf.SixFunctors.IntegralSystemOperations`. For each
   Geometry, `ordinaryDirect_sections` makes the transport to the published
   sequence direct image the identity on every section. `Geometry.pullTransport`
   is left-adjoint uniqueness for that fixed ordinary comparison, localized
   exactly, and `Geometry.pullEvaluation` composes it with the recorded
   cochain-normalized `pullbackTensorDerivedEvaluation`. The proper comparison
   is right-adjoint uniqueness with that fixed pullback transport; the open
   comparison is left-adjoint uniqueness. Their unit/counit normalizations rule
   out inserting a scalar into the composite. Hence the twist (u,u^-1) in the
   return fails supportEvaluation_canonical for nonidentity u; exceptional
   evaluation is then fixed by the existing finite counit equation. The same
   normalization applies to both structural realizations used for omega.

Advisory helper audit: there are now **zero sorries in the definition module**.
`direct_additive` was removed; the instance is obtained from the existing ordinary
adjunction's `right_adjoint_additive`. `restriction_sections` was removed;
`restrictionSections` transports the object equality of the recorded
`coefficientSequenceRestriction_exists` to the underlying sections with
`congrArg`. `Support.openTensor_isIso` was removed; invertibility of that exact
open-unit transpose is a proof field of Support. `quotient_restriction` was
removed; `QuotientRestriction` states that equality as proof data, and Realization
contains the X/Y fields used by its actual transitions. The new definition node
explicitly records both requirements. Their existence remains part of the
original item's theorem, whose proof docstring gives the open-slice/zero-on-the-
complement and canonical-quotient arguments. No helper theorem without a DAG
statement remains in the definition module.

Additional dependency declarations read and used:
`WeilConjectures.IntegralSystemRealization.Direct`, `DirectEvaluation`, `Open`,
`OpenEvaluation`, `Direct.adj`, `Open.adj` in
`Sheaf.SixFunctors.IntegralSystemOperations`, and the section-normalized sequence
adjunction and cochain-normalized `pullbackTensorDerivedEvaluation` in
`Sheaf.Paper.CompletedPullbackTensorComparison`. Their existing definition nodes
are cited by the new data node; no duplicate of those notions was introduced.

## Second reading by NC (repair)

A second pass by this same worker reopened the returned head's saved sources,
the current finite-exceptional module (including FormulaNormalized,
dualFormula_existsUnique and dualFormulaIso), the actual regular-unit definition
in FiniteDualizing, the published proper/open system evaluation records and their
inverse-image evaluation normalization, and the main-20261015 finite-exceptional
statement and proof. The earlier correspondence table still covers the same
hypotheses and domain, including empty schemes, zero objects, positive indices,
identity quotient maps and arbitrary quotient composites without any uniform
level bound. The two missing canonical-map clauses are now explicit, as above.
The inverse-image transport uses adjunction uniqueness with the sectionwise
identity, rather than an unspecified isomorphism. The dual-formula equality uses
those same canonical transports, with the first Hom variable contravariant and
the second covariant. It therefore has precisely the direction of
FiniteExceptional.dualFormulaIso. All added fields are conclusion data or their
normalizations, not extra hypotheses on f or input systems. This is an honest
second reading by the author; independent review remains the maintainer's.
