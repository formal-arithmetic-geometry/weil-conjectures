## Worker report

Group Q69; item `lem-coef-dual-formula-scalar-transpose`; stage 2, 2026-10-18.

The module `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` states
`WeilConjectures.CoefDualFormulaScalarTranspose.coef_dual_formula_scalar_transpose`.
Every theorem has `sorry` as its proof and a source and natural-language proof plan.
Every definition has real data. The formula isomorphisms are selected by a unique
explicit evaluation characterization, not by choosing an unspecified isomorphism.
The eight postponed theorems are supporting clauses of this node's construction
and final identity; all 27 declarations are recorded in `lean.declarations`.

### Hypotheses and clauses

* The global algebraic-closure finite-field datum is `D : FiniteFieldDatum.{u}`.
  Its prime characteristic is `D.p`. The coefficient assumptions are
  `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`, fields `E`, `L`, their
  `Algebra (Padic l)` and `FiniteDimensional (Padic l)` instances, and
  `i : E →ₐ[Padic l] L`. A homomorphism of fields is injective, so this is the
  specified finite coefficient-field inclusion. Integer rings, powers of their
  maximal ideals, quotient maps and ramification are the existing Padic constructions;
  no replacement ring, chosen basis or extra flatness assumption is introduced.
* The schemes `X`, `Y` have `Over (Spec (.of D.k))` structures. Their structure
  morphisms have `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` instances.
  The map `f` has `IsOver`, `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`.
  Thus the hypotheses say exactly separated finite type over k. The fixed
  compactification is `c : Compactification f`.
* The actual small pro-etale completed-coefficient categories are
  `sfIntegralConstructibleCategory l E W` and the analogous L categories.
  Their ambient categories and completed rings are the imported
  `IntegralVerdier.Ambient`, `scalarReductionSource`, and
  `completedIntegralCommRingSheafUnrestricted`. Site and coefficient sizes are
  unchanged; `u` is explicitly bound, and independent coefficient/site APIs are
  instantiated explicitly at `{u,u}` where required.
* The completed strict-tower scalar functors are the imported
  `integralScalarExtension l E L i W`. Their constructible restrictions are
  `sfConstructibleIntegralScalarExtension D.p l hl E L i W`. The latter have
  literally the former ambient objects and maps, with only membership proofs added.
* `GE`, `GS`, `adjE`, `adjL` are the specified constructible right adjoints with
  their full adjunction structures. The left functors are the actual
  `sfCompactSupportFiniteIntegralFunctor` for c, not abstract functor parameters.
  In particular the conclusion uses `adjE.counit` and `adjL.counit`. It does not
  posit or assume any compatibility square for the sought comparison. Quantifying
  over presentations of the given right adjoint is legitimate: the unique
  unit/counit-preserving isomorphism of right adjoints identifies every such
  presentation with the source's reduction/limit realization. Our formula
  normalization uses that very supplied adjunction, so it also fixes this transport.
* `wEX`, `wEY`, `wLX`, `wLY` are the existing
  `IntegralFiniteExtension.DualizingDatum`: the integral dualizing objects with
  their specified finite reduction isomorphisms and quotient coherence. Each
  `aEX`, `aEZ`, `aEY`, `aLX`, `aLZ`, `aLY` is the existing normalized
  `IntegralHom.TensorPresentation`, not an arbitrary tensor bifunctor.
  `sEX`, `sLX` are its `IntegralVerdier.SignedSymmetry` presentations.
  These parameters expose the evaluations already fixed in the statement.
* `finiteSupportComposition` is the published proper/open compositor, with the
  supplied compactifications compared canonically with the default ones.
  `finiteEtaleTrace` transposes its composite with the absolute structural counit
  under the actual absolute adjunction. `finiteSupportOrigin` and `finiteTrace`
  transport that map through the published comparison-site and intrinsic
  coefficient isomorphisms. `TraceNormalized` gives the exact reduction equation
  against `sfCompactSupportFiniteReductionIso` and the recorded dualizing reductions.
  `trace` is chosen from `trace_existsUnique`, which fixes the map itself.
  Its uniqueness proof plan uses the special dualizing self-Hom computation; it
  explicitly does not claim general faithfulness of individual finite reductions.
* `ordinaryPush_eq`, `ordinaryPullIso`, `ordinaryPullComplexMap`,
  `pullCompletion_existsUnique`, and `pullCompletion` give the needed canonical
  transport from the projection-formula ordinary pullback to completed pullback.
  The normalization is the actual `ordinaryIntegralCompletionChain` (quotient
  augmentation, zero shifted coordinate) on every good K-flat representative.
  The map is uniquely specified before passing to individual finite evaluations.
* `formulaObject` is exactly `D_X (f_comp^* (D_Y M))`, using the imported ordinary
  internal Hom into the given dualizing object and the imported completed pullback.
  `FormulaNormalized` identifies its comparison with the supplied exceptional
  adjoint by evaluation: apply the actual `PurCompactSupport.projectionMap`, the
  normalized completion map, the specified signed swap and tensor-Hom evaluation,
  then the structural relative trace. The other side is evaluation after the
  supplied exceptional counit. The actual `sfQcqsCompactSupportRealization` occurs
  in both sides. `formula_existsUnique` and `formulaIso` therefore select precisely
  the canonical kappa of the source Hom-bijection, including its counit normalization.
  This supplies the extra normalization needed here beyond the bare existential
  formula isomorphism in the upstream integral-adjoint theorem; that existential
  isomorphism is never chosen as a definition of kappa.
* `dualValue` extracts the constructibility proof from `integral_verdier_biduality`;
  its object is literally the specified integral dual. `pullDualValue` is the
  actual `constructibleIntegralPullback` of that dual. The two inline residue-field inverse terms transport `finiteFieldDatumPrimeUnit`
  through the structural residue-field algebra maps. They need no rational Verdier
  dependency. No rational object or rationalization assumption occurs here.
* `betaIso` has exactly the morphism
  `IntegralFiniteExtension.beta` as its hom. `beta_isIso` records the imported
  finite-extension clause for arbitrary normalized tensor presentations. Thus the
  dualizing comparison inside beta is the imported `IntegralFiniteExtension.u`,
  defined by the scalar-extended absolute structural counit and the prescribed
  finite comparison maps. Neither beta nor u is an arbitrary isomorphism.
* `supportScalar` is the proper/open canonical scalar mate
  `PurCompactSupport.comparison (completedChange ...) c`, conjugated by the actual
  `IntegralFiniteExtension.completion` maps and by the recorded compact-support
  realization. Its direction is `T_Y F_E → F_L T_X`. `supportScalar_isIso` is the
  finite-free-distributivity clause defining alpha in the node, and
  `supportScalarIso` has exactly that canonical map as its hom.
* `dualFormulaScalar` is d_M. It is beta_X at `f_E^* D_Y,E M`, followed by
  `D_X,L.map` of the opposite of
  `f_L^*(beta_Y inverse) ≫ (scalarPullbackCompleted ...).inv`.
  Lean composition runs left to right; this is exactly the node's
  `D_X,S(c inverse composed with f_S^*(beta_Y inverse)) composed with beta_X`.
  `scalarPullbackCompleted` is the published normalized tensor reassociation.
* `exceptionalScalar` is b-prime: `T_X.map kappa_E.hom`, followed by d_M,
  followed by `kappa_L.inv`. Both kappa components are `formulaIso` above.
* The final equality is precisely the counit equation, written in the faithful
  ambient category. Its left side is `F_L.map exceptionalScalar`, the canonical
  support realization at `GS(T_Y M)`, and `adjL.counit` in that order. Its right
  side is `supportScalarIso.inv` followed by `T_Y.map adjE.counit`.
  The ambient source is `image_L(T_X GE M)` and target is `T_Y M`.
  Transporting the source by the canonical support realization and using naturality
  removes the displayed realization at `GS(T_Y M)` and gives exactly
  `epsilon_S ∘ F_S(b-prime) = T_Y(epsilon_R) ∘ alpha inverse`.
  Full faithfulness of the constructible inclusion makes this equivalent to the
  equation in the original constructible category, with no weakened conclusion.

### Dependency declarations

Used recorded declarations and their owning modules (with auxiliary declarations
from those same modules where noted):

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: finite coefficient rings
  and `Padic.finite_coefficientExtensionRing`; the coefficient-field structures and
  quotient homomorphisms are those already imported by the recorded dependencies.
* Mathlib scheme/site leaves: `Scheme`, `Scheme.ProEt`, `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`, `Compactification`, `CategoryTheory.comp_over`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: existing completed
  coefficient conventions, without identifying the completed ring with a discrete
  constant integral ring.
* `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`.
* `Sheaf.Paper.IntegralScalarExtensionUniverses`: the recorded completed
  `integralScalarExtensionOfUniverses` (and the definitionally equal standard-size
  `integralScalarExtension` used by the constructible scalar functor).
* `Sheaf.Paper.QcqsCompactSupportRealization`:
  `sfQcqsCompactSupportRealization` and its actual projection normalization;
  `sfCompactSupportFiniteIntegralFunctor` and `sfCompactSupportFiniteReductionIso`
  come from its recorded compact-support imports.
* `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `finiteFreeCompletedScalarComparison`, for the proof of the finite-free alpha clause.
* `Sheaf.SixFunctors.IntegralVerdier`:
  `IntegralVerdier.dual`, `IntegralVerdier.SignedSymmetry`,
  `integral_verdier_biduality` and its preservation clause.
* `Sheaf.SixFunctors.CoefIntegralFiniteExtension`:
  `IntegralFiniteExtension.DualizingDatum`, `tensorModel`, `completion`, `beta`,
  `coef_integral_finite_extension`; the finite dualizing declarations, their
  specified structural adjunctions and `finiteDualizingOrigin` are its dependencies.
* `Sheaf.Paper.IntegralOperationsScalarComparisons`:
  `scalarPullbackCompleted` and the actual chain/strict-tower completion comparisons.
* `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback` and the
  recorded underlying integral tensor-Hom/pullback conventions.
* `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients`:
  `AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint` is the
  recorded proof-route theorem. Its bare existential formula comparison is not
  substituted for an evaluation-defined comparison. The current live source was
  read with `scompile.py --source` as well as the local source.
* `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the published
  coherent constructible-adjunction/coefficient-system interface used by the proof route.

The two construction-only theorem dependencies flagged at immutable head
`810a9f9ed786` are replaced in `stmt_deps` by definition nodes:

* `def-sf-etale-support-compositor` owns
  `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`,
  `AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso`.
* `def-sf-compact-support-site-comparison-construction` owns
  `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`,
  `AlgebraicGeometry.ProEtale.compactSupportSiteComparison` and its Plus variant.

These are `existing: true` bindings of published definitions. Their new-node
statement dependencies are definitions only; the coherence and comparison theorem
nodes are not prerequisites for introducing this item's statement. The earlier
`def-sf-intrinsic-compact-support-realization` and
`def-sf-ordinary-integral-pullback-construction` bindings are retained. The item also
continues to omit `cor-exc-base-change-open-immersion-general`,
`lem-tw-ordinary-completed-integral-pullback`, and `thm-coef-rational-verdier`
from its statement dependencies. No Lean file is changed for this repair.

The original proof-dependency modules with recorded declarations are imported as
proof imports. In particular the proof plan retains absolute trace exchange,
coherent coefficient-system evaluation, signed tensor-Hom calculus, and the
strict-tower homotopy-limit construction. No downstream rational-operations theorem
is imported or used to assert this integral scalar-transpose identity.

### Edge cases and semantic checks

* Identity coefficient extension E=L and identity i: the definitions still use
  the specified scalar multiplication unit and its canonical inverse; no inequality
  of fields or ramification index assumption excludes this case.
* Arbitrary finite ramification: the maps use the existing quotient ideals and
  canonical coefficient inclusions. The proof uses S/pi^n S at the finite-free
  stage and the cofinal v-adic subsequence en; no equality of uniformizers or
  unramified hypothesis appears in Lean.
* Identity f, open f, and proper f: the same chosen compactification, source
  adjunction, projection and structural counit normalizations are used.
* Empty X or Y when a morphism exists, and the zero input M: no nonemptiness,
  nonzero cohomology or positive dimension is imposed.
* Finite indexing uses n : natural as exponent n+1. This covers all nonzero
  coefficient levels; the exponent-zero quotient is the zero ring and contributes
  the trivial reduction equation. There is no finite n in the integral conclusion.
* All universes and variables are bound; auto-implicit is disabled. The K-flat completion
  characterization supplies `HasDerivedCategory.standard` explicitly on its quotient
  functors, with unchanged site/coefficient sizes and instance registrations.
* Replacing a kappa by an unrelated rescaled isomorphism fails FormulaNormalized.
  Replacing beta or alpha is impossible: their hom fields are actual published
  constructions. Thus the theorem has no arbitrary-comparison hypothesis and
  does not assume the desired counit square.
* Individual reductions are not asserted faithful on arbitrary derived morphisms.
  The final proof explicitly transports one coherent mapping-system identity.

### Searches

* `msearch.py Q69 lem-coef-dual-formula-scalar-transpose leanfinder
  "The scalar comparison for the Verdier duality formula for exceptional inverse
  image transposes to compact support scalar comparison"`: generic internal-Hom,
  condensed-category and Ext hits; no statement of this normalized integral identity.
* `msearch.py ... loogle "CategoryTheory.mateEquiv, CategoryTheory.Adjunction.counit"`:
  the generic mate/counit and inverse-mate equations, not the canonical Verdier
  formula identification or its scalar-transpose theorem.
* `msearch.py ... grep "dual.*formula|formula.*dual|scalar.*transpose"`:
  unrelated Mathlib monotone-convergence/matroid hits, no six-functor theorem.
* `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for dual-formula,
  exceptional-adjoint, trace, projection, and scalar-transpose names, and the exact
  item-id search: no existing exact theorem. The upstream integral theorem has
  the existential formula comparison, rather than the evaluation normalization.
* `rg` in `/home/ubuntu/weil-newtargets-shared/lean/Sheaf` found the source
  Step-15 discussion in `RationalOperations`, which is a downstream rational
  statement and not this integral theorem. It is not imported. The searches did
  find the canonical comparison-site, finite dualizing, ordinary-completed pullback,
  proper/open scalar and tensor-Hom constructions reused above.
* Source inspection included every original statement dependency's recorded
  declaration or Mathlib match, the four construction definition bindings and signatures/docstrings
  of their maps, and the current blueprint unit. There is no exact existing match.

No statement correction or mathematical dispute is claimed. The main node changes only
in `lean` and `stmt_deps`; its mathematical statement, proof and proof dependencies
match the current published base verbatim. The four new definition nodes register
published construction data that previously lacked dedicated definition ownership.

## New nodes

`def-sf-intrinsic-compact-support-realization` binds
`AlgebraicGeometry.ProEtale.sfIntrinsicCompactSupportComparison` in the existing module
`Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange`, together with
`sfIntrinsicOpenExtensionComparison`. It defines the composite of the unit-cancellation
open-extension comparison, the published derived direct-image comparison, and associators.
Its source is the parent's blueprint paragraph 8 / Step 15, where canonical comparison-site
realization is used in the evaluation normalization. The recorded signature is verbatim
from the published definition, including finite commutative A, arbitrary X,Y,f and the
fixed compactification c. The two sides are exactly E_X followed by intrinsic support,
and fixed-scalar support followed by E_Y. The old exceptional open-base-change theorem
is not needed to introduce this composite. All construction data already exist, so
`existing: true` uses that module directly and avoids a duplicate definition.

`def-sf-ordinary-integral-pullback-construction` binds
`WeilConjectures.ordinaryIntegralCompletionChain` in the existing module
`Sheaf.Paper.OrdinaryCompletedIntegralPullback`. Its declaration list records the
completed direct ring map, its uniqueness clause, module push/pull functors, adjunction,
additivity and termwise complex functor, quotient augmentation and its uniqueness clause,
product augmentation, chain condition and actual chain map. Its source is the same
blueprint paragraph 8 / Step 15, whose ordinary-to-completed comparison requires this
specific quotient-and-zero normalization; the published source additionally identifies
Bhatt--Scholze 6.5.9 and Stacks 06YY/08TC. The ring map clause is
`ordinaryIntegralFiniteDirectRingMap` / `ordinaryIntegralDirectRingMap`; sectionwise push
is `ordinaryIntegralModulePush`; the sheafified module left adjoint and its actual
adjunction are `ordinaryIntegralModulePull` / `ordinaryIntegralModuleAdjunction`.
`ordinaryIntegralModulePull_additive` supplies the additive lift used by
`ordinaryIntegralPullComplex`. The generator formula is exactly
`ordinaryIntegralQuotientAugmentation_existsUnique`; its product is
`ordinaryIntegralProductAugmentation`, and the (quotients, zero) mapping-cocone lift is
`ordinaryIntegralCompletionChain`, justified by the recorded chain condition. This
node defines construction data for arbitrary schemes; it does not restate the theorem
that ordinary pullback preserves constructibility or that completion is invertible.
Its primary Lean signature is copied verbatim from that chain-map definition.

Searches for both nodes: `msearch.py leansearch` with the ordinary pullback / intrinsic
support transport query returned generic sheaf module pullbacks and adjunctions;
`msearch.py loogle` for `SheafOfModules.pushforward, CategoryTheory.Functor.isoWhiskerRight`
returned generic pushforward/pullback composition identities; `msearch.py grep` for
`ordinaryIntegralModulePush|sfIntrinsicCompactSupportComparison|ordinaryIntegralCompletionChain`
returned zero Mathlib hits. The complete tool outputs are retained in each new node's
`mathlib_searches`. Direct `rg -l` over the DAG, upstream source and side source found
these exact construction declarations in the two published theorem modules, and no
dedicated definition node for either construction. `blueprint_refs.py search` returned
zero blueprint nodes for both `ordinary completed pullback` and `intrinsic compact support`.
Related nodes `def-weil-compact-support-candidate` and
`def-pur-integral-derived-operations` define endpoint functors, not these normalized
realization/augmentation maps; `def-pur-compact-support-transport` is Frobenius transport
and is a different construction. The new nodes cite the already existing definitions
of all their ingredients and introduce no new Lean construction or postponed theorem.

`def-sf-etale-support-compositor` binds the exact existing
`AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso` definition in
`Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`. Its source is
Stacks 0F7J and 0F7B(b), read in `literature/stacks-project/more-etale.tex`.
The node permits exactly the definition's finite commutative A, schemes X,Y,Z,
maps f,g, selected compactifications for f,g and their composite, and the two
quasi-compactness instances. Its definition is the inverse input compactification
comparison, proper/open tower compositor, and output compactification comparison.
It asserts no associativity or unit equation. Definition-only dependencies supply
scheme morphisms, compactifiability, compactifications, derived categories and
etale compact support. The owning module's coherence theorems are unnecessary to
state this composite. The existing definition's signature is copied verbatim from
`def` to before `:=`; no Lean declaration is copied or added.

`def-sf-compact-support-site-comparison-construction` binds the exact existing
`AlgebraicGeometry.ProEtale.compactSupportSiteComparison` and
`compactSupportSiteComparisonPlus` in
`Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`. Its source is
Stacks 09AF and 099R, read in `literature/stacks-project/proetale.tex`.
The node has precisely finite commutative A, arbitrary X,Y,f and compactification c.
The Plus comparison is reassociation, the actual proper direct-image counit mate,
the canonical open-extension comparison, and reassociation. The ambient comparison
is its inverse transported through the canonical bounded-below inclusions.
All endpoint categories are ordinary fixed-A module-sheaf categories, and the
comparison direction on the ambient categories is pro-etale support to comparison
pullback of etale support. Definition-only dependencies introduce sites, module
derived categories, comparison pullback, compactification, extension by zero,
ordinary direct image and mates. Isomorphism data reuse the existing published
construction; the theorem of the old node is not asserted as a hypothesis.
The primary signature is verbatim from the ambient definition.

Searches for these two additional nodes were rerun with `msearch.py`:
LeanSearch query `canonical proper open compact support composition and etale
proetale comparison natural isomorphism` returned eight generic topology/scheme
composition hits; Loogle query
`CategoryTheory.Functor.isoWhiskerRight, CategoryTheory.Functor.associator`
returned twelve generic functor coherence identities; Mathlib grep for
`unboundedEtaleLowerShriekCompIso|compactSupportSiteComparison` returned zero hits.
The new nodes store those complete actual outputs. The corresponding upstream
source grep returned no hits. The Sheaf grep found the two published definitions
and their consumers; DAG grep found theorem users and definitions of other
constructions. `def-pur-finite-exceptional-composition` is the right-adjoint
conjugate, and `def-sf-refinement-comparison-isomorphism` compares two
compactifications at an etale-origin witness; neither owns either new definition.
A scan of every definition node found no exact construction owner.
`blueprint_refs.py search` returned zero nodes for each of
`compact support composition` and `compact support site comparison`.

## Second reading by Q69

Repair self-check for the return at immutable head `810a9f9ed786`, with the
saved packet, current main node and the complete definition signatures/bodies
open. This is a same-worker self-check, as the dispatcher forbids other agents;
the maintainer supplies the independent review. The return accepted all 27 Lean
declarations, hypotheses, canonical maps and final signature, so they are retained
byte for byte. The earlier self-check's claim that the two theorem nodes were
needed as statement dependencies was incorrect; this repair removes that claim
and replaces both nodes by the construction definition nodes above.

H2: compared the saved item's node with the current read-only main node. The only
changed fields are `lean` and `stmt_deps`. In particular, the natural-language
statement, proof and proof dependencies are unchanged. Both flagged theorem ids
are absent from the final `stmt_deps`. Four added construction nodes are cited.
The replacements introduce construction ownership rather than a new hypothesis
or a new mathematical conclusion; no statement_change is needed.

H12: each new node has exactly the prescribed definition fields, empty proof
fields, complete actual search outputs, source, correct item/ancestor/via, chapter
and unit, and `existing: true` binding. The two added definitions are absent from
the current DAG as independent definition notions. Their immediate statement
dependencies are all definition nodes. The primary Lean signatures are copied
from the respective existing definitions; the site-comparison record lists both
Plus and ambient definitions. No additional module or postponed theorem is added.

The compositor's three factors in its body match the new node clause by clause:
`rightDerivedLowerShriekIso` inverse for the restricted `ofComp` compactification,
`rightDerivedLowerShriekOfCompactificationCompIso` for the tower, then
`rightDerivedLowerShriekIso` for the composite compactification. The site
comparison body matches `fixedComparisonDirectImageMatePlus` and
`properOpenSiteExtensionIso` in the stated order; its ambient definition uses
the inverse Plus comparison and canonical inclusion compatibility isomorphisms.
This accounts for the sole additional construction uses at lines 71 and 132 of
the retained item module without theorem-node statement dependencies.

The full original clause correspondence in Worker report still applies:
finite-field datum, prime inequality, E-to-L inclusion, separated finite-type
X,Y,f, compactification, four dualizing data, six tensor presentations, two signed
symmetries, two actual adjunctions and arbitrary M. Kappa is evaluation-normalized,
beta and alpha have their actual canonical homs, d_M and b-prime have the specified
order, and the conclusion is the exact counit identity. Identity E=L, ramified
coefficients, empty schemes and zero M are retained. The new definition bindings
also permit the finite zero ring; they add no invertibility or nonemptiness
hypothesis. `lean.statement` still equals the full final theorem signature.

### Validation

The required saved-packet initial dry run passed at temporary commit `4b0596264e`
with `OK (dry run)`. That mechanical pass did not resolve the independent ownership
return, so this repair explicitly replaces the two flagged dependencies. It retains the saved Lean file and repairs only definition ownership and the report.
All verification uses the prescribed scompile.py/deliver2.py wrappers, their
unchanged 60-second per-file limit and normal refresh/rebase bookkeeping. No direct
Git command, live-library write, global build, launcher-tool edit or extra agent
is used. The retained main module passed the prescribed `scompile.py` check (exit 0),
with no errors or unexpected warnings in either sandbox or library compilation.
The wrapper printed elapsed values 60.9 s and 94.3 s; no timeout setting was
changed. These are recorded as printed, without claiming they are compiler CPU
timings. The repaired packet also goes through the normal delivery dry run.

The repaired `deliver2.py --no-push` passed at temporary commit `790b4c70c9`: 
`OK (dry run)`, including server preflight, the main module and all four
existing-declaration definition bindings. The wrapper staged the main module,
the item node, four definition node records and this report. No compile error,
unexpected warning or timeout was reported. The final push uses the same
prescribed wrapper and repeats its normal gates.

## Timeout-return recheck, 2026-10-18

The return at immutable head `43c8fcc9f615` reports a 60-second timeout in
`Sheaf/Stage2/Sandbox0.lean`. Following the dispatcher's saved-packet instruction,
I first read this report and ran the unchanged saved packet through
`deliver2.py Q69 lem-coef-dual-formula-scalar-transpose --no-push`. It passed:
`OK (dry run): commit c887b86109 passes the preflight and compiles; nothing pushed`.
The wrapper completed the preliminary main-module and existing-declaration checks,
the sandbox main-module check (including the previously failing Sandbox0), the
library-path main-module check, both existing-declaration probe checks, and server
preflight. No compile error, timeout or unexpected warning was reported. This is
a successful recheck; it does not establish a source-level cause for the earlier
timeout. The default 60-second limit and launcher scripts were unchanged.

I retained the saved Lean source and node records as explicitly instructed when
the initial dry run passes. The additional same-worker self-check opened the full
module, the item's statement and proof, the current shared node, the four new
definition bindings and their published construction bodies, and the source
blueprint's finite-scalar-extension paragraph. The item differs from the current
shared base only in `lean` and `stmt_deps`; all four construction nodes are still
new bindings to existing declarations. No mathematical statement change is made.
The final theorem signature matches `lean.statement` verbatim, all 27 declarations
are listed, every theorem proof remains `sorry`, every universe/variable is bound,
auto-implicit is disabled, and every Lean line is at most 100 characters.

The clause correspondence above was checked again: the coefficient inclusion and
prime inequality, separated finite-type schemes and morphism, fixed compactification,
four normalized dualizing data, tensor presentations, signed symmetries, actual
constructible adjunctions and arbitrary input M remain present. The canonical
evaluation normalization fixes kappa, beta has its published evaluation-defined
hom, alpha is the specified proper/open comparison, d_M has the contravariant
order in the node, and b-prime conjugates it by those kappa components. The final
identity is the requested counit equation after the faithful ambient inclusion
and canonical support realization. Identity coefficient extension, arbitrary
ramification, empty schemes and the zero input remain included. No mismatch was
found and no Lean change was needed. The final delivery wrapper repeats its normal
compile and preflight gates before pushing this packet with the updated report.
