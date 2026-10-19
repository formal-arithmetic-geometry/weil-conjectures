## Worker report

The module `Sheaf.Paper.FiniteFreeCompletedScalarComparison` states the complete finite-free comparison. Every theorem proof is `sorry`; definitions have actual data. The auxiliary maps are characterized uniquely, including both components of the strict product cone. In particular, the comparison is a natural transformation on the ambient derived categories, with invertible components asserted only on derived-complete inputs.

Hypothesis and clause correspondence:

| Node text | Lean |
| --- | --- |
| Prime ℓ | `l : ℕ`, `[Fact l.Prime]`. |
| Finite extensions E and L of ℚℓ, with E included in L | `E L : Type u`, field, ℚℓ-algebra and finite-dimensional instances, and `ι : E →ₐ[ℚ_[l]] L`. A field algebra homomorphism is injective. No independent assumption of finite degree over E is needed. |
| Valuation rings, uniformizers and finite quotients | The existing `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and `coefficientExtensionRing`, through the coefficient and strict-tower imports. |
| Any scheme Y and its small pro-etale site | `Y : AlgebraicGeometry.Scheme.{t}` and `Scheme.ProEt.topology Y`. The independent universes remain object universe `t+1`, morphism universe `t`, and coefficient/module universe `max u (t+1)`. |
| Completed sheaves R and S are inverse limits of the finite constant sheaves | `completedIntegralCommRingSheafUnrestricted l E Y` and the same for L; their underlying ring sheaves are the recorded `completedIntegralCoefficientSheafUnrestricted`. No discrete constant integer sheaf is substituted. |
| Canonical map R → S | `completedCoefficientMap_existsUnique` requires its composite with every target projection to equal the source projection followed by `integralScalarQuotientSheafMap`; `completedCoefficientMap` selects this unique map. |
| S finite free of rank [L:E] as an R-module sheaf | First conjunct of `finiteFreeCompletedScalarComparison`: the restricted regular S-module is isomorphic to the product of `Fin (completedScalarRelativeDegree l E L ι)` copies of the regular R-module. This finite product is also the finite direct sum. The degree is `Module.finrank E L` with the E-algebra structure induced by ι. |
| D(R), D(S), ordinary derived tensor | `DerivedCategory (integralTowerModules l E Y)` and L respectively. `completedScalarChangeData` uses the recorded universal derived-change-of-rings theorem; `completedDerivedScalarExtension` selects its left derived functor and retains its canonical counit in `completedScalarCounit`. Ordinary extension is the witness's sheafified tensor on objects and maps. |
| Derived t-complete input K | The second conjunct quantifies every K and assumes `IsDerivedCompleteUnrestricted l E Y K`, reusing the recorded Roos completeness predicate without imposing a geometric finite-field hypothesis. |
| Positive quotient indices m≥1 | Every Lean level `n : ℕ` means exponent `n+1`, as in all the dependency constructions. No zero-exponent quotient enters the tower. |
| Reductions S → (O_L/v^m)_Y and restriction to S-modules | `integralScalarTowerFunctor`, `integralScalarLevel` and `integralOperationsRestrict` are the existing strict reductions with the target completed action. The projection in the chain-comparison formula is `completedIntegralCommRingProjectionUnrestricted l L Y n`. |
| Strict Rlim is Cone(1-s)[-1] | `integralScalarComplexFunctor` uses the recorded `integralOperationsRoos` = `CochainComplex.mappingCocone` of `completedScalarRoosEndomorphism`. The latter uses exactly the recorded transition maps. |
| Compatible quotient maps P⊗R S → Res(P⊗R A_L,m) | First clause of `completedScalarChainComparison_existsUnique`: after the cone's `fst` and the nth product projection, the sheafified tensor s⊗x goes to residue(s)⊗x. The object transports in both tensor-section definitions are those of the canonical ordinary tensor witness. |
| Zero shifted-product component | Second clause of `completedScalarChainComparison_existsUnique`: the degree-i map followed by `mappingCocone.snd.v i (i-1)` is zero. Together the two cone components uniquely determine the chain comparison. |
| χ is a morphism in D(S), independent of resolution | `completedScalarComparison_existsUnique` uniquely normalizes a natural transformation from ordinary derived extension to the recorded integral scalar-extension functor on every K-flat flat-term representative, using its counit and `integralScalarExtensionComparison`. The selection `completedScalarComparison` therefore uses a unique normalized transformation, never an arbitrary triangle filler. |
| The final object is exactly integral scalar extension and its derived-limit realization | The codomain is `integralScalarExtension` from the dependency module, itself the normalized descent from `integralScalarExtensionWellDefined`. That theorem's existing representative clause asserts the derived-limit realization of precisely this tower. No replacement functor or arbitrary limit is introduced. |
| χ is an isomorphism on complete inputs, natural in K | The second conjunct asserts `IsIso ((completedScalarComparison ...).app K)` under completeness. Naturality is part of the natural-transformation type and the unique descent normalization, including all derived morphisms. |
| Ordinary extension is derived v-complete | The same conjunct asserts `IsDerivedCompleteUnrestricted l L Y ((completedDerivedScalarExtension ...).obj K)`. |
| Identity extension agrees with the completeness unit after multiplication | Final conjunct: on every good representative the identity comparison, followed by its strict-tower normalization, equals the ordinary derived counit, then the localized actual multiplication isomorphism, then the directly constructed completeness unit. `completedScalarIdentityMultiplication` is uniquely fixed by s⊗x ↦ s*x. `completedScalarIdentityUnit` is independently fixed by x ↦ 1⊗x and zero shifted component. Since good representatives localize to the entire derived category, this is the asserted identity normalization on all objects, rather than a statement only about maps to an unmarked limit. |

The docstrings give the full proof plan: valuation-ring finite freeness and rank; basis-compatible inverse limits; regular quotient/Koszul reflector units; finite sums and scalar restriction; the equality of augmented localizations for t=u v^e; the explicit tensor associativity formula identifying the specified unit; and descent, naturality and identity normalization.

Dependency declarations inspected and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`; its imported coefficient constructions are the valuation rings, chosen uniformizers and quotients.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, and its `Scheme.ProEt.topology` and constant-commutative-ring presentation. Its constant-coefficient category is not confused with completed coefficients.
- `Sheaf.Paper.CompletedIntegralCoefficients`: completed unrestricted ring and commutative-ring sheaves, finite coefficient sheaves, their projections, and the original finite-field presentation.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.Paper.DerivedComplete`: `WeilConjectures.IsDerivedComplete`; supplied unrestricted presentation described below.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`: `SheafOfModules.derivedChangeOfRingsIndependentCoefficients` and `derivedChangeRingIndependentCoefficients`, including the complete witness signature and universal counit normalization.
- `Sheaf.Paper.IntegralScalarExtension`: `WeilConjectures.integralScalarExtension`, `integralScalarExtensionComparison`, and its additive instance, exactly as on the delivered Q04 branch.
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`: `integralScalarExtensionWellDefined`, `integralScalarQuotientSheafMap`, tensor sections, finite complexes, target restriction, strict towers and the normalized descent.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` = Mathlib's `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, the standard localization and Q.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: `CategoryTheory.IsDerivedLimit`, `IsDerivedLimitTriangle`.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlatIndependentCoefficients`, `IsKFlatResolutionIndependentCoefficients`; used through the good-representative localization and the existing completeness predicate.

All already-stated proof dependencies are imported directly. The source places were checked in [Bhatt--Scholze](https://arxiv.org/pdf/1309.1198), Definition 3.4.10, Lemma 3.4.12, Proposition 3.5.1, Definition 3.5.2 and Lemma 6.8.2(1), and [Stacks 093M](https://stacks.math.columbia.edu/tag/093M). The comparison is a consequence of these statements, as the node already records.

Edge cases checked: K=0; the empty scheme (both regular modules and all products are zero); identity extension (explicit final normalization); ramified extension (cofinal powers en, without assuming equal uniformizers or unramifiedness); positive first level n=0 meaning exponent one; unbounded K (no boundedness hypothesis); arbitrary scheme without qcqs, noetherian, finite-field or characteristic restriction. The degree cannot be zero for the field inclusion. Choices of uniformizers are those already fixed by the coefficient dependency; cofinality covers differing generators.

Searches for an existing statement were run through `msearch.py` and are recorded in `searches.jsonl`:

- LeanFinder: “Finite free completed coefficient extension of derived complete sheaves equals ordinary derived change of rings”. The repeat search returned eight results including `AdicCompletion.congr`, `AdicCompletion.map`, `AdicCompletion.ofTensorProduct`, and `BDeRhamPlus`; none concerns this derived sheaf comparison.
- Loogle: `"AdicCompletion", "tensor"`. Twelve results concern ordinary module completion, including `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`, not this node.
- LeanSearch: “The completion map from ordinary derived coefficient extension to completed scalar extension is an isomorphism for a finite free coefficient algebra”. Service unavailable (Internal Server Error), recorded as unavailable.
- Mathlib grep: `finiteFreeCompletedScalar|completedCoefficientMap|derived.?complet|completedTensor`. No hits.
- Source-repository and side-library `rg`: `finiteFreeCompletedScalar|completedCoefficientMap|lem-weil-finite-free-completed-scalar-comparison`. No matching declaration. Broader scalar/completion searches located the reused tower and completion framework.
- The current server source for `Sheaf.Paper.DerivedComplete` was read and confirms the finite-field parameter. The current source for `Sheaf.Paper.IntegralScalarExtension` was unavailable; delivery branches were checked and Q04's exact three-declaration module was read and reused.

No statement correction, new mathematical notion, or disputed statement is required. Compilation checks are described below; the required dry-run result is reported in the worker return.

## Dependency modules

`def-weil-derived-complete`: `Sheaf.Paper.DerivedCompleteUnrestricted` imports the original `IsDerivedComplete` and gives `IsDerivedCompleteUnrestricted` by existentially quantifying the irrelevant finite-field datum D (in universe zero) and l≠D.p. Every coefficient sheaf, reduction and augmentation used in that predicate ignores D and this proof. Such data always exist: choose characteristic 2 if l≠2, and characteristic 3 otherwise, with a finite prime field and its algebraic closure. Thus this introduces no assumption on Y, l, E or K and retains the recorded Roos condition, including its canonical first map. It does not replace completeness by the existence of an arbitrary Roos limit of an arbitrary tower.

`def-weil-integral-scalar-extension`: this genuine unstated prerequisite had no `lean` record. The current server source and delivery branches were checked first. The supplied `Sheaf.Paper.IntegralScalarExtension` is byte-identical to Q04's already delivered module, using precisely `integralScalarExtensionWellDefined` to select its normalized functor and retain the natural representative comparison and additivity. It is included as the prerequisite packet required by the human's instruction that unstated dependencies be stated in the same delivery. No tensor, tower or descent is copied, and no independent scalar-extension notion is created.

Validation: all three node copies differ from the current shared DAG only in `lean`. Every delivered module has lines at most 100 characters, explicitly bound variables and universes, and all helper declarations listed in its owning node. The current `scompile.py` check of `DerivedCompleteUnrestricted` compiled cleanly in sandbox and library positions. The required `deliver2.py --no-push` run compiles all three actual delivered modules, including every proof import, and runs server preflight. All three actual modules passed both sandbox and final library-path compilation in this run, with the preliminary dependency checks also clean. No compiler error or non-sorry warning was emitted. The dry run then proceeds to server preflight; the second reading remains the responsibility of the second reader.

## Second reading by Q42

I independently opened the item node, all thirteen statement-dependency node records,
all three delivered modules, and the source declarations below. I found no mathematical
mismatch in the item. A late published dependency required the universe/API repair
described in the final addendum below. I added the required main-declaration lists to the module docstrings of
`FiniteFreeCompletedScalarComparison` and `IntegralScalarExtension`, which each
contain multiple declarations. All original drafted declarations and theorem statements stay
verbatim unchanged; the late repair also retains the newly published comparison name. I also updated the dependency record note to describe the
documentation difference from Q04, and appended this second-reading section.
There is no statement correction, new definition node, or target change.

The following is my object/hypothesis/conclusion checklist, made from the node before
comparing its assertions with the Lean.

| Node object or assertion | Exact Lean rendering and verdict |
| --- | --- |
| A prime ℓ | `l : ℕ` and `[Fact l.Prime]`; exact. |
| Two finite extensions E⊂L of ℚℓ, with the specified inclusion | The `E L : Type u` field, ℚℓ-algebra, finite-dimensional binders and `ι : E →ₐ[ℚ_[l]] L`; exact. Injectivity follows from the field homomorphism, and finiteness over E follows from finiteness over ℚℓ. No further instance is assumed. |
| Valuation rings, chosen uniformizers, quotient rings | The imported `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, `coefficientExtensionIdeal`, `coefficientExtensionRing`; exact. I read their bodies: the integer subring is characterized by the extending absolute value and the quotient ideal is the power of the chosen uniformizer ideal. |
| Any scheme Y and its small pro-etale site | `Y : AlgebraicGeometry.Scheme.{t}`, with `Y.ProEt` and `Scheme.ProEt.topology Y`; exact. No base field, geometric characteristic, qcqs, separatedness, Noetherianity, or nonemptiness binder is present. |
| Constant finite sheaves, completed R and S, and their projections | `integralCoefficientCommRingSheaf`, `completedIntegralCommRingSheafUnrestricted`, and `completedIntegralCommRingProjectionUnrestricted`; exact. The underlying completed ring is the limit of `integralCoefficientSheafSystem`, not the constant integer ring. |
| Canonical completed coefficient map R→S | `completedCoefficientMap_existsUnique` fixes every residue as `π_E ≫ integralScalarQuotientSheafMap`; `completedCoefficientMap` selects that unique map. Exact, including compatibility with the inclusion rather than an arbitrary ring map. |
| S is finite free of rank [L:E] as an R-module sheaf | First conjunct of `finiteFreeCompletedScalarComparison`: an isomorphism from the restricted regular S-module to the product indexed by `Fin (completedScalarRelativeDegree l E L ι)` of regular R-modules. Exact: finite products equal finite sums in this abelian category. `completedScalarRelativeDegree` uses `Module.finrank E L` with precisely `ι.toAlgebra`. |
| D(R), D(S), and ordinary derived tensor along R→S | `DerivedCategory (integralTowerModules ...)` and `completedDerivedScalarExtension`; exact. I followed every `.choose_spec` in `completedScalarChangeData` through the full universal derived-change-of-rings signature. The ordinary functor has the actual sheafified tensor objects AND maps, and the derived functor retains its universal counit. |
| Derived t-complete K, with no boundedness condition | The second conjunct quantifies every `K : DerivedCategory (integralTowerModules l E Y)` and assumes `IsDerivedCompleteUnrestricted l E Y K`; exact. The wrapper retains `IsDerivedComplete`, its canonical reduction augmentation, and its distinguished Roos triangle. |
| Every positive reduction level, with the target completed action | `n : ℕ` denotes exponent `n+1`; the tower is `integralScalarTowerFunctor`, formed from `integralScalarFiniteComplex` followed by `integralOperationsRestrict l L Y n`. Exact: restriction is along the target completion projection. |
| The strict derived limit Cone(1-s)[-1] | `integralScalarComplexFunctor` uses `integralOperationsRoosFunctor`; its object is `CochainComplex.mappingCocone` of `towerTransitionEndomorphism` with the recorded tower steps. Exact; the sign is 1-s. |
| Quotient components of the map from P⊗R S | First clause of `completedScalarChainComparison_existsUnique`: composing with `mappingCocone.fst` and the nth product projection sends `completedScalarTensorSection ... s x` to `integralScalarTensorSection ... (π_L(s)) x`. Exact for every complex, degree, level, site object, and pure tensor. Both section definitions transport the actual sheafification units through the ordinary witness's object equalities. |
| Its shifted-product component is zero | Second clause of that theorem fixes `mappingCocone.snd.v i (i-1)` to zero in every degree; exact. Together the two projections fix the chain map uniquely; this is stronger specification of the canonical construction, not an arbitrary triangle filler. |
| χ is the resulting resolution-independent map in D(S) | `completedScalarComparison_existsUnique` fixes a natural transformation by its equality on every K-flat flat-term representative, using `completedScalarCounit`, `DerivedCategory.Q.map` of the specified chain map, and `integralScalarExtensionComparison`. Exact: this is the normalized descent of that chain map. |
| Codomain is the recorded integral scalar extension and its derived-limit realization | `integralScalarExtension`, with its retained representative comparison, is selected from `integralScalarExtensionWellDefined`. I read that theorem's derived-limit clause and its uniqueness with the representative comparison; exact. No second limit functor is substituted. |
| χ is invertible and natural on complete K | `IsIso ((completedScalarComparison ...).app K)` in the second conjunct. Naturality is part of the natural-transformation type on the entire derived category. Exact. |
| The ordinary extension is derived v-complete | The other assertion in the second conjunct is `IsDerivedCompleteUnrestricted l L Y ((completedDerivedScalarExtension ...).obj K)`; exact, and concerns the ordinary extension object. |
| Identity extension gives the completeness unit after multiplication | Final conjunct compares χ on every good representative, followed by its strict-extension normalization, with the ordinary counit, localized `completedScalarIdentityMultiplication`, and localized `completedScalarIdentityUnit`. Exact: multiplication is uniquely fixed by `s⊗x ↦ s • x`, while the unit is independently fixed by `x ↦ 1⊗x` and zero shifted component. All objects have good representatives, so this equality determines the derived natural transformation, not just selected objects. |

Dependency and source checks: I opened the signatures and relevant bodies in
`CompletedIntegralCoefficients`, `ProEtaleDerivedCategory`, `RingedSiteModules`,
`DerivedComplete`, `IntegralReductionTowerUnrestricted`, `IntegralOperationsWellDefined`,
`IntegralScalarExtensionWellDefined`, `DerivedChangeOfRingsIndependentCoefficients`,
`KFlat`, and the coefficient modules. I also opened Mathlib's `constantSheaf`,
`DerivedCategory`, `HasDerivedCategory`, `SheafOfModules.restrictScalars`, and the
recorded `CategoryTheory.IsDerivedLimit` / `IsDerivedLimitTriangle`. In particular,
`integralOperationsGoodComplex` means K-flat with flat terms and no boundedness, and
`integralTowerHasDerivedCategory` supplies the standard localization without a new
hypothesis on the scheme.

I read [Stacks 093M](https://stacks.math.columbia.edu/tag/093M) and the actual
`lemma-completion-flat` in
[sites-modules.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/sites-modules.tex).
Its ring is Noetherian; the coefficient valuation ring is a DVR, so this is a
consequence of the coefficient data, not a missing assumption on Y. I read
[Bhatt--Scholze](https://arxiv.org/pdf/1309.1198), Definition 3.4.10, Lemma 3.4.12,
Proposition 3.5.1, Definition 3.5.2, and the setup of §6.8 with Lemma 6.8.2(1).
The replete-topos hypothesis is supplied here by the pro-etale site. Section 6.8
starts with any scheme; later constructibility restrictions are not hypotheses of
this coefficient/completion comparison.

I separately reviewed both delivered dependency modules against their own nodes.
`DerivedCompleteUnrestricted` is a §1(B) presentation repair: the old D and l≠D.p
parameters occur only as irrelevant coefficient/tower presentation arguments. Its
existential auxiliary datum always exists in universe zero: take the prime 2 or 3
different from l, exponent one, its finite prime field, and its algebraic closure.
It adds no condition on K or Y and does not choose a triangle map as data.
`IntegralScalarExtension` is the genuine previously unstated dependency: its functor
and retained comparison come from the normalized descent's unique compatible
isomorphism property. Additivity comes from the same witness. Thus the selection
meets the unique-object exception of AGENTS.md §5 and is not a hollow construction.
Fresh `scompile.py --source` checks for both modules returned source unavailable,
confirming that their mere absence from the local mirror is not being used to infer
publication. Both dependency modules remain part of this delivery. There are no new
nodes to review under H12.

Edge cases: the empty scheme and zero complex are allowed; no nonzero-object
hypothesis is introduced. The rank cannot be zero for a field inclusion, although
`Fin d` and the finite product are meaningful even at d=0. Tower level n=0 is the
first positive exponent, not quotient by the unit ideal. The identity inclusion is
explicitly covered. Ramification is unrestricted; neither uniformizer equality nor
unramifiedness is assumed. Arbitrarily unbounded complexes and schemes of every
characteristic are included. Site object and morphism universes stay t+1 and t,
coefficient/module size is max u (t+1), and u is independent of t. Both finite
coefficient fields may be placed in their common universe without a mathematical
restriction; all finite extensions and embeddings remain represented. No binder or
universe was left auto-implicit.

Independent searches, using different words from the worker: LeanFinder query
“For a sheaf of complete discrete valuation rings, finite free base change preserves
derived completeness and agrees with the homotopy limit of tensor reductions”
returned eight ordinary `AdicCompletion` results, none a sheaf-derived comparison.
Loogle `"SheafOfModules", "completion"` returned zero hits. LeanSearch for finite
free completed coefficient sheaves and the derived inverse limit of reductions
was unavailable (Internal Server Error), which is recorded as unavailable rather
than a negative result. I searched Mathlib's homological/category modules, all
upstream `WeilConjectures`, and the side `lean/Sheaf` with
`derived.?complete|adic.*tensor|tensor.*adic|completion.*scalar|scalar.*completion`
and the proposed declaration names. Upstream `Complete/IntegralCoefficient.lean`
was opened: it is `Sheaf J (ModuleCat (Shrink (PadicAlgCl.integers ...)))` over a
discrete constant coefficient ring with an embedding into the fixed algebraic
closure, not the completed ring-sheaf module category here. It is not an exact
existing match. Side adic tower/module-completion results likewise do not state
this canonical strict-cone comparison. No module is dropped as an existing match.

Every definition has real data or comes from a theorem determining the object up
to the equality used downstream. All theorem proofs remain `sorry`; the index
arithmetic proof in the cochain projection's type supplies only i-1+1=i. All
source/blueprint docstrings and the five proof steps (valuation/basis, inverse
limits, regular Koszul units, augmented localization and tensor associativity,
then naturality/identity) are present. I checked all three primary recorded
signatures against the literal source text and the project's signature checker;
all agree, with explicit binders, and every delivered line is at most 100 characters.

Documentation repair (H8/conventions): the two multi-declaration module headers
lacked the main-definition/statement lists required by brief-stage2 §3. Those
lists are now present. The worker report above describes the original packet;
IntegralScalarExtension now differs from Q04 only by this module documentation.

Validation in the second reading: the explicit three-file `scompile.py Q42
lem-weil-finite-free-completed-scalar-comparison ...` run completed with exit 0.
Both preliminary checks and all three sandbox/library-position pairs passed with
no errors or warnings. Reported elapsed times include waiting for shared compiler
slots; the wrapper retains its 60-second compiler limit after slot acquisition.
The required delivery dry run below rechecks the final documentation-adjusted
sources and server preflight before push.

The final-source `deliver2.py Q42
lem-weil-finite-free-completed-scalar-comparison --no-push` completed with exit 0
and printed `OK (dry run): commit 0ce1e3ef42 passes the preflight and compiles;
nothing pushed`. Its packet contains exactly the three modules, their three
node records, and this report. The wrapper correctly retained the current base's
`reviewed_lean` bookkeeping rather than delivering the stale dependency copy.

Late publication and §1(B) dependency repair: immediately after the successful
first dry run, I checked the server dependency source again because the dry run
reported new `reviewed_lean` bookkeeping. `scompile.py --source
Sheaf.Paper.IntegralScalarExtension` now returned Q11's newly published module.
I stopped the push wrapper during preliminary compilation, before it created or
pushed a delivery commit. Thus the earlier source-unavailable checks and the
first dry-run result above describe their times correctly, but no longer describe
the current dependency.

I read the new source in full. Q11's `integralScalarExtension` has
`Y : Scheme.{u}` with the very same u as E and L. Our item has `Y : Scheme.{t}`
with independent t and u; restricting to t=u would silently add a universe
condition. The underlying `integralScalarExtensionWellDefined` already has the
independent t,u interface, so this is precisely the authorized §1(B) repair of
an unusable recorded presentation, not a change to either mathematical statement.
The existing supplied module already states the unrestricted construction. I
retained it, updated `lean.note` to give this actual reason, preserved Q11's
public imports, and preserved its newly published name
`integralScalarExtensionOnGoodIso` as the same normalized comparison exposed as
`integralScalarExtensionComparison`. The four definitions use actual data from
the same normalized descent witness; there is no new theorem or new choice.
The only change beyond the documentation repair and report is this compatibility
definition and retention of the newly published public imports. Earlier claims of
byte identity with Q04 apply to the initial packet, before this late repair.

The repeated dry run after the late dependency repair also completed with exit 0:
`OK (dry run): commit e88bff0441 passes the preflight and compiles; nothing pushed`.
All three final modules passed sandbox and library-position compilation, with no
errors or non-sorry warnings. The repaired dependency and its preserved public
name are included in this successful final packet.
