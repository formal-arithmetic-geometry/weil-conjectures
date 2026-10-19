## Worker report

The module `Sheaf/Paper/ResidueLisseProjectiveModels.lean` states
`WeilConjectures.residue_lisse_projective_models`.  It binds a prime `l`, a finite
extension `E`, an affine weakly contractible scheme `S`, and an integral derived
object `K`.  The hypotheses render derived completeness, residue constructibility
through the unrestricted integral constructible predicate, and one finite Tor
interval for the degree-one scalar reduction.  The conclusion quantifies a finite
family of opens indexed by `Fin n`, whose supremum is `⊤` and whose members are
pairwise disjoint.  On every member it gives a bounded complex over the completed
coefficient sheaf, a splitting into a finite product of copies of the unit sheaf in
each degree, and an isomorphism from the canonical derived pullback of `K`.
The differential is an arbitrary differential of the displayed cochain complex, so
no constancy of its entries is asserted.

The declarations used are:

* `WeilConjectures.IsDerivedCompleteUnrestricted` from
  `Sheaf.Paper.DerivedCompleteUnrestricted`;
* `WeilConjectures.scalarReductionDerivedExtension` from
  `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`;
* `AlgebraicGeometry.Scheme.HasFiniteProEtaleTorAmplitude` from
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`;
* `WeilConjectures.integralDerivedPullback` and
  `WeilConjectures.integralTowerModules` from
  `Sheaf.Paper.IntegralDerivedOperations` and
  `Sheaf.Paper.IntegralReductionTowerUnrestricted`;
* `WeilConjectures.completedIntegralCoefficientSheafUnrestricted` from
  `Sheaf.Paper.CompletedIntegralCoefficients`;
* `AlgebraicGeometry.Scheme.IsWeaklyContractible` from
  `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`;
* `AlgebraicGeometry.Scheme.Opens`, `Scheme.Opens.ι`, and `Disjoint` from Mathlib.

The hypotheses and clauses are rendered as follows.  `hS` is the affine hypothesis;
`hweak` is evaluation-surjectivity for every locally surjective sheaf map on the
terminal pro-etale object; `hcomplete` is the unrestricted derived-completeness
predicate; `hresidue` is the existing integral constructibility predicate, which
includes finite cohomological support and constructibility of every residue
cohomology sheaf; and `hTor` is the universal finite Tor interval predicate.  The
cover clauses are `(⨆ i, U i) = ⊤` and pairwise `Disjoint`.  Bounds are rendered by
`P.IsStrictlyGE a`, `P.IsStrictlyLE b`, and `a ≤ b`.  A projective term is rendered
by maps `ι` and `ρ` with `ι ≫ ρ = 𝟙 _` into a finite product of unit sheaves.
The final `Nonempty` is the representing derived isomorphism.

Edge cases checked: `Fin n` permits `n = 0`, which is the required empty-cover case
for an empty scheme; `Fin 0` also makes the finite product in a term a genuine empty
product; the bounds allow `a = b`; and all differentials remain arbitrary sheaf
maps.  No characteristic or nonzero-ring assumption is introduced.

Searches made: `msearch.py leanfinder` with “finite disjoint open cover bounded
complex direct summands completed coefficient sheaves” (no matching local-model
theorem); `msearch.py loogle` with
`IsProEtaleSitePerfect, StrictPerfectCoefficientPackageOnSite,
integralDerivedPullback` (no matching theorem); and `msearch.py grep` with
`residue.?lisse|projective.?model|finite.?projective` under Mathlib
(`0 hits`).  Repository searches used `rg` for residue/lisse/projective model
names and for `lem-fix-residue-lisse-projective-models`; the only nearby result was
the distinct adic theorem `residue_lisse_perfect_lift`, whose coefficient datum,
Noetherian and compactness hypotheses do not match this node.

The module also supplies explicit sheafification and locally-bijective instances
for the full and sliced pro-etale sites, using `essentiallySmallSelf`; these are
the canonical size transports needed to form the displayed derived categories.

## Earlier second reading (a previous round; superseded)

I reread the node and the complete Lean signature after compilation.  The prime,
finite extension, affine weak-contractibility condition, derived object, completeness,
residue constructibility and finite-Tor hypotheses all occur as explicit binders.
The conclusion has finite `Fin n` indexing, coverage by supremum, pairwise
disjointness, boundedness, degreewise split finite-unit terms, and the canonical
derived-pullback isomorphism.  The file compiles cleanly with the expected `sorry`
proof warning suppressed by the project options.


## Second reading by NB

I independently read the node's statement and all eight proof steps, the sandbox
module, every statement-dependency binding, and the actual signatures used by the
module. I read Stacks `proetale.tex`, definition-Dbc and
lemma-describe-constructible-complexes (09C2), followed by
lemma-local-structure-constructible-complex (09C3), including its proof, and
`algebraization.tex`, lemma-restriction-derived-complete-equivalence (099I).
There is no repair note for this item. There are no new nodes, dependency modules,
or `statement_change` in this delivery; the mathematical node is unchanged.

The following is my object/hypothesis/conclusion checklist, formed from the node
before comparing it to the Lean.

| Node item | Lean rendering and verdict |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]`; exact, including ell = 2. |
| Finite extension E/Q_ell | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`; exact. |
| R, uniformizer, and k | The recorded `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and `coefficientExtensionRing l E 1` used by the coefficient interfaces; exponent one is the residue quotient, not exponent zero. |
| Affine scheme S | `(S : Scheme.{u}) (hS : IsAffine S)`; exact, no Noetherian condition on S. |
| Small pro-etale site | `Scheme.ProEt S`, `Scheme.ProEt.topology S`, and the identity object `Scheme.ProEt.mk (𝟙 S)`; exact. |
| Evaluation on S lifts epimorphisms of sets | `hweak : ...IsWeaklyContractible.{u + 1} ...`; opened its upstream definition, which tests locally surjective sheaf maps. On this sheaf topos epimorphism and local surjectivity agree. I fixed the sets universe explicitly to the site object universe. |
| B_U is the limit of positive constant quotients | `completedIntegralCoefficientSheafUnrestricted l E U`; opened its construction: it is `limit (integralCoefficientSheafSystem ...)`, whose zero-based n denotes exponent n+1, with actual quotient transitions. It is not the discrete constant ring R. |
| Arbitrary K in D(Mod(B_S)) | `K : DerivedCategory (integralTowerModules.{u, u} l E S)`; the abbreviation is the actual `SheafOfModules` category, with standard localization and no boundedness built in. |
| Completeness for canonical restricted reduction tower | `hcomplete : IsDerivedCompleteUnrestricted l E S K`; read both this wrapper and `IsDerivedComplete`. Its K-flat representative, canonical augmentation cone, and Roos triangle use the quotient projections and reduction transitions; no arbitrary map replaces the unit. Its auxiliary existential finite-field datum is irrelevant to these constructions and imposes no characteristic condition on S. |
| K_1 is derived residue tensor | `(scalarReductionDerivedExtension.{u, u} l E S 0).obj K`; opened its source/target and universal derived-change-of-rings witness. It is tensor along the actual completed projection to exponent one, not ordinary underived reduction. |
| Only finitely many nonzero residue cohomology sheaves | First conjunct of `hresidue : intrinsicFiniteTorsionConstructible l E 1 (by omega) S K_1`; opened the definition and its `Set.Finite` support. Exact. |
| Every residue cohomology sheaf is constructible | Second conjunct of that same predicate, using `IsConstructibleProEtaleModuleSheaf`. Opened the finite-stratification, locally constant restriction and finite geometric module-stalk clauses. This is intrinsic pro-etale constructibility and does not add etale origin. |
| Every residue cohomology sheaf is locally constant on S | **Missing in the original Lean.** Added `hlisse : ∀ q : ℤ, IsLocallyConstantProEtaleModuleSheaf S ... ((DerivedCategory.homologyFunctor ... q).obj K_1)`. Opened the predicate: localized-site restrictions become constant module sheaves on an actual pro-etale covering. Combined with finite constructible stalks over the finite residue field, this is precisely finite-dimensional local models. |
| One finite Tor interval works on all local tests | `hTor : HasFiniteProEtaleTorAmplitude S k K_1`; opened both Tor predicates. The existential a,b is outside all test module sheaves and every representative/K-flat resolution is tested. This intrinsic sheaf-theoretic amplitude condition is equivalent to the node's all-localizations wording: restriction preserves the tensor calculation and cohomology, and any module on a localization can be tested by extension by zero along that localization; conversely the identity localization gives this global test. Thus no separate interval depending on the test module or U is introduced. |
| Finite disjoint open cover | `∃ (n : ℕ) (U : Fin n → S.Opens), (⨆ i, U i) = ⊤ ∧ Pairwise ...Disjoint...`; exact. Each open is clopen because the finite union of the other opens is its complement. |
| On every member a bounded complex over B_U | The `∀ i` existential `P : CochainComplex (integralTowerModules ... (U i).toScheme) ℤ`, with `a ≤ b`, `P.IsStrictlyGE a` and `P.IsStrictlyLE b`; exact. Read Mathlib's support definitions: terms are zero outside the finite interval. |
| Every term splits off a finite sum of B_U | For each degree r, `N : ℕ`, inclusion `ι : P.X r ⟶ ∏ᶜ ...unit B_U`, retraction in the reverse direction, and `ι ≫ ρ = 𝟙 _`. A finite product is the same finite biproduct in this abelian category, so this is the required finite sum and the correct splitting orientation. |
| This model represents K restricted to U | `Nonempty ((integralDerivedPullback l E (U i).ι).obj K ≅ DerivedCategory.Q.obj P)`; read the completed derived pullback and its representative normalization. Here the finite disjoint open cover makes U clopen. Restriction to a clopen factor is exact and preserves all limits and canonical quotient towers, so completed pullback of the complete K agrees with ordinary restriction K|U. The target uses precisely B_U. |
| Arbitrary sheaf-linear differentials | P is an arbitrary cochain complex of B_U-module sheaves. No constant-matrix condition occurs. Exact. |

The source assumes Lambda Noetherian, an ideal I, and K in D_cons. At Lambda=O_E,
I=(varpi), the existing DVR coefficient construction supplies Noetherianity rather
than adding a hypothesis on S. The D_cons hypotheses expand to the completeness,
constructibility and Tor conditions above; 09C3 additionally assumes lissity of
residue cohomology. Tag 099I is the stated completed-coefficient comparison.
The source proves completed constant projective module terms. In this field-residue
specialization the node's eight-step free-model induction gives its stated sheaf
summands without imposing constant integral differentials. I found no source-based
fault requiring a correction of the node or any target unit.

Dependency interfaces were checked beyond their names. `ProEtaleDerivedCategory`
uses intrinsic constant-ring `SheafOfModules`, while fixed ModuleCat-valued sheaves
are a separate encoding. The modules recorded for local constancy and constructibility
also publicly retain the original ringed-site declarations used by the recorded
`intrinsicFiniteTorsionConstructible` predicate. I opened both versions and used
those original declarations; there is no private copy. `integralTowerModules` and
`scalarReductionSource` are definitionally the completed-ring module category,
and `scalarReductionTarget` at 0 is the intrinsic residue category. The completeness
wrapper and completed pullback keep their canonical quotient normalizations.
`ringedSiteModules`, `restrictScalars`, `limit`, `constantSheaf`,
`DerivedCategory`, `homologyFunctor`, `Scheme.Opens.ι`, and the support bounds
were checked in their actual source modules. I added the already-landed coefficient,
completion, reduction, constructibility, Tor-amplitude and operation nodes to
`stmt_deps`, so these direct interfaces are recorded explicitly.

Edge cases checked: n=0 is allowed for the cover, and the supremum over Fin 0 is
bottom, giving the empty scheme its empty cover. Zero residue is allowed and yields
the zero model by derived Nakayama, without an implicit nonzero-object requirement.
Finite products allow N=0 and hence the zero term; bounds may coincide. All residue
degrees q are tested, including zero sheaves outside the finite support. No condition
ell != char(S), finite-field base, local Noetherianity, nonempty S, positive rank,
or constant differential is added. The common ambient u is the recorded intrinsic
site/coefficient size convention; site objects remain in u+1 and morphisms in u,
with module values in u+1 and the coefficient ULift. It does not equate the object
and morphism universe of the site. All variables are bound, `autoImplicit` is false,
and the set-sheaf universe in weak contractibility is now explicit.

Independent searches on 2026-10-17, using msearch.py for this group/item:

- LeanSearch: "A complete sheaf complex with finite lisse residue has a bounded local projective model". Eight hits about finite presentations/local generators and regular-topology sheaves; none is this theorem.
- LeanFinder: "derived adic complete sheaf complex finite projective local models weakly contractible". Eight hits about solid condensed modules, finite presentation, and K-projectivity; none gives this local-model theorem.
- Loogle: `"IsLocallyConstantProEtaleModuleSheaf"`; zero hits.
- Mathlib grep through msearch: `projective.*model|model.*projective|lisse.*residue`; zero hits.
- Direct rg with `local.*structure.*constructible|residue.lisse|projective.model|completed.*projective` on the supplied upstream WeilConjectures tree and side Lean: I opened the closest candidates. Upstream `SixFunctors/ProEtale/Derived/Perfect.lean` proves finite Tor/constructibility from an existing bounded retract model, not this complete integral residue-to-model assertion. `residue_lisse_perfect_lift` in `ResidueLissePerfectLift.lean` requires locally Noetherian/compact X, an adic datum, and etale-local constant perfect residue; it is not this theorem on arbitrary weakly contractible affine S. Site-perfect and ring-perfect model statements have different premises and coefficient categories. No exact existing match was found.

Repairs made:

1. Added the missing `hlisse` hypothesis; the worker report had incorrectly treated constructibility alone as supplying global local constancy.
2. Made `IsWeaklyContractible.{u + 1}` explicit; the original left the tested set universe unconstrained.
3. Added the theorem's source/blueprint docstring and the full eight-step proof plan with the node's dependency names. The original theorem had no declaration docstring.
4. Removed all four copied sheafification/local-bijectivity instances. Full-site instances already come from the imported `SfIntegralReductionTower` via `SfIntegralConstructible`; slice instances were unused (and also exist elsewhere). The retained `SfIntegralConstructible` import is needed for its universe-specialized sheafification instances, not an extra constructibility assumption. No extra definition or theorem is introduced.
5. Added the already-recorded proof-dependency imports and the direct-interface stmt_deps; synchronized `lean.statement` verbatim with the final signature and removed the four deleted instances from `lean.declarations`.

Validation: scompile.py compiled the sole delivered module both as sandbox and as
its library module, cleanly with exit 0 (2.9 s and 3.1 s). An earlier attempt after
removing the copied instances also removed their existing instance-provider import;
Lean diagnosed unresolved max-universe instance metavariables. Restoring the existing
`SfIntegralConstructible` import fixed this without adding assumptions or copies.
The original Worker report above is retained as required; the corrections here
supersede its claims about lissity and the four copied instances.
