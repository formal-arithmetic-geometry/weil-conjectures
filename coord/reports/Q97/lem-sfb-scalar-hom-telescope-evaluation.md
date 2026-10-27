## Worker report

Item: `lem-sfb-scalar-hom-telescope-evaluation`, group Q97, stage 2, 2026-10-22.
Module: `Sheaf.Algebra.Homology.ScalarHomTelescopeEvaluation`.
Main declaration: `CategoryTheory.scalarHom_telescope_evaluation`.
The item theorem has the sole new `sorry`. The repaired dependency module retains its
current live completed proof and proof helpers unchanged; this repair proves nothing new. All helper definitions contain real data;
there is no chosen arbitrary comparison, new axiom, or postponed definition.

The node's natural-language statement, proof, and proof dependencies are unchanged.
The already-landed `def-sfb-scalar-hom-comparison-data` owns the normalized models
used in the binders. The new `def-sfb-localization-hom-comparison-data` owns the five
plain continuity/comparison definitions extracted from the theorem module. The item
cites this definition node in `stmt_deps`; `lem-sfb-internal-hom-localization-comparison`
stays in `proof_deps` and is imported only as a proof dependency. Its accompanying
§1(B) module publicly imports the new definition module. Only its `lean` field changes.
The telescope helpers are statement-local packaging in the owning node's module,
listed in `lean.declarations`, as authorized by the missing-helper paragraph.

### Hypotheses and objects

- Site small in the module universe: `{C : Type u} [SmallCategory C]` and
  `J : GrothendieckTopology C`. This is the chosen small site of the size convention;
  coefficients, module values and the site lie in its chosen universe `u`. It does
  not require a geometric site's original object and arrow universes to coincide:
  the statement already requests a site small in the module universe, after the
  convention's skeleton/replacement. No geometric site or coefficient ring is fixed.
- Arbitrary commutative coefficient ring: `(A : Type a) [CommRing A]`, with its own
  independent universe `a`; ring sheaf `(R : Sheaf J CommRingCat.{u})`.
- Map to global sections: `aR : A →+* RingCat.sectionsSubring
  (R.obj ⋙ forget₂ CommRingCat RingCat)`, exactly the existing coefficient action's
  signature. This compatible family is Γ(C,R); `(t : A)` is arbitrary.
- Module sheaves: the public existing `SheafOfModules.scalarModules J R` abbreviation
  is exactly `ringedSiteModules` on the ring sheaf with commutativity forgotten.
- Ordinary unbounded derived categories and Q: existing `DerivedCategory` and
  `DerivedCategory.Q`. The binder `∀ B : Sheaf J CommRingCat.{u},
  HasDerivedCategory.{w} (scalarModules J B)` supplies the chosen localizations for
  the existing simultaneous scalar model interface. Universe `w` remains independent.
- Exact filtered colimits impose no extra witness: module sheaves on this small site
  are Grothendieck abelian by the existing
  `grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses` theorem.
  This is the same treatment used by the recorded localization-comparison dependency;
  ordinary colimits below are the sheaf-module complex colimits, hence termwise.
- S and R→S are the actual `ringedLocalizationRing R (aR t)` and
  `ringedLocalizationRingUnit R (aR t)`. These are the small-site versions retained
  publicly by the recorded independent-universe localization module. No substitute
  coefficient ring is introduced. RingedSiteLocalization supplies the ordinary
  sheaf-module telescope/section-localization convention.
- `M : ScalarHomModels.{u,u,u,w} J`, `μ` and `α` are precisely the normalized tensor,
  scalar-derived-pair and scalar-Hom-adjunction presentations of the recorded nodes.
  Their existence is `scalarInternalHomAdjunction_exists`; they are presentations
  of the specified operations, not extra flatness or continuity hypotheses.
  Their fields retain actual extension objects/maps, the ordinary sectionwise unit,
  the universal derived pair, its K-flat computation, representative evaluation,
  and the five canonical Hom bijections. `M.scalar ... |>.derived` is F;
  `scalarDerivedRestriction ...` is U; the adjunction unit is η.
- `derivedInternalHomOfUniverses.{u,u,u,w} J R` is H_R, and `M.closed R` provides
  its existing relative derived tensor and evaluation. These are the models tied
  to the actual total tensor complexes and K-flat complexes by `M.model`.
- `_hK : HasLocalizationHomContinuity.{u,u,u,w} J R K` is used verbatim. Opening its
  definition gives every sequential complex diagram with one common termwise lower
  bound, with `IsIso` of the Q-image of the actual `colimit.post` for the fixed
  functorial K-injective Hom representatives. It neither assumes continuity for
  arbitrary unbounded diagrams nor asks for constructibility or perfectness.
- `_hL : ∃ n : ℤ, L.IsGE n` is cohomological boundedness below, not a termwise bound.

### Every conclusion clause

- `scalarHomTelescopeDiagram A t` has constant object P and transition `t • 𝟙 P`.
  Its natural transformation on a chain map f is f at every stage; its structure
  law uses only the existing linearity and category identities. In
  `scalarHomTelescope`, the coefficient instance is explicitly the recorded
  `scalarLocalizationCoefficientLinear A R aR`, so there is no arbitrary A-action.
- `scalarHomTelescope` composes that actual diagram with Mathlib `colim` on complexes.
  `scalarHomTelescopeLeg ... P n` is exactly `colimit.ι ... n`, the node's j_n.
- `scalarHomTelescopeLambda ... T n` is η_T followed by U applied to
  `(IsLocalization.Away.invSelf t)^n • 𝟙 (F.obj T)`. The scalar instance is explicitly
  `scalarLocalizationDerivedLinear (Localization.Away t) S
  (scalarLocalizationCoefficientMap A R aR t)`, the specified localized action.
  Composing with the unit makes this precisely t^(-n)η_T; restriction is not assumed
  linear over the localized coefficient ring.
- The two existential `ScalarHomTelescopePresentation`s specialize T to H_R(K,L)
  and L. The field `iso` is universally quantified over a complex P and every
  supplied isomorphism `e : Q.obj P ≅ T`; it is exactly β_H or β_L, as applicable.
  Thus the theorem covers every pair C_H,C_L and every specified e_H,e_L.
- The field `legs` reads `Q.map j_n ≫ β.hom = e.hom ≫ λ_n(T)` for every natural n,
  exactly both β leg formulas, in Lean's left-to-right composition convention.
- `localizationHomRestrictedComparison` is the recorded ρ: U applied to the actual
  evaluation-transpose χ, followed by the evaluation-normalized α. Its definition
  uses extended evaluation and the inverse strong tensor comparison; α's evaluation
  field precomposes with η_K, so no arbitrary scalar-Hom comparison is substituted.
- `scalarHomTelescopeGamma` is the actual composite
  `β_H.hom ≫ ρ ≫ H_R.map (1, β_L.inv)`. This is the explicit formula in proof step 6
  of the node. Its construction identifies the comparison itself, not only its
  endpoints or an arbitrary arrow satisfying the same stage restrictions.
- The theorem's first conjunct asserts `IsIso` of this exact gamma for each pair
  of representatives and supplied isomorphisms. This is equivalent to providing
  an isomorphism whose hom is that arrow (Mathlib `asIso`).
- The next conjunct is `γ ≫ H_R.map (1, β_L.hom) = β_H.hom ≫ ρ`, exactly the first
  displayed gamma square.
- Its following `∀ n` is `Q.map j_H,n ≫ γ = e_H.hom ≫
  H_R.map (1, e_L.inv ≫ Q.map j_L,n)`, exactly the second displayed formula. The
  H-leg and L-leg remain different, even when their representatives happen to agree.
- Each presentation's `change` quantifies every quasi-isomorphism f with
  `Q.map f ≫ e'.hom = e.hom`, and asserts the β square for the actual telescope
  colimit map. The theorem's second large conjunct gives the gamma square for
  simultaneous quasi-isomorphisms f_H,f_L satisfying both matching conditions.
  The β squares imply invertibility of their Q telescope maps; therefore these
  equalities also apply in reverse and to zigzags, as the node requests.
- The last `∀ n : ℕ` is exactly
  `tensor.map (ρ ∘ λ_n(H), 1_K) ≫ ev(K,UFL) = ev(K,L) ≫ λ_n(L)`.
  It is equality in D(R) of the displayed tensor-evaluation morphisms. No degree,
  cohomology-only image, global-section shadow, or abstract isomorphism replaces it.
  The natural-number quantifier includes n=0.
- There is no termwise boundedness binder on either representative. There is no
  completeness, constructibility, nonzerodivisor, nonzero-ring, perfectness,
  flatness-of-K, or flatness-of-representative hypothesis.

### Dependency declarations read and used

All stmt_deps were read, including their natural-language statements and recorded
Lean or Mathlib interfaces, and the source signatures/docstrings were opened.

| Node/interface | Module and declaration used |
| --- | --- |
| Size convention | Metatheoretic convention; explicit `u`, `a`, `w` and `SmallCategory` implement it; no substitute definition |
| Scalar actions | `Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions`: `scalarLocalizationCoefficientLinear`, `scalarLocalizationDerivedLinear`, `scalarLocalizationCoefficientMap` |
| Module category | `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, through the existing `scalarModules` abbreviation |
| Derived category | `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`, `HasDerivedCategory` |
| Localization | `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`, publicly retaining `RingedSectionLocalizationRing`: `ringedLocalizationRing`, `ringedLocalizationRingUnit` |
| Section/telescope convention | `Sheaf.CategoryTheory.RingedSiteLocalization`: `ringedSiteSectionLocalization` |
| Change of rings | `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`: `DerivedChangeOfRingsCochainModel`, `nonempty_derivedChangeOfRingsCochainModel`; retained in the normalized scalar model |
| Restriction | `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`, through `scalarRestriction` and `scalarDerivedRestriction` |
| Scalar adjunction | `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`: `sheafRingDerivedCoefficientAdjunction`; retained in `ScalarDerivedPair` |
| Internal Hom | `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: `derivedInternalHomOfUniverses` |
| Total tensor | `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`; the actual representative tensor used by `M.model` |
| K-flat complexes | `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: `CochainComplex.IsKFlatIndependentCoefficients`; part of the recorded tensor/scalar models |
| Colimits | `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.ι`, `colim`; and `Functor.ofSequence`, `NatTrans.ofSequence` |
| Scalar-Hom normalization | `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`: `scalarInternalHomAdjunction_exists`; its public `ScalarInternalHomData`: `ScalarHomModels`, `ScalarHomTensorComparison`, `ScalarInternalHomAdjunction` |
| Continuity and χ,ρ | `Sheaf.Algebra.Homology.LocalizationHomComparisonData`: `localizationHomComplex`, `localizationHomContinuityMap`, `HasLocalizationHomContinuity`, `localizationHomComparison`, `localizationHomRestrictedComparison` |
| Localization theorem (proof only) | `Sheaf.Algebra.Homology.InternalHomLocalizationComparison`: `internalHom_localization_comparison` |
| Evaluation | `Sheaf.Paper.CoefficientRingedTensorHomModel`: `CoefficientClosedStructure.tensor`, `.evaluation`, `.transpose`; `CoefficientTensorModels` |

All recorded proof dependency modules are imported: `ScalarLocalizationSheafExact`,
`SheafRingDerivedCoefficientAdjunction`, `ExactFunctorDerivedFunctor`,
`KFlatResolutionIndependentCoefficients`, `DerivedChangeOfRingsCochainModel`,
`ScalarLocalizationTelescopeCore`, `ScalarLocalizationUnitFactors`,
`ScalarLocalizationCoefficientActions`, `ScalarInternalHomAdjunction`,
`InternalHomLocalizationComparison`, `RingedDerivedClosedSymmetricMonoidal`, and
`CoefficientRingedTensorHomModel`. Their proofs remain future stage-3 work for this
node; the docstring carries all seven node proof steps and their dependency ids.

### Edge cases

Checked before finalizing the statement:

- n=0: invSelf(t)^0 = 1; lambda is η, so evaluation is the unit-stage normalization.
- t=1 or any unit: the telescope identifies with the original object; stages carry
  the prescribed inverse powers, including units not equal to one.
- t=0 or nilpotent: localization and the derived telescope are zero. No invertibility
  of t in R, domain assumption, or nonzero coefficient ring was introduced.
- t-torsion: genuine localization and the filtered colimit retain the eventual-zero
  relation; no injectivity of the transition maps is assumed.
- Zero ring, zero K or L, and empty site: all constructions and iso formulas remain
  meaningful; there is no Nonempty or Nontrivial hypothesis.
- A bounded-below derived L with an unbounded representative (for example, adding
  an unbounded contractible complex) is included without any termwise restriction.
  The same check applies to C_H, even if its Hom object has unbounded cohomology.
- Distinct representatives, arbitrary supplied e_H,e_L, changes in only one input,
  and backward zigzag arrows are all included in the explicit quantifiers.

### Searches

Prescribed `msearch.py Q97 lem-sfb-scalar-hom-telescope-evaluation` searches:

1. `leanfinder "Derived internal Hom scalar localization telescope colimit legs evaluation pairing"`:
   eight hits, including `LightCondensed.ihomPoints_apply`, `ModuleCat.ihom_ev_app`,
   `HomologicalComplex.isColimitOfEval` and a colimit/evaluation transport formula.
   None states scalar-localization Hom compatibility with all telescope legs.
2. `loogle "CategoryTheory.Limits.colimit.ι, CategoryTheory.Functor.ofSequence"`:
   zero hits. The two constructions were subsequently opened in Mathlib source.
3. `grep "telescope|localization.*[Ee]valuation" CategoryTheory`: zero Mathlib hits.
4. `leansearch "constant sequential diagram scalar multiplication telescope functor"`:
   eight hits, notably `Functor.ofSequence` and `Functor.OfSequence.map`, plus
   unrelated scalar action/sequential product declarations. Used `Functor.ofSequence`.
5. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
   `scalarHomTelescope`, `hom_telescope`, and telescope/evaluation combinations:
   found `sequence_relative_hom_telescope` and its `ScalarLocalizationDerivedHom`
   consumer, which concern relative/global Hom and do not supply this internal-Hom
   representative square or evaluation equality. No exact existing declaration.
6. `rg` in Mathlib CategoryTheory, Sheaf/CategoryTheory and upstream CategoryTheory
   for sequence/telescope functors found `Functor.ofSequence`, `NatTrans.ofSequence`
   and unrelated module-category telescope complexes. The helper is the actual
   functorial use of these existing constructors, not a copied tensor/localization.
7. `rg` in `dag/lean_names_upstream.json` and upstream sources for this item and
   scalar-Hom telescope names found no existing attachment.

Source read: local Bhatt--Scholze PDF, printed pages 61--62 (Lemma 6.8.12,
Proposition 6.8.14(2), Remark 6.8.15), and the current blueprint unit
`main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-dc-restricted-functors/_section.md`.
The PDF supplies the conditional localization route; the DAG explicitly records the
additional representative-normalized evaluation extraction and its seven-step proof.

No STATEMENT-DISPUTED issue or source correction was found.

## Second reading by Q97

Performed a fresh self-check of the node and completed source file. No second agent
was started, as the dispatch brief forbids it; the maintainer performs the independent
review after delivery. This paragraph does not claim independent worker review.

Rechecked the exact composition directions: beta's equations are Q(j) then beta,
e then lambda; gamma's square is gamma then H(beta_L), beta_H then rho; the gamma
leg uses e_L inverse then the L leg; evaluation tensors rho after lambda with id_K.
Rechecked the actual definition of rho and alpha's evaluation normalization, rather
than merely their endpoint types. Rechecked that telescope maps are induced by the
same chain map at every stage, and that all coefficient instances are specified
inside real definitions. Rechecked the common termwise lower bound belongs only
to the continuity predicate, while L's own lower bound is cohomological and neither
representative carries a bound. Rechecked quantification over all supplied e_H,e_L
and n=0, as well as simultaneous quasi-isomorphism squares. No mathematical clause
was changed during this reading; elaboration required explicit universe arguments
on the normalized scalar comparison interfaces, and no universe equality or extra
hypothesis was added.

## New nodes

`def-sfb-localization-hom-comparison-data` owns
`Sheaf.Algebra.Homology.LocalizationHomComparisonData` and exactly the five existing
definitions `localizationHomComplex`, `localizationHomContinuityMap`,
`HasLocalizationHomContinuity`, `localizationHomComparison`, and
`localizationHomRestrictedComparison`. No duplicate is left in their former module.
The new node describes all five constructions, rather than asserting the localization
theorem: the actual fixed K-injective Hom functor, Q of colimit.post, common-termwise-
lower-bound continuity, transpose of extended evaluation through inverse μ, and its
restriction followed by normalized α. Each definition's original signature and body
are retained; only its blueprint ownership in the docstring changes. All c,v,r,w
universes remain independent. Its dependencies are exactly the seven notions cited
in its statement. Its definition module imports the existing ScalarInternalHomData,
without importing either scalar-Hom adjunction or localization-comparison theorems.

Source: Bhatt–Scholze Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61–62, conditional
internal-sheaf extraction; Stacks 03DB, 07A4, 07A6, 08J7, 08J9 and 0A95. This owns the
already-reviewed maps and predicate; it makes no new mathematical assertion.
Before extraction, rg through dag/nodes, lean/Sheaf and lean/WeilConjectures found
these exact names only attached to the theorem node and used by its consumer
IntegralGeneralLfpHomInversion. No definition node owned them. blueprint_refs ancestor
returned None, and search "internal Hom localization" returned zero blueprint nodes.
`msearch.py leansearch` with "Derived internal Hom sequential colimit continuity
comparison on complexes of module sheaves" returned eight general colimit declarations;
`leanfinder` with "Canonical scalar extension internal Hom comparison transpose
evaluation restriction adjunction" returned eight ordinary ModuleCat adjunction
results. `grep` for the three continuity/comparison names returned zero Mathlib hits.
The exact outputs are retained in the node's mathlib_searches. These searches identify
the existing definitions for movement, not a reason to create a second copy.

## Dependency modules

`lem-sfb-internal-hom-localization-comparison`:
`Sheaf.Algebra.Homology.InternalHomLocalizationComparison` now publicly imports
LocalizationHomComparisonData and no longer declares its five definitions. The old
record bundled independent notions in a theorem's module without definition ownership,
so it could not serve as their H2/H12 statement dependency. Its `lean.declarations`
now lists only `internalHom_localization_comparison`, and `lean.note` explains this
§1(B) repair. Every non-lean field of the dependency node is byte-for-byte preserved
as JSON data. Its current live theorem, all proof helpers and the completed proof are
retained, rather than replaced by a sorry or the old returned dependency version.
The public import preserves the interface for existing consumers such as
IntegralGeneralLfpHomInversion; no declaration is renamed and every moved body is
unchanged. The new module owns only definitions and contains no theorem or sorry.

## Repair of return L at af979f5c9b0c

H2/H12: moved all five definitions into a new definition-owned module; copied the
comparison theorem node with a lean-only explanatory record; replaced that theorem
by the new definition node in the item's stmt_deps; retained it in proof_deps. The
main theorem's signature, proof docstring, hypotheses and conclusion are unchanged.
The required initial saved-packet dry run passed at 4f98ed5e366, which did not detect
the semantic ownership fault. The repair follows the independent return anyway.
Compared the packet's non-lean mathematical fields to current main and fetched the
live dependency source with scompile.py --source; the local and server source agree.

### Second reading of the repair by Q97

Read the new node against all five declarations: Γ uses coefficientHomResolution
then homComplexFunctor at Q.objPreimage K; the continuity map is precisely Q.map of
colimit.post; its predicate quantifies every ℕ-diagram with a common strict lower
bound; χ transposes μ.inv followed by F(evaluation); ρ is U.map χ followed by α.
No choose from a theorem is introduced. Rechecked all moved bodies verbatim against
the live source and confirmed no copy remains in the old module. The old theorem's
signature and completed proof remain intact. The item now publicly imports the new
definition module and only privately imports the theorem for stage 3. All earlier
clause-by-clause and edge-case checks therefore still apply, including n=0, zero,
unit and nilpotent scalars, the zero ring, and unbounded representatives. No second
agent was started, as required by this dispatch; independent review remains the
maintainer's responsibility.

Static repair checks: all three lean.statement strings occur verbatim in their files;
the new node cites exactly its stmt_deps; no delivered Lean line exceeds 100 columns.
All five extracted bodies and both original proof regions match the live source,
allowing only trailing whitespace and the required ownership docstrings/import.
Only the item theorem contains sorry; both definition and dependency modules have none.

## Delivery tool blocker

The repaired `deliver2.py --no-push` run compiled the three-file packet successfully
and reached server preflight, which rejected the preserved live proofs in the
required dependency module. Concrete diagnostic (repeated for its existing helpers):

`(c) lean/Sheaf/Algebra/Homology/InternalHomLocalizationComparison.lean
(lem-sfb-internal-hom-localization-comparison): theorem
CategoryTheory.localizationHom_unique: the proof is not sorry (stage 2 states;
every theorem and lemma ends with := by sorry or := sorry)`.

This is an unchanged proof from current main, not a new stage-2 proof. The same
check rejects localizationHom_unit, localizationModuleLeg_naturality,
localizationResolution_scalar, localizationRestrictedTensorIso_pure,
localizationRestrictionSheafification_unit, localizationRestriction_faithful,
localizationRestriction_full, localizationTensor_additive,
localizationUnderlyingComplexIso_unit, localizationUnderlyingDerivedIso_unit,
localizationUnderlyingIso_naturality, localizationUnderlyingIso_unit and
localizationUnderlying_scalar_isIso. The tool does not distinguish preserved proofs
in an existing §1(B) module from newly supplied proofs. Replacing these completed
live proofs with sorry would erase stage-3 work; keeping duplicate definitions or
omitting the requested dependency module would fail the independent return.
No launcher or project tool was edited or bypassed. Nothing was pushed.

A preceding explicit scompile attempt timed out on the dependency sandbox at 60 s
(its private overlay compiled in 46.6 s); the subsequent dry run passed its compile
stage and failed only at preflight. No timeout setting was changed.

## Saved-packet retry on 2026-10-22

Ran the required initial `deliver2.py Q97
lem-sfb-scalar-hom-telescope-evaluation --no-push` on the retained packet. All three
modules passed the compilation stage. Server preflight again exited 1 with
`PREFLIGHT FAILED, nothing pushed`, rejecting the existing completed proofs in
InternalHomLocalizationComparison, including CategoryTheory.localizationHom_unique:
`the proof is not sorry (stage 2 states; every theorem and lemma ends with
:= by sorry or := sorry)`.

Fresh self-check against the current shared source confirmed that all five moved
definition signatures and bodies match verbatim, no copy remains in the old module,
the private proof region matches, and the main theorem and completed proof match.
The dependency node differs from main only in lean; the item differs only in lean
and stmt_deps. Its theorem remains in proof_deps and the new definition owner is in
stmt_deps. All three recorded signatures occur literally in their modules, the new
node's citations match its dependency list, and every delivered Lean line is at most
100 characters. The sole sorry is still the item theorem. Re-read all five extracted
definitions and the full item signature, including the universal representative,
change-of-representatives and n=0 evaluation clauses; no further defect was found.

The gate failure persists after the authorized ownership extraction and preservation
of live proofs. No tool was edited or bypassed, no completed proof was erased, and
nothing was pushed. The packet is retained for a maintainer gate repair.

## Saved-packet retry, dispatcher attempt 3, 2026-10-22

Ran the prescribed initial deliver2.py --no-push on the retained packet. All three
modules compiled on the server. Preflight again failed with the same proof-not-sorry
diagnostic for fourteen pre-existing theorem helpers in the required dependency
module, starting with CategoryTheory.localizationHom_unique. Nothing was pushed.

Fresh comparison to the current shared source verified that each of the five moved
definition signatures and bodies is identical and absent from the old module. The
entire dependency proof-helper region and final theorem are identical, ignoring
trailing whitespace only. The dependency node changes only lean; the item changes
only lean and stmt_deps, retaining the theorem in proof_deps. All three recorded
signatures occur verbatim; all delivered Lean lines satisfy the width limit. The
only sorry remains scalarHom_telescope_evaluation. Read the extracted definitions
and item signature again; the return's ownership repair remains fully present.

The failed dry run supplies no packet defect to repair: it rejects unchanged live
proofs in the module that the return explicitly requires us to deliver. No script
was modified or bypassed, no completed proof was replaced by sorry, and the packet
is retained for a maintainer gate repair.


## Saved-packet retry, dispatcher attempt 4, 2026-10-22

Ran the prescribed initial deliver2.py --no-push on the retained packet. The tool
completed its three-module compilation stage, staged the seven delivery files,
and exited 1 with `PREFLIGHT FAILED, nothing pushed`. The concrete failure remains
fourteen existing proved helpers in InternalHomLocalizationComparison being
rejected as `the proof is not sorry`, beginning with localizationHom_unique.
There is no pending delivery invocation and no push was attempted.

Fresh comparisons against the current shared source confirm that the dependency
node changes only lean and the item changes only lean and stmt_deps. The five
extracted definition signatures and bodies match live source verbatim, and no
copy remains in the old module. Both the initial private proof-helper region and
the entire region from localizationRestrictedTensorPresheafIso through the final
theorem match live source, ignoring trailing whitespace only. All three recorded
signatures occur literally in their modules; every delivered Lean line is at most
100 characters. The sole sorry remains the item theorem.

Re-read the five definitions, new definition node, dependency module imports and
complete item signature. The new definition node owns exactly the five requested
notions; the item cites that owner in stmt_deps and retains the localization theorem
in proof_deps. The required ownership extraction is present without mathematical
changes or erased stage-3 proofs. The new definition module has real data throughout.
The repeated failure is in the stage-2 gate's treatment of preserved live proofs
in the required dependency module. No launcher or repository tool was modified or
bypassed. The repaired packet remains in the sandbox for a maintainer gate repair.


## Saved-packet retry, dispatcher attempt 5, 2026-10-22

Ran the prescribed initial `deliver2.py Q97
lem-sfb-scalar-hom-telescope-evaluation --no-push` on the saved packet. Its
three-file server compilation stage completed successfully. Server preflight then
exited 1 with `PREFLIGHT FAILED, nothing pushed`, rejecting fourteen unchanged
live proof helpers in the required dependency module as `the proof is not sorry`,
starting with `CategoryTheory.localizationHom_unique`.

Compared the saved packet to the current shared source again. The dependency node
changes only lean; the item changes only lean and stmt_deps. The new definition
owner is in stmt_deps, and the localization theorem remains in proof_deps. All
five extracted definition signatures and bodies occur verbatim in the live source
and are absent from the repaired theorem module. Its diff consists only of the
new public import, the five removed definitions and trailing whitespace; every
existing completed proof is preserved. All three lean.statement signatures occur
verbatim, all delivered Lean lines satisfy the 100-column limit, and the item's
main theorem remains the sole sorry. Read the five definitions again, including
the actual colimit.post map, common termwise lower bound, evaluation transpose
and normalized restricted comparison. The requested H2/H12 repair is retained.

The concrete diagnostic is the same gate failure as the previous retries, not a
new compiler or ownership defect. Replacing preserved completed proofs with sorry
would erase existing stage-3 work. No launcher or repository tool was modified
or bypassed, and no push was attempted. The repaired packet remains available
in this sandbox for the maintainer's gate repair.

## Saved-packet retry after provider interruption, 2026-10-22

The prescribed initial `deliver2.py Q97
lem-sfb-scalar-hom-telescope-evaluation --no-push` finished with exit code 1,
after successfully compiling all three Lean modules. Its final result was
`PREFLIGHT FAILED, nothing pushed`. No delivery invocation remains pending.
Preflight rejected fourteen unchanged live proof helpers in
InternalHomLocalizationComparison as `the proof is not sorry`, starting with
`CategoryTheory.localizationHom_unique`. No push was attempted.

Compared the retained repair with the current shared source using a direct
file diff, without running git in the read-only repository. The theorem module
diff contains only the new public import, removal of the five definitions and
trailing whitespace. Thus all completed proofs are unchanged. Each extracted
definition's signature and body matches the live source verbatim and is absent
from the repaired theorem module. The dependency node differs only in lean;
the item differs only in lean and stmt_deps. The new definition owner is in
stmt_deps, while the localization theorem is retained in proof_deps. All three
recorded signatures occur verbatim in their modules; all Lean lines meet the
100-column limit; the item's theorem remains the sole sorry.

Re-read the extracted definitions and complete item signature. The H2/H12
ownership repair requested in the immutable-head return is present. The
remaining concrete diagnostic is the stage-2 gate rejecting preserved live
proofs in the required dependency module. No tool was edited or bypassed and
no completed proof was erased. The packet is retained for a maintainer gate
repair; repeating a push cannot resolve this preflight refusal.


## Continuation verification after provider interruption, 2026-10-22

Checked for a pending Q97 scompile/deliver2 invocation before retrying; none
was running. The prescribed saved-packet dry run completed with exit code 1:
all three modules passed its server compile stage, then preflight reported
`PREFLIGHT FAILED, nothing pushed`. It again rejected fourteen unchanged
proved helpers in the required dependency module, starting with
`CategoryTheory.localizationHom_unique: the proof is not sorry`.

A fresh direct comparison with the current shared source confirms all five
extracted definition signatures and bodies are verbatim and absent from the
former module. All completed proof regions remain unchanged. The dependency
node changes only lean; the item changes only lean and stmt_deps. All three
recorded signatures occur verbatim, all Lean lines satisfy the width limit,
and the item's theorem is the sole sorry. The requested definition ownership
and proof dependency separation remain present. No push was attempted and no
tool was modified or bypassed. The remaining blocker is the stage-2 gate's
rejection of preserved live proofs in the expressly required dependency repair.

## Current saved-packet verification, 2026-10-22

The required initial saved-packet dry run compiled all three modules and exited 1
at server preflight: `PREFLIGHT FAILED, nothing pushed`. The fourteen diagnostics
again reject unchanged live theorem helpers in the required dependency module
as `the proof is not sorry`, starting with `CategoryTheory.localizationHom_unique`.

Fresh direct comparison against current shared source confirms the dependency
module changes only by the new public import, extraction of the five definitions,
and whitespace. Every completed proof is preserved. The dependency node changes
only lean; the item changes only lean and stmt_deps, citing the new definition
owner and keeping the localization theorem in proof_deps. All three signatures
are verbatim, all lines meet the width limit, and the item theorem is the sole
sorry. Re-read the five extracted definitions and the full item signature; the
requested H2/H12 repair remains present. No additional mathematical repair is
indicated by this diagnostic. No tool was edited or bypassed, no completed proof
was erased, and no push was attempted. The remaining failure is the stage-2
preflight gate rejecting preserved live proofs in the required dependency module.

## Latest interruption recovery check, 2026-10-22

No Q97 compile or delivery process was pending. The prescribed saved-packet
dry run compiled all three files, then exited 1 with `PREFLIGHT FAILED, nothing
pushed`, again rejecting fourteen preserved live proofs as `the proof is not sorry`.
The first named rejection is `CategoryTheory.localizationHom_unique`.

A direct diff against current shared source confirms that the dependency module
only gains the new public import and loses the five extracted definitions;
completed proofs are unchanged. Re-read the definition module and full item
signature. Rechecked node field deltas, definition ownership, the theorem's
retention in proof_deps, verbatim signatures, line lengths and the single item
sorry. All satisfy the requested repair. The remaining refusal is in the
stage-2 gate for the expressly required dependency extraction. No push was
attempted, no tool was modified or bypassed, and no existing proof was erased.

## Resumed dispatch verification, 2026-10-22

The initial saved-packet dry run completed before the interruption; its process
returned exit code 1, so no delivery invocation is pending or repeated. All three
modules passed server compilation. Preflight reported `PREFLIGHT FAILED, nothing
pushed` and rejected fourteen preserved proofs in the required dependency module,
beginning with `CategoryTheory.localizationHom_unique: the proof is not sorry`.

A fresh direct diff against current shared source confirms that the dependency
module changes only by importing the new definition owner, extracting the five
definitions, and trailing whitespace. All completed proofs are unchanged. The
dependency node changes only lean; the item changes only lean and stmt_deps.
The item cites the new definition owner instead of the theorem in stmt_deps,
and retains the theorem in proof_deps. All three recorded signatures occur
verbatim in their modules, all delivered Lean lines meet the width limit, and
the item theorem is the sole sorry. The requested ownership repair is present.

The remaining failure is the preflight gate rejecting unchanged live proofs in
the dependency module explicitly required by return L. No tool was edited or
bypassed, no completed proof was erased, and no push was attempted. The packet
is retained in this sandbox for the maintainer to repair the gate.

## Saved-packet dry run, current dispatch, 2026-10-22

The prescribed initial deliver2.py --no-push compiled all three modules, then
exited 1 with PREFLIGHT FAILED, nothing pushed. It rejected fourteen preserved
live proofs as “the proof is not sorry”, beginning with
CategoryTheory.localizationHom_unique. Direct file comparison confirms the
required dependency module only gains the new public import, loses the five
extracted definitions and changes trailing whitespace; all proofs are unchanged.
All five extracted signatures and bodies match live verbatim. Node field deltas,
verbatim lean.statement strings, line lengths and statement/proof dependency
ownership were checked again. The item theorem is the packet's sole sorry.
The requested repair is retained; the remaining refusal is the delivery gate's
handling of preserved proofs. No tool was edited or bypassed and nothing pushed.


## Saved-packet verification, latest dispatch, 2026-10-22

The prescribed initial dry run compiled all three modules, then exited 1 at
preflight with `PREFLIGHT FAILED, nothing pushed`. It rejected fourteen preserved
live proof helpers as `the proof is not sorry`, starting with
`CategoryTheory.localizationHom_unique`. A fresh direct diff confirms the required
dependency module changes only by the public import, extraction of the five
definitions, and whitespace; all existing proofs are unchanged. All five extracted
signatures and bodies match live source verbatim and have no remaining declaration
in the former module. The dependency node changes only lean; the item changes only
lean and stmt_deps. Its new definition owner is in stmt_deps and the theorem remains
in proof_deps. All three recorded signatures are verbatim, no Lean line exceeds
100 characters, and the item theorem remains the sole sorry.

Re-read the extracted definitions and item signature. The requested H2/H12 repair
is present. The remaining diagnostic is the delivery gate rejecting unchanged live
proofs in the expressly required dependency module. No tool was edited or bypassed,
no completed proof was erased, and no push was attempted.


## Saved-packet gate verification, 2026-10-22T12:54:37+00:00

Ran the prescribed initial deliver2.py --no-push. All three modules passed
server compilation; preflight exited 1 with PREFLIGHT FAILED, nothing pushed.
It rejected fourteen unchanged completed proof helpers in the required dependency
module as “the proof is not `sorry`”, beginning with
CategoryTheory.localizationHom_unique.

Direct diff against current shared source confirms that the dependency module
only adds the definition-owner import, extracts the five definitions, and changes
whitespace. Every completed proof is unchanged. The dependency node changes only
lean; the item changes only lean and stmt_deps. The item cites the new definition
owner and retains the theorem in proof_deps. All three recorded signatures are
verbatim, all Lean lines satisfy the width limit, and only the item theorem has
sorry. Re-read the extracted definitions and full item signature. The H2/H12
repair remains present. No tool was modified or bypassed and no push was attempted.
The remaining failure is the delivery gate rejecting preserved live proofs in
the expressly required dependency repair.

## Saved-packet retry, current dispatch, 2026-10-22

The prescribed initial deliver2.py --no-push compiled all three modules and
returned exit code 1 at preflight: PREFLIGHT FAILED, nothing pushed. It again
rejected fourteen unchanged live proof helpers as “the proof is not `sorry`”,
starting with CategoryTheory.localizationHom_unique. A direct diff confirms
that the dependency module only gains the new public import, loses the five
extracted definitions, and changes trailing whitespace; all completed proofs
are preserved. Re-read the extracted definitions and checked verbatim recorded
signatures, node field deltas, line widths, and statement/proof ownership. The
requested H2/H12 repair remains present. No tool was edited or bypassed, no
completed proof was replaced, and nothing was pushed. The remaining failure is
the stage-2 gate rejecting preserved proofs in the required dependency repair.

## Saved-packet check in this dispatch, 2026-10-22

The prescribed initial deliver2.py --no-push compiled all three modules, then
exited 1 with PREFLIGHT FAILED, nothing pushed. It rejects fourteen unchanged
live proofs in the required dependency module as “the proof is not `sorry`”,
starting with CategoryTheory.localizationHom_unique. Direct comparison against
current shared source confirms that the module only gains the new owner import,
loses the five extracted definitions, and changes whitespace; all proofs remain
unchanged. Re-read the five extracted definitions and full item signature. The
dependency node changes only lean; the item changes only lean and stmt_deps,
retaining the theorem in proof_deps. All three signatures are verbatim, all Lean
lines satisfy the width limit, and the item theorem is the only sorry. The
requested ownership repair remains intact. No tool was edited or bypassed and
no completed proof was erased. No push was attempted. The remaining failure is
the stage-2 preflight gate rejecting preserved live proofs in the explicitly
required dependency module.

## Saved-packet verification, 2026-10-22T13:22:28+00:00

The prescribed initial deliver2.py --no-push compiled all three modules,
then exited 1 with PREFLIGHT FAILED, nothing pushed. Preflight again rejects
fourteen unchanged live proof helpers in the required dependency module as
“the proof is not `sorry`”, beginning with CategoryTheory.localizationHom_unique.

Direct comparison with current shared source confirms the dependency module
only adds the definition-owner public import, extracts the five definitions,
and changes whitespace. All completed proofs are preserved. Verified all five
moved signatures and bodies verbatim, their absence from the former module,
all three recorded signatures, line widths and node field deltas. The item
cites the new definition owner in stmt_deps and keeps the theorem in proof_deps.
The item theorem remains the sole sorry. Re-read the extracted definitions
and complete item signature; the requested H2/H12 repair remains present.
No tool was modified or bypassed, no proof was erased, and no push was attempted.
The concrete remaining failure is the stage-2 gate rejecting preserved live
proofs in the dependency module expressly required by return L.

## Saved-packet validation, 2026-10-22T13:33:09+00:00

The prescribed dry run was retried on the retained packet and exited 1: PREFLIGHT FAILED, nothing pushed. The diagnostic rejects fourteen existing dependency-module proofs as “the proof is not `sorry`”, starting with CategoryTheory.localizationHom_unique. The complete diagnostic is retained in dry-run-current.log in the sandbox.

A separate prescribed scompile.py run of all three modules exited 0, including the private overlay, sandbox and library forms. Re-read the five extracted definitions and full item signature. Checked by direct source comparison that all five moved signatures and bodies are verbatim and absent from the former module; after the extraction and owner import, every remaining dependency-source token, including completed proofs, matches current shared source. The dependency node changes only lean; the item changes only lean and stmt_deps. It cites the new definition owner instead of the theorem in stmt_deps, retaining that theorem in proof_deps. All recorded signatures are verbatim, all Lean lines satisfy the width limit, and only the item theorem contains sorry.

The requested ownership repair remains complete. The remaining failure is the delivery gate rejecting unchanged live proofs in the required dependency module. No launcher tool was edited or bypassed, no completed proof was replaced, and no push was attempted.

## Saved-packet verification, 2026-10-22T13:41:40+00:00

The required initial deliver2.py --no-push completed its three-file server
compilation and exited 1 at preflight: PREFLIGHT FAILED, nothing pushed.
It rejects fourteen unchanged dependency proofs as “the proof is not `sorry`”,
starting with CategoryTheory.localizationHom_unique. Direct source diff confirms
that all completed proofs are preserved; changes comprise the owner import,
extraction of the five definitions, and whitespace. All five definition signatures
and bodies match live verbatim and are absent from the former module. Re-read
the extracted definitions and full item signature; checked node field deltas,
statement/proof dependency ownership, verbatim signatures and line widths. The
required H2/H12 repair is present. No proof was erased, no tool was modified or
bypassed, and no push was attempted. The remaining failure is the stage-2 gate
rejecting preserved live proofs in the required dependency repair.


## Saved-packet dry-run verification, 2026-10-22T13:47:58+00:00

The prescribed initial deliver2.py --no-push compiled all three modules, then
exited 1: PREFLIGHT FAILED, nothing pushed. Preflight rejects fourteen existing
completed dependency-module proofs as "the proof is not `sorry`", starting with
CategoryTheory.localizationHom_unique.

Direct diff against current shared source confirms the dependency module only
adds the new definition-owner public import, extracts the five definitions, and
changes whitespace. Every completed proof is unchanged. Re-read the new owner
module and full item signature. The dependency node changes only lean; the item
changes only lean and stmt_deps, cites the new definition owner, and retains the
localization theorem in proof_deps. All three recorded signatures occur verbatim,
no Lean line exceeds 100 columns, and the item theorem remains the sole sorry.
The required H2/H12 ownership repair is present. No new packet defect is indicated.
No proof was erased, no tool was modified or bypassed, and no push was attempted.
The remaining failure is the stage-2 gate rejecting preserved live proofs in the
explicitly required dependency repair.

## Saved-packet verification, 2026-10-22T14:05:20+00:00

The prescribed initial deliver2.py --no-push compiled all three modules, then
returned exit code 1 with PREFLIGHT FAILED, nothing pushed. Its fourteen
diagnostics reject existing completed dependency-module proofs as “the proof
is not `sorry`”, starting with CategoryTheory.localizationHom_unique.

A fresh direct diff against current shared source confirms that the dependency
module only gains the new public definition-owner import, loses the five extracted
definitions, and changes whitespace. Every completed proof is preserved. Re-read
the extracted definitions and full item signature; checked verbatim recorded
signatures, node field deltas, line widths and the sole item sorry. The item cites
the new definition owner in stmt_deps and retains the theorem in proof_deps.
The dependency node changes only lean, with the required ownership explanation.
The requested H2/H12 repair is present. No proof was erased, no tool was edited
or bypassed, and no push was attempted. The remaining refusal is the stage-2
gate rejecting preserved live proofs in the expressly required dependency repair.

## Saved-packet verification, 2026-10-22T14:14:07+00:00

The prescribed initial deliver2.py --no-push completed: all three modules passed
server compilation, then preflight exited 1 with PREFLIGHT FAILED, nothing pushed.
It rejects fourteen unchanged completed dependency proofs as “the proof is not
`sorry`”, beginning with CategoryTheory.localizationHom_unique. No invocation
was pending after the provider interruption, and no delivery was repeated.

Direct comparison against current shared source verifies all five extracted
definition signatures and bodies verbatim and their absence from the former
module. After removing the new owner import and these definitions, every
remaining dependency-source token, including all proofs, matches live source.
The dependency node changes only lean; the item changes only lean and stmt_deps.
It cites the new definition owner instead of the theorem in stmt_deps and retains
that theorem in proof_deps. All three signatures are verbatim, all Lean lines
satisfy the width limit, and the item theorem remains the sole sorry. Re-read
the extracted definitions and full item signature; the requested H2/H12 repair
is present. The failure is the gate rejecting preserved live proofs in the
required dependency extraction. No tool was modified or bypassed, no completed
proof was erased, and nothing was pushed.

## Resumed saved-packet verification, 2026-10-22T14:30:15+00:00

Checked the interrupted tool before repeating: its process result was no longer
available, and the saved dry-run log recorded PREFLIGHT FAILED, nothing pushed.
Repeated the prescribed deliver2.py --no-push. The private-overlay dependency
compile timed out, so the wrapper confirmed against current server sources and
advanced to preflight. Preflight exited 1, rejecting fourteen unchanged completed
dependency proofs as “the proof is not `sorry`”, starting with
CategoryTheory.localizationHom_unique. Nothing was pushed.

Fresh token comparison with current shared source verifies each of the five
extracted definitions has its exact original signature and body, is absent from
the former module, and every other dependency-module token (including all
completed proofs) is unchanged after accounting for the new owner import.
Re-read the new owner module and the full item module. Verified verbatim node
signatures, line widths, the sole item sorry, lean-only dependency-node change,
and lean/stmt_deps-only item change. The item cites the new definition owner
and retains the localization theorem only in proof_deps. The requested H2/H12
repair remains complete. No completed proof was erased and no tool was edited
or bypassed. The remaining failure is the stage-2 gate refusing preserved live
proofs in the explicitly required dependency extraction.

## Saved-packet server verification, 2026-10-23T04:28:08+00:00

The prescribed initial deliver2.py --no-push again exited 1 with PREFLIGHT FAILED,
nothing pushed. It rejects fourteen preserved live dependency proofs as “the proof
is not `sorry`”, beginning with CategoryTheory.localizationHom_unique.

A separate prescribed scompile.py run of all three delivery modules exited 0.
All private-overlay, sandbox and library checks passed without errors or warnings.
Fresh server source was fetched with scompile.py --source. Direct comparison
confirms the five definition signatures and bodies moved verbatim and are absent
from the theorem module; after removing their declarations and the added public
owner import, all remaining source tokens, including completed proofs, match the
server source. Re-read the definition owner and complete item module. Checked
verbatim node signatures, line widths, the sole item sorry, lean-only dependency
node delta, and lean/stmt_deps-only item delta. The new definition node owns all
five notions, the item cites it in stmt_deps, and the theorem remains in proof_deps.

The requested H2/H12 ownership repair remains complete. The remaining failure is
the stage-2 gate refusing unchanged completed proofs in the required dependency
extraction. No completed proof was erased, no tool was modified or bypassed,
and no push was attempted.


## Current saved-packet verification, 2026-10-23T04:46:40+00:00

Ran the required initial deliver2.py --no-push on the retained packet. It
exited 1 at preflight, rejecting fourteen existing completed dependency proofs
as “the proof is not `sorry`”, beginning with CategoryTheory.localizationHom_unique.
Nothing was pushed. A separate prescribed scompile.py run compiled all three
modules successfully, including their private-overlay, sandbox and library checks.

Fetched current server source with scompile.py --source. Verified all five
extracted definitions have verbatim signatures and bodies and are absent from
the dependency module; after removing the new owner import and those definitions,
all remaining source tokens match fresh server source. Re-read the new definition
module and full item module, and checked recorded signatures, line widths and
statement/proof dependency ownership. The H2/H12 repair is present. The dependency
node changes only lean; the item changes only lean and stmt_deps. The gate refusal
concerns preserved live proofs, not proofs introduced by this repair. No completed
proof was erased and no launcher tool was edited or bypassed.

## Saved-packet validation, 2026-10-23T05:02:11+00:00

The required initial deliver2.py --no-push completed and exited 1 at server
preflight: fourteen unchanged dependency proofs are rejected as “the proof is not
`sorry`”, beginning with CategoryTheory.localizationHom_unique. Nothing was pushed.
A separate prescribed scompile.py run of all three files exited 0: every overlay,
sandbox and library check passed without errors or unexpected warnings.

Fetched the current theorem module through scompile.py --source. Verified each
of the five extracted definition signatures and bodies verbatim, verified its
absence from the former module, and verified all remaining source tokens against
fresh server source after accounting for the new owner import. All completed
proofs are preserved. Re-read the owner module and complete item statement; checked
verbatim signatures, line widths, lean-only dependency-node changes and the
lean/stmt_deps-only item change. The item cites the new definition owner and keeps
the theorem in proof_deps. The requested H2/H12 ownership repair remains complete.

The remaining failure is the stage-2 gate refusing unchanged live proofs in the
required dependency module. Removing those proofs would erase completed stage-3
work; omitting the extraction would violate the return. No launcher tool was edited
or bypassed, and no proof was erased.


## Saved-packet verification, 2026-10-23T05:33:47+00:00

Ran the prescribed initial deliver2.py --no-push on the retained packet. It
exited 1 at server preflight with PREFLIGHT FAILED, nothing pushed, rejecting
fourteen preserved dependency proofs as “the proof is not `sorry`”, beginning
with CategoryTheory.localizationHom_unique. A separate prescribed scompile.py
run of all three modules exited 0: all private-overlay, sandbox and library
checks passed, without errors or unexpected warnings.

Fetched fresh server source using scompile.py --source. Verified all five moved
definitions have verbatim signatures and bodies and are absent from their former
module. After accounting for the owner import and extraction, every remaining
dependency-source token, including all completed proofs, matches server source.
Re-read the owner module and complete item statement. Verified verbatim recorded
signatures, line widths, node field boundaries and statement/proof ownership:
the item cites the new definition node in stmt_deps and retains the theorem in
proof_deps; the dependency node changes only lean. The H2/H12 repair remains
complete. The tool refusal concerns unchanged live proofs in the expressly
required dependency extraction. No proof was erased, no launcher tool was
edited or bypassed, and nothing was pushed.


## Resumed saved-packet verification, 2026-10-23T05:56:22+00:00

The prescribed initial deliver2.py --no-push finished with exit 1 at server
preflight, nothing pushed. It again rejects fourteen preserved live dependency
proofs as “the proof is not `sorry`”, starting with
CategoryTheory.localizationHom_unique. No delivery was repeated after an
interrupted mutation.

A separate prescribed scompile.py invocation reported successful private-overlay,
sandbox and library checks for all three modules, without compiler diagnostics.
Fresh server source was fetched through scompile.py --source. A token comparison
verified that all five extracted definition signatures and bodies are unchanged
and absent from their former module; after accounting for their extraction and
the new owner import, every remaining dependency token, including the completed
proofs, matches server source. Recorded signatures, node field boundaries and
100-column limits pass. Re-read the owner definitions and the full item module;
the requested H2/H12 ownership extraction remains complete.

The remaining blocker is the stage-2 preflight gate refusing unchanged completed
proofs in the explicitly required dependency-module extraction. No proof was
erased, no gate or launcher tool was modified or bypassed, and nothing was pushed.


## Saved-packet verification, 2026-10-23T06:00:10+00:00

The prescribed initial deliver2.py --no-push exited 1 at server preflight,
nothing pushed. It rejects fourteen preserved live dependency proofs as
“the proof is not `sorry`”, beginning with
CategoryTheory.localizationHom_unique. A separate prescribed scompile.py run
of all three modules exited 0 with no compiler diagnostics.

Fetched fresh server source with scompile.py --source. Verified the five
extracted definitions have verbatim signatures and bodies and are absent from
the former module. After accounting for extraction and the new public import,
all remaining source tokens, including completed proofs, match fresh server
source. Re-read the definition module and complete item statement. All recorded
signatures are verbatim and all Lean lines meet the 100-column limit. The
dependency node changes only lean; the item changes only lean and stmt_deps,
cites the new definition owner and retains the theorem in proof_deps. The
requested H2/H12 repair is present. The remaining failure is the stage-2 gate
refusing unchanged live proofs in the expressly required dependency extraction.
No completed proof was erased, no launcher tool was modified or bypassed,
and nothing was pushed.


## Saved-packet verification, 2026-10-23T06:17:07+00:00

Ran the prescribed initial deliver2.py --no-push on the retained packet. It
exited 1 at server preflight with PREFLIGHT FAILED, nothing pushed. The fourteen
diagnostics reject preserved live dependency proofs as “the proof is not
`sorry`”, beginning with CategoryTheory.localizationHom_unique. A separate
prescribed scompile.py invocation of all three modules exited 0; every private
overlay, sandbox and library check passed without compiler diagnostics.

Fetched current server source with scompile.py --source. Verified the five
extracted definitions have verbatim signatures and bodies and are absent from
the former module. After accounting for extraction and the new public import,
every remaining dependency-source token, including all completed proofs, matches
current server source. The read clone differs from that server source only in
trailing whitespace. Re-read the owner definitions and full item module. All
recorded signatures are verbatim, all lines meet the 100-column limit, and all
modules disable autoImplicit. The dependency node changes only lean; the item
changes only lean and stmt_deps, cites the definition owner and retains the
theorem in proof_deps. The requested H2/H12 ownership repair remains complete.

The remaining failure is the stage-2 gate refusing unchanged completed proofs
in the expressly required dependency-module extraction. No completed proof was
erased, no launcher tool was modified or bypassed, and nothing was pushed.


## Saved-packet verification, 2026-10-23T06:41:41+00:00

The prescribed initial deliver2.py --no-push exited 1 at server preflight:
fourteen preserved live dependency proofs are rejected as “the proof is not
`sorry`”, beginning with CategoryTheory.localizationHom_unique. Nothing was
pushed. A separate prescribed scompile.py run of all three modules exited 0;
all private-overlay, sandbox and library checks passed without diagnostics.

Fetched fresh server source using scompile.py --source. Verified verbatim
signatures and bodies for all five extracted definitions, their absence from
the former module, and every remaining source token after accounting for the
new owner import. All completed proofs are unchanged. Re-read the definition
owner and complete item module; verified recorded signatures, explicit universe
binders, line widths, node field boundaries and statement/proof ownership.
The requested H2/H12 repair remains present. The remaining failure is the
stage-2 gate rejecting preserved live proofs in the required dependency-module
extraction. No proof was erased, no launcher tool was modified or bypassed,
and nothing was pushed.


## Saved-packet verification, 2026-10-23T07:14:47+00:00

The prescribed initial deliver2.py --no-push exited 1 at server preflight,
nothing pushed. Fourteen preserved live dependency proofs are rejected as
“the proof is not `sorry`”, starting with CategoryTheory.localizationHom_unique.
A separate prescribed scompile.py invocation of all three modules exited 0;
all private-overlay, sandbox and library checks passed without diagnostics.

Fetched current server source through scompile.py --source. Verified verbatim
signatures and bodies of all five extracted definitions, their absence from the
former module, and preservation of every remaining dependency-source token after
accounting for the owner import. Re-read the owner module and full item signature.
Verified recorded signatures, explicit implicits, line widths, and node field
boundaries. The item cites the new definition owner in stmt_deps and keeps the
theorem in proof_deps; the dependency node changes only lean, with lean.note.
The requested H2/H12 extraction remains complete. The remaining failure is the
stage-2 gate rejecting unchanged completed proofs in the required dependency
module. No completed proof was erased, no launcher tool was edited or bypassed,
and nothing was pushed.


## Saved-packet verification, 2026-10-23T07:20:51+00:00

The required initial deliver2.py --no-push compiled the retained packet and
exited 1 at preflight, rejecting fourteen preserved live dependency proofs as
“the proof is not `sorry`”, starting with CategoryTheory.localizationHom_unique.
A separate scompile.py run compiled all three modules successfully, including
private-overlay, sandbox and library checks, without diagnostics.

Fetched fresh server source via scompile.py --source. Verified all five moved
definition signatures and bodies unchanged and absent from the former module.
Every remaining dependency-source token matches live source after accounting
for extraction and its public import; all completed proofs are preserved.
Re-read the owner definitions and full item statement; checked recorded
signatures, line widths, explicit implicits and node field boundaries. The
requested ownership repair remains complete. The remaining failure is the
stage-2 gate refusing preserved live proofs in the required extraction module.
No proof was erased, no launcher tool was modified or bypassed, and nothing
was pushed.


## Saved-packet verification, 2026-10-23T07:31:25+00:00

The required initial deliver2.py --no-push exited 1 at server preflight,
nothing pushed. It rejected fourteen preserved live dependency proofs as
“the proof is not `sorry`”, starting with CategoryTheory.localizationHom_unique.
The separate prescribed scompile.py invocation compiled all three modules
successfully, including private-overlay, sandbox and library checks, without
diagnostics.

Fetched fresh server source with scompile.py --source. Verified the exact
signatures and bodies of all five extracted definitions and their absence
from the former module. After accounting for the new public owner import and
the extraction, every remaining dependency-source token matches live source;
all completed proofs are preserved. Re-read the owner definitions and full
item statement. Checked verbatim recorded signatures, explicit implicits,
line widths and node field boundaries. The item cites the new definition
owner in stmt_deps and keeps the theorem in proof_deps. The dependency node
changes only lean, with the required note.

The requested H2/H12 repair remains complete. The tool refusal is stage-2
preflight applying its sorry-only gate to unchanged completed live proofs
in the expressly required dependency-module extraction. No completed proof
was erased, no launcher tool was edited or bypassed, and nothing was pushed.


## Saved-packet verification, 2026-10-23T07:50:03+00:00

The prescribed initial deliver2.py --no-push exited 1 at server preflight,
nothing pushed. Its fourteen diagnostics reject preserved live dependency proofs
as “the proof is not `sorry`”, starting with CategoryTheory.localizationHom_unique.
A separate prescribed scompile.py invocation compiled all three modules successfully,
including private-overlay, sandbox and library checks, without diagnostics.

Fetched fresh server source using scompile.py --source. Verified verbatim signatures
and bodies of all five moved definitions, their absence from the former module,
and equality of every remaining dependency-source token after accounting for the
new public import. All completed proofs are preserved. Re-read the owner module
and full item module; checked recorded signatures, explicit implicits, line widths,
node field boundaries and statement/proof ownership. The H2/H12 repair remains
complete. The remaining failure is preflight applying its sorry-only gate to
unchanged completed live proofs in the required dependency extraction. No proof
was erased, no launcher tool was edited or bypassed, and nothing was pushed.


## Saved-packet verification, 2026-10-23T08:09:59+00:00

The required initial deliver2.py --no-push rejected fourteen preserved live
dependency proofs as “the proof is not `sorry`”, beginning with
CategoryTheory.localizationHom_unique. Nothing was pushed. A separate prescribed
scompile.py invocation compiled all three files successfully, with every private
overlay, sandbox and library check clean.

Fetched current server source through scompile.py --source and compared the
required extraction: all five moved definitions retain their exact signatures
and bodies, are absent from the former module, and every remaining dependency
source token matches the current server after accounting for its new public
import. All completed proofs are preserved. Re-read the owner definitions and
full item statement; verified verbatim recorded signatures, explicit implicits,
line widths and node field boundaries. The item cites the new definition owner
in stmt_deps, retains the theorem in proof_deps, and the dependency node changes
only lean with its ownership-repair note. The H2/H12 repair remains complete.

The blocker is the stage-2 preflight tool applying its sorry-only check to
unchanged completed proofs in the required dependency extraction. No completed
proof was erased, no launcher tool was modified or bypassed, and nothing was
pushed.


## Saved-packet repair and successful validation, 2026-10-23

The initial prescribed dry run now reached the updated preflight and reported
only a missing `import_flags` key on the new definition node. Added
`import_flags: []`; no mathematical statement or Lean source changed. The next
deliver2.py --no-push passed preflight and compiled all three modules at
acad19284a0. This supersedes the historical sorry-only gate failures above.

Freshly fetched the current server comparison module through scompile.py
--source. Direct comparison confirms the dependency module differs only by
its new public owner import and extraction of the five definitions. All five
signatures and bodies are verbatim, and every remaining proof is unchanged.
Re-read the full item and owner modules; checked all recorded signatures,
explicit universes, autoImplicit false, and the 100-column limit. The item
changes only lean and stmt_deps, cites the definition owner, and retains the
comparison theorem in proof_deps. The dependency node changes only lean.
The requested H2/H12 ownership repair is complete. Updated the Lean record
dates to today's UTC date before final validation and delivery.

## Reviewer fix (maintainer review of c6be4156b8c2, 2026-10-23)

The mathematics and the ownership repair asked for at af979f5c9b0c are correct.
However, the landing index (tools/nt_parallel2.py with import_prune_check check 3)
does not drop names that a delivered module removes. Because of this, the
intra-delivery move of the five definitions into
`LocalizationHomComparisonData` would be refused with "declares names that other
modules already declare: ... also in InternalHomLocalizationComparison". Q14
2472d1bb was refused in exactly this way on 2026-10-22. The reviewer therefore
lands the same ownership by re-export, as was done for Q14 735d3bd0:

- `InternalHomLocalizationComparison.lean` is the published live text, byte for
  byte. The five definitions and the stage-3 proofs stay where they are.
- `LocalizationHomComparisonData.lean` (the module of
  def-sfb-localization-hom-comparison-data) has `public import` of that module. It
  re-exports the five definitions unchanged and adds one transparent `abbrev`,
  `HasLocalizationHomSequentialContinuity`. The abbrev is the node's primary
  declaration; the five names stay in its `declarations`.
- The item module and its record are unchanged. Its public import of the
  definition module still provides `HasLocalizationHomContinuity` and
  `localizationHomRestrictedComparison`. The item still cites the definition node,
  not the theorem node, in stmt_deps.
