## Worker report

The module `Sheaf.Paper.RationalCompactSupportCoefficientCoherence` states
`AlgebraicGeometry.Scheme.rationalCompactSupportCoefficientCoherence` with `sorry`.
There are no proved theorems and no postponed data definitions. The source is the opening
scalar-extension paragraph of blueprint main-20261015,
`sec-six-functors-basics/sk-thm-sf-pf-field/thm-cbc-qbar.proof.md`, read together with the
completed-coefficient expansion in this DAG node. Stacks `sites-modules.tex`, Tag 0E8I,
was read as the supporting underived tensor identity, not as a completed coherence theorem.

The helpers in `Sheaf.Paper.NormalizedCoefficientFamilies` define the normalized
coefficient-family data used by this node:

* `cbcScalarCompactSupportInverse` is the actual inverse comparison on ambient objects:
  `push_F.map` of the canonical inverse open adjunction mate, followed by
  `pbcScalarDirectImageIso.inv.app (j!_E K)`. The first factor is the existing `mateEquiv` applied to the ordinary balancing
  comparison transported by the resolving counits, not an arbitrary invertible transformation. The second is the existing
  proper counit-tensor mate. No basis or arbitrary comparison is chosen.
* `CbcCompactSupportCoefficientFamily` packages the existence assertion for one of the
  two stated compact-support families. Its fields contain the existing raw-category
  functors and exact comparisons, their integral normalization and their equations.
  The type does not redefine an integral/rational category, an operation, or completion.

* `CbcCompletedPullCoefficientFamily` specializes the same raw-stage formulation
  to the actual datum completed pullback and fixes its comparison by ordinary
  balancing and the quotient completion unit. It does not introduce a new
  pullback functor or completion reflector.

Clause-by-clause rendering:

1. A prime ell is `(l : ℕ) [Fact l.Prime]`. The chosen algebraic closure is
   `(Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`.
   The coefficient stages are `Padic.FiniteCoefficientFields l Ω`. The published
   `pbcFiniteField.{u}` supplies the canonical small field model, so `w` is independent of
   the scheme universe `u`; no equality of these universes is imposed.
2. The four schemes and maps are `X' X Y' Y : Scheme.{u}`, `f`, `f'`, `g`, and `g'`.
   `c : Compactification f`, `c' : Compactification f'`, `gbar`, `properSquare`, and
   `openSquare` specify the chosen compactification and its Cartesian base change.
   These are the recorded interfaces, and allow any canonically identified presentation
   of the pullbacks. They express the given Cartesian compact-support square by pasting.
   A separate common-base S need not be chosen: the maps already form a square over Y,
   and extra S-structure does not enter any operation or equation here.
3. The four `IsNoetherian` instances give precisely the four Noetherian hypotheses.
   `dX`, `dY`, `dX'`, `dY'` are `Fact` wrappers for existence of a finite bound on
   `topologicalKrullDim`. `iX`, `iY`, `iX'`, `iY'` wrap invertibility of l at every stalk.
   These are data already stated in the node, not extra hypotheses.
   `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` expresses separated finite
   type. There is no restriction on `g`, no smoothness assumption and no base field.
   The pulled-back hypotheses on f' follow from the two supplied Cartesian squares.
4. The integral category is exactly `pbcIntegralStage l Ω W E`, hence the recorded
   `PbcBoundedConstructibleComplete W (pbcStageDatum l Ω E)`.
   `pbcStageCategory l Ω W E` is its recorded raw scalar localization at the specified
   uniformizer. No condensed category, new coefficient category, envelope or completion
   of that rationalization is substituted. The canonical small coefficient presentation
   uses the already published field equivalences, valuation rings and coefficient maps.
5. In `CbcCompactSupportCoefficientFamily`, `preserves` records that the actual ambient
   composite `cbcDerivedOpenShriek d c.i c.isOpenImmersion ⋙ d.push c.g` takes integral
   objects to integral objects. `localization` fixes `family.base.Φ E` by its entire
   composite with `pbcStageLocalization`: both the object map and integral morphism map
   are the actual compactification operations. The universal property of localization
   then fixes every fraction, hence every rational morphism. The same construction is
   used separately for c and c'. No preservation assumption is imposed on either
   intermediate compactification factor by itself.
6. `family : StageSystem.CoherentExactMorphism ...` supplies the actual natural
   isomorphisms `family.base.β h : H_E ⋙ T_Y h ≅ T_X h ⋙ H_L`. This is exactly the
   displayed orientation of b, using Lean's left-to-right functor-composition convention.
   `beta` explicitly characterizes their inverses on every integral
   object by the localization of `cbcScalarCompactSupportInverse`, conjugated by the
   specified integral/scalar comparisons. Thus these are the specified proper/open
   comparisons on the stated raw categories, not freely chosen isomorphisms.
7. `unit` is the heterogeneous equality with `Iso.refl (family.base.Φ E)` at repeated
   stages. This includes L=E and uses the literal identity normalization of the published
   scalar system. The exact-family fields give additivity, shift commutation, exactness,
   and `betaCommShift`. The additional `shift` field fixes H's shift comparison itself
   to the localization of the actual ambient `commShiftIso n`, for every integer n and
   every integral object; its two existential witnesses assert only subcategory membership.
   Thus a freely chosen exact shift structure cannot replace the specified one.
8. `family.base.coh h h' K` is precisely the successive-coefficient law. In Lean order
   it says `T_Y(h').map b_h ≫ b_h' ≫ H_N.map a_X = a_Y ≫ b_(h.trans h')`.
   Cancelling `a_Y` yields exactly the displayed equation of the node. The quantification
   includes all objects and permits repeated stages as well as strict inclusions.
9. `CbcCompletedPullCoefficientFamily l Ω g` (and the same for g') fixes the raw
   completed-pullback family on every integral object and map by `localization`.
   `comparison` is the ambient inverse of d; `completionUnit` prescribes it by the
   ordinary balancing comparison transported through `cbcDatumOrdinaryTransport`,
   and the actual `ordinaryToCompleted` unit. Completion's reflection property fixes
   this map uniquely. `beta` is the explicit conjugated localization equation fixing
   the inverse rational beta to that same comparison, including repeated fields.
10. The final theorem quantifies H, H', P, P' and then a
    `StageSystem.Morphism.Hom (H.family.base.comp P.family.base)
      (P'.family.base.comp H'.family.base)`.
    Thus U and V are literally the specified composites, rather than independently
    chosen functors identified with their endpoints. `StageSystem.Morphism.comp`
    defines its beta by whiskering the two constituent betas. Componentwise this is
    exactly `b^U = P_g,L(b^f) d^g` and `b^V = H_f',L(d^g') b^f'` in the node.
11. The final normalization equation identifies every exchange component with the
    localization of `completedCompactSupportExchange`, for every integral object,
    every generating tuple of the ideal and its completeness witness. Its two
    existential witnesses are only integral subcategory membership, not choices of
    maps. The arrow is the exact strict-tower proper factor followed by direct image
    of the exact completed open factor. No replacement by a finite-evaluation lift occurs.
12. `η : StageSystem.Morphism.Hom ...` contains the displayed `comm` equation on every
    raw rational object: `T_Y'(eta_E) ≫ b^V = b^U ≫ eta_L(T_X K)`.
    Reversing the sides is exactly the final equation in the node. There is no `IsIso`
    condition on the exchange and no descent conclusion. The later Qbar theorem and
    its module are not imported or used.

Dependency declarations used (their exact declarations and docstrings were inspected):

* Mathlib `FieldTheory.IsAlgClosed.Basic` / `AlgebraicClosure`: `IsAlgClosure`,
  `IsAlgClosed`, `AlgebraicClosure`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its public coefficient constructions.
* `WeilConjectures.Compactification.BaseChange`: `Compactification.baseChange`,
  `ofIsPullback`, the two base-change squares; the chosen squares use
  `ChosenCartesianSquare` and `OpenImmersionSquare`.
* `Sheaf.Paper.FiniteExtensionCompactSupportBaseChange`:
  `finiteExtension_compactSupportBaseChange`, `cbcCompactSupportSource`,
  `cbcCompactSupportTarget`, the recorded complete-category interfaces.
* `Sheaf.Paper.IntegralUniformCoefficient`: `pbcBoundedConstructibleComplete`,
  `pbcPadicCoefficientDatum`; canonical small stages use the published lifted
  `pbcIntegralDatum` presentation rather than copying these definitions.
* `Sheaf.Paper.PbcRationalCategory`: `PbcRationalDerivedCategory`, `PbcRationalCategory`,
  `pbcRationalization`.
* `Sheaf.Paper.PbcRationalTransport`: `ScalarLocalization.transport_exact`,
  `HasExactTransport`, `transportNat`.
* `Sheaf.Paper.ProjectionCompactification`: `proEtaleRingCompactSupportImage` and its
  termwise-derived extension by zero; the completed exchange's exact equivalent
  presentation is `cbcDerivedOpenShriek ⋙ d.push`.
* `Sheaf.Paper.PbcActualStrictPullback`: `pbcActualStrictCompletedPull`,
  `pbcActualStrictCompletedPullUnit`, `pbcActualCompletedPullback_tower`.
* `Sheaf.Paper.PbcScalarExtension`: `pbcScalarDirectImageIso`,
  `pbcScalarOrdinaryPullIso`, `pbcScalarCompletedPullIso`, `pbcConditionalIntegral`,
  and the specified scalar maps, units, associators and shifts.
* `Sheaf.Paper.CompletedCompactSupportExchange`: `completedCompactSupportExchange`.
* `Sheaf.CategoryTheory.RingedSliceExtensionTensor`:
  `SheafOfModules.ringedSlice_extension_tensor` (supporting open factor).
* `Sheaf.Paper.CompletedOpenExchangeTransport`: `cbcDatumOrdinaryTransport`, the
  resolving-counit-normalized identification with the datum's ordinary pullback;
  `cbcDerivedOpenAdjunction` is the exact open adjunction used by `mateEquiv`,
  imported directly from `Sheaf.Paper.CompleteCompactSupportProetale`.
* `Sheaf.Paper.PbcDescentFunctors` and published StageSystem modules:
  `StageSystem.CoherentExactMorphism`, `StageSystem.Morphism.coh`, `Morphism.Hom.comm`.
  The source of `WeilConjectures.CategoryTheory.StageSystem.Functor` was obtained with
  `scompile.py --source`, because it is absent in the old local source checkout.

All available recorded proof-dependency modules are imported as proof-only imports;
statement dependencies are public imports. The two proof nodes
`lem-sf-open-tensor-normalization` and `lem-sp-finite-free-direct-image-coherence` have
no Lean records at preparation and consequently have no import to add yet.
The repair note for this item is resolved stage 1, not a withdrawn stage-2 interface;
its instruction to keep the statement is observed. The entire current 16-step proof
is retained in the main theorem docstring.

The first compile exposed a timeout in the already existing scalar module; its server
confirmation reached `QbarCompactSupportBaseChange` and timed out there at 60 seconds.
I removed that downstream import and expressed the specialized compact-support mate
and its beta specifications directly with the smaller published APIs. No second
ordinary-pullback or open-scalar comparison definition is introduced: the new compact
comparison applies the actual `mateEquiv` expression as one factor in its own composite.
The final statement's U,V are literal `Morphism.comp` values, which also makes the two
composite comparison formulas definitional. There is no import cycle with the later
Qbar theorem.

Edge cases checked: equal coefficient fields (the unit condition and inverse specifications
explicitly include them); equal adjacent fields in a triple (coherence uses non-strict
inclusions); arbitrary ramification (uses normalized tensor/completion maps, no equality
of uniformizers); zero objects and zero maps; empty schemes (no nonemptiness assumption
on schemes); arbitrary g (no flatness or finite-type constraint); any presentation of the
pulled-back compactification; any integer shift, including zero and negative shifts;
independent algebraic-closure and scheme universes. The use of ambient factors does not
require the intermediate compactification scheme to be supplied as a new PBC endpoint.
No statement correction or disputed mathematical claim was needed.

Searches before writing:

* `msearch.py ... leanfinder "scalar extension coefficient natural isomorphism compact
  support base change rational derived category coherence"`: eight module scalar-extension
  associator hits, including `ModuleCat.extendScalars_assoc'`; no completed/rational
  compact-support exchange theorem.
* `msearch.py ... loogle "CategoryTheory.NatTrans.CommShift,
  CategoryTheory.isoWhiskerLeft, CategoryTheory.isoWhiskerRight"`: zero hits, unknown
  identifier `CategoryTheory.isoWhiskerLeft`; source inspection uses `Functor` namespace.
* `msearch.py ... grep "compactSupport.*[Ss]calar|[Ss]calar.*compactSupport|
  coefficient.*[Cc]oherence" CategoryTheory`: zero Mathlib hits.
* `msearch.py ... leansearch "scalar extension compatibility of compactly supported
  derived direct image and base change exchange natural transformation"`: eight hits
  on ordinary module change of rings, `IsBaseChange`, and Kan base change, no match.
* `rg` in `lean/Sheaf` for coherent scalar/compact-support names found
  `PbcScalarExtension`, `QbarCompactSupportBaseChange`, and the integral/rational
  compact-support value construction. Their signatures were read: the first lacks
  the open compact-support factor; the last imposes a base field and constructs values;
  the Qbar theorem concludes descent/invertibility and supplies only the reusable
  definition-level specifications for this task. None is this statement.
* `rg` in upstream `WeilConjectures` for the item id: no hit. Searches in Mathlib,
  upstream and side sources for the new declaration names: no hit.
* `tools/lean_names_upstream.py show` on the item: the index printed its census and no
  matching declaration for this item. No existing declaration states the entire node.

Validation: the initial combined file passed once in 59.5 seconds but exceeded the
60-second limit in the delivery dry run. The normalized data are now in their own
definition-node module, imported by the theorem module, so the two files compile
separately. The split passed `scompile.py`: definitions 57.9 seconds; theorem 11.5 seconds,
with no errors or unexpected warnings. Three theorem-only imports were then moved
from the definitions to the theorem module to reduce the definition-file import cost.
That cleanup exposed the owning import of `cbcDerivedOpenAdjunction`; the definitions
now import `CompleteCompactSupportProetale` directly. The adjunction and compact mate
are kept opaque to routine reduction, without changing their defining constructions.
The final delivery dry run returned OK at `383e78b2cf`: both files compile cleanly
within the fixed per-file limit and the complete packet passes the server preflight.

## Second reading by Q71

This is the author's separate rereading, not a claim that a second agent reviewed it.
The dispatcher explicitly requires direct worker delivery and prohibits starting agents;
the maintainer supplies the independent review.

I reopened the node and the entire Lean module and checked the correspondence above.
The first draft's exact-family package allowed a chosen H shift comparison. I added
`shift`, the explicit localization of the ambient `commShiftIso`, to retain the specified
shift normalization. The identity condition is explicit at every stage; iterated-field
coherence is the existing `Morphism.coh`, with its associators in the correct order.
The main theorem requests both separate H families as well as the transformation between the two literal composite families, so it does not silently replace b^f and b^f' with only b^U and b^V.
The inverse formulas have the open factor before the proper factor; inverting reverses
them and yields exactly `Rp_*(lambda) pi`. The literal `Morphism.comp` comparison
formulas insert the completed pullback in the stated respective positions. Finally,
the final normalization is the actual completed strict exchange and `Hom.comm` supplies its scalar
square without any invertibility hypothesis or conclusion. The later Qbar
base-change theorem and its module are not imported, called, selected, or used in a construction.


## New nodes

`def-cbc-normalized-coefficient-families` owns
`Sheaf.Paper.NormalizedCoefficientFamilies`. It defines the specialized family data
whose existence the item asserts: the actual compact-support mate composite, the
localization and shift normalization of H, and the ordinary-balancing/completion-unit
normalization of P. Its statement spells out each field; the clause mapping above
also applies to these definitions. It reuses `CoherentExactMorphism`, the scalar
system and all existing operations. It contains no theorem and no sorry. The source
is the same opening coefficient paragraph; it adds no assertion or hypothesis.
The item gains this one statement dependency; its mathematical statement stays intact.

Searches for the new data (also recorded in `mathlib_searches`): LeanSearch, normalized
coherent exact compact-support/completed-pullback families, gave 8 unrelated coherent-site
and normalization hits; LeanFinder, coherent exact scalar coefficient families normalized
by localization/completion units, gave 8 unrelated localization/perfectoid hits; Mathlib
grep for the two structure names and CoherentExactMorphism gave zero hits. Source and
side-library rg found no structure-name hit. DAG search found only unrelated twist,
purity, Kummer and trace families; blueprint search for coefficient family gave zero.
The existing generic `CoherentExactMorphism` and ambient scalar maps are used directly.

The author's second reading includes this new node and both split modules. The split
only moves declarations; the theorem signature and all normalization fields are unchanged.
