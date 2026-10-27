## Worker report

Q90 states `WeilConjectures.mixedReductionUnit_composition` in
`Sheaf.Paper.MixedReductionUnitComposition`. All theorem bodies are `sorry`.
Definitions have actual data. The item's statement and accepted proof plan are unchanged.
The whole-system helper declarations belong to the item module and are all listed
in its lean.declarations. Both dependency node files are byte-identical to live:
`def-weil-integral-reduction-tower` retains all ten Q28 declarations, including
`canonicalIntegralReductionTowerMap_naturality`; `def-weil-mixed-reduction-unit`
retains all six Q103 declarations. There are no dependency rebindings. One new
existing:true definition node records the published quotient constant constructions.
The maintainer performs the independent delivery review; no independent second
reading by a separate worker is claimed here.

Sources read: the assigned DAG statement and all seven proof steps; every statement
dependency's statement and recorded module; the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-sf-pf-reduction/lem-fix-operation-reduction.proof.md`,
first paragraph (K-flat tensor reassociation) and last paragraph (identities of the
specified maps, composition and units). The assigned older finite-field-independence
proof path is absent from the current blueprint; the current reduction proof gives
the explicit tensor/map normalization used here. The example CompactObject module
has been withdrawn and contains no declarations; its node and the live module-mode
conventions were read.

Hypotheses and objects, clause by clause:

- A prime ell: `(l : ℕ) [Fact l.Prime]`.
- A scheme W: `(W : Scheme.{t})`, with independent universe `t`.
- Finite coefficient fields A, M, N: `(A M N : Type u)`, their `Field`,
  `Algebra ℚ_[l]` and `FiniteDimensional ℚ_[l]` instances.
  `ι : A →ₐ[ℚ_[l]] M` and `j : M →ₐ[ℚ_[l]] N` present the nested
  inclusions invariantly; the direct inclusion is exactly `j.comp ι`.
  No distinctness or proper-extension hypothesis is present. Naming an ambient
  algebraic closure is unnecessary: the constructions depend only on these
  finite extensions and embeddings, and restriction to the given subfields
  recovers the literal inclusions.
- The rings R_(B,n) with exponent n+1 are the existing
  `integralCoefficientCommRingSheaf l B W n`, used in the actual ringed sequence
  site `coefficientSequenceCommRingSheaf`. Every `n : ℕ`, including zero, occurs
  inside the sequence site, instead of being separately quantified in the law.
- Coherent reduction r_B: `IntegralCoherentReduction.derived l B W`, ordinary
  derived change of rings from constant completed coefficients to the actual
  quotient sequence ring. It retains all horizontal maps. Its `ordinary`,
  `tensor` and `counit` declarations specify the strict representative and
  the universal reduction counit before any finite evaluation.
- Completed scalar extension C_(B/D): the recorded
  `integralScalarExtensionOfUniverses l D B inclusion W`, on the whole
  unbounded derived category and with its original strict-tower realization.
- The prescribed scalar associator and unitor: precisely
  `CompletedLineTensor.associator l A W M ι N j K hK` and
  `CompletedLineTensor.unit l A W K hK`. No line datum, arbitrary associator,
  completion-map inverse on complexes, or replacement identity functor is bound.
- A derived-complete K: `K : DerivedCategory (integralTowerModules l A W)` and
  `hK : IntegralOnSlice.IsComplete l A W none K`. The global `none` branch is
  definitionally the existing `IsDerivedCompleteUnrestricted` predicate.
- The exact mixed unit eta: `MixedCoherentReduction.completed` is the unique
  ordinary whole-system tensor unit, descended through its full universal
  counit square, followed by reduction/restriction of the existing
  `completedScalarComparison`. The latter is the prescribed quotient-cone map
  with zero shifted-product coordinate. The sheaf formula in
  `ordinary_existsUnique` is literally iota_n(s) tensor (1 tensor x), using
  the actual sheafification unit and the model's object-equality transport.

Conclusions, clause by clause:

- The first conjunct composes eta_(M/A) with scalar restriction of
  eta_(N/M) at C_(M/A)K. `MixedCoherentReduction.restrictComp` then identifies
  successive restrictions with direct restriction. Its ordinary identification
  is uniquely the identity on every section group, and its derived version is
  the standard exact-functor comparison. Finally it applies direct restriction
  to r_N of the recorded associator. The result equals exactly eta_(N/A).
  The written order is Lean's left-to-right categorical composition.
- The second conjunct is eta_(A/A), the canonical identity restriction
  identification `restrictUnit`, then coherent reduction of the recorded
  completed unitor. Its right side is `𝟙 _` on the coherent reduction of K.
- Both equalities are morphism equalities in the derived category of module
  sheaves on the entire vertical sequence site. Quantification over every
  complete K gives equality of the specified natural transformations on the
  complete subcategory; naturality comes from the already normalized derived
  natural transformation and the natural completion comparison. No statement
  detects derived-system equality by evaluations or by cohomology.
- All quotient transitions are part of that source and target category. The
  normalized completion comparison is used as an actual term, so its
  augmentation and zero shifted coordinate are retained, not existentially
  chosen. Applying the fixed strict-tower/homotopy and derived-limit realization
  functors to these identities preserves them, including both Roos coordinates.
  This is the functorial-retention assertion in the node, rather than an
  assertion that arbitrary chosen representatives are equal as chain maps.
- There is no flatness assumption on quotient homomorphisms, no Tor-amplitude
  assumption on K, no boundedness, no invertibility-of-ell assumption on W,
  and no chain inverse for any completion comparison.

Dependency declarations read and used:

- `Sheaf.Paper.IntegralReductionTowerCanonical`:
  `canonicalIntegralReductionTower`, `canonicalIntegralReductionTowerMap`,
  `canonicalIntegralReductionTowerCone`, and the publicly retained
  `unrestrictedIntegralReductionFunctor`, `unrestrictedIntegralTensorSection`,
  `unrestrictedTowerComplex`, `unrestrictedTowerUnit`, `unrestrictedTowerTransition`.
  These published declarations and their ownership remain unchanged. The item
  module constructs the coherent ringed-sequence realization from the recorded
  sequence-site and generic scalar models.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `integralScalarExtensionOfUniverses` and its normalized representative comparison.
  `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `completedCoefficientMap`, `completedOrdinaryScalarExtension`,
  `completedScalarTensorSection`, `completedDerivedScalarExtension`,
  `completedScalarCounit`, `completedScalarComparison` and its Roos normalization.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`; its global
  branch is the existing augmented Roos-triangle condition.
- `Sheaf.Paper.MixedReductionUnit`: `sfMixedReductionUnit_existsUnique`,
  `sfMixedReductionUnitHomotopy`, `sfMixedReductionDerivedUnit_existsUnique`,
  `sfMixedReductionDerivedUnit`, `sfMixedCompletedReductionUnit`.
  Their full signatures/docstrings were read. The item imports that module,
  preserves its owning node, and supplies the whole-system helpers needed to state
  this composition theorem with independent universes.
- `Sheaf.Paper.CompletedLineTensorCoherence`:
  `AssociatorData`, `IsAssociatorNormalized`, `associatorData`, `chi`,
  `associator`, `ordinaryUnit`, `unit`, and `extension_complete`.
  The actual scalar associator and unit are independent of auxiliary lines.
- Existing generic mechanisms reused: `SemilinearSections.quotientConstantRing`,
  `quotientConstant`, `res`, and `SheafOfModules.DerivedChangeOfRingsCochainModel`
  with `nonempty_derivedChangeOfRingsCochainModel`. Its object/map formulas,
  universal counit and K-flat computation determine the pair up to its unique
  comparison-preserving isomorphism. This is not a bare choice of an arbitrary
  morphism or object. Every comparison used in the laws remains normalized.
- All recorded proof modules are imported privately: semilinear derived sections,
  ringed K-flat word comparison descent, sheaf-ring derived coefficient adjunction,
  successive derived quotient normalization, quotient scalar comparison descent,
  finite-free completion comparison, strict Roos homotopy functor, exact pro-etale
  countable products and strict Roos comparison. The mathlib-match dependency
  `lem-weil-pbc-mate-pasting` is imported via `Mathlib.CategoryTheory.Adjunction.Mates`;
  `mateEquiv_vcomp`, `mateEquiv_hcomp` and `conjugateEquiv_id` were read.

Edge cases checked mathematically before writing: n=0 is the quotient by the
first power and is present as the first sequence object; W empty and K=0 introduce
no missing hypotheses; A=M=N and either single adjacent equality are admitted by
identity algebra homomorphisms; the completed identity extension is compared by
`CompletedLineTensor.unit` and is not replaced by strict identity. A ramified
extension can give a nonflat same-index quotient map; ordinary derived reduction
and its K-flat universal counits still define all terms. Arbitrarily unbounded
complete K are included. Separate `t,u` avoid imposing equality of the small site's
object/morphism universe with the field universe.

Searches actually run through the prescribed msearch wrapper:

- LeanFinder: `Mixed derived reduction tensor units compose for completed scalar
  extensions on entire coherent quotient towers`. Eight hits, including
  `ModuleCat.extendScalarsComp_hom_app_one_tmul`, adic-completion tensor lemmas
  and cotangent-space comparisons. None is the whole derived quotient-system
  identity for the specified completed mixed unit.
- Loogle: `CategoryTheory.Adjunction.comp_unit_app`. One hit, the generic
  composite-adjunction unit formula; it does not state the completed mixed law.
- Mathlib grep: `mixedReduction|mixed.*[Uu]nit|comp_unit_app`, subdirectory
  `CategoryTheory`. Twelve hits, generic adjunction/mates, site, shift and
  Day-convolution formulas, with no completed mixed reduction declaration.
- LeanSearch: `Mixed reduction units for completed scalar extension compose as
  natural transformations on quotient diagrams`. Eight hits, including
  `ModuleCat.extendScalars_id_comp`, `QuotSMulTop.map_comp`,
  `CategoryTheory.Quotient.natTrans_ext`, `CategoryTheory.TwoSquare.natTrans`,
  `ModuleCat.restrictScalarsComp'App_hom_naturality` and ordinary extension units.
  None states this item.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for mixed units and coherent
  reduction found the recorded finite-level MixedReductionUnit, the generic
  semilinear sequence framework and the coherent extension *counit* in
  CoefficientExtensionReductionModel. The latter is a different arrow and a
  different comparison, not the prescribed mixed unit law. Existing generic
  quotient constants and scalar models are reused here.
- `grep -rn lem-weil-mixed-reduction-unit-composition lean/WeilConjectures`
  and searches of `dag/lean_names_upstream.json` found no owning declaration.
  Searches for the new namespaces and main declaration in both live Lean roots
  and that index found no conflicting declarations.

## Returned delivery repair

The returned immutable head c26eb628b66f incorrectly rebound two established dependency
records and introduced a cycle. This repair removes both rebindings completely:

- `def-weil-integral-reduction-tower.json` is copied byte for byte from current live
  main. Its Q28 existing:true record, all ten declaration names and its stage-3-proved
  naturality declaration are preserved.
- `def-weil-mixed-reduction-unit.json` is copied byte for byte from current live main.
  Its Q103 record and all six declaration names are preserved.
- `IntegralCoherentReduction` and `MixedCoherentReduction` now live inside
  `Sheaf.Paper.MixedReductionUnitComposition`. The two former helper modules are
  removed from the delivery. Every helper's blueprint docstring names the item,
  and every helper is listed in the item's lean.declarations. Their definitions,
  normalizations, existence statements and the two final laws are unchanged.
- The item adds the actual recorded owners to stmt_deps:
  `def-coef-ringed-sequence-site` (`Sheaf.Paper.CoefficientRingedSequenceSite`,
  `coefficientSequenceCommRingSheaf`, `coefficientSequenceModules`);
  `def-pur-quotient-constant-system` (`Sheaf.Paper.QuotientSystemFlatModels`,
  `SemilinearSections.quotientConstantRing`, `quotientConstant`);
  `lem-pur-derived-change-of-rings` (`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`,
  publicly retaining `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence);
  `def-coef-semilinear-system-models` (`Sheaf.Paper.SemilinearSystemModels`,
  `SemilinearSections.res`);
  `def-trf-completed-scalar-identity-unit`
  (`Sheaf.Paper.FiniteFreeCompletedScalarComparison`, `completedScalarComparison`
  and its ordinary functor, tensor sections and counit). The already-listed
  `def-weil-integral-scalar-extension` remains a direct dependency through
  `Sheaf.Paper.IntegralScalarExtensionUniverses`.

The dependency records no longer import downstream sequence-site or scalar-comparison
owners. All additional edges run from this theorem to those owners. A read-only
traversal of statement/proof dependencies checks that no added owner reaches this item.
The review's item-statement approval is respected: no mathematical statement,
proof plan or hypothesis was changed. The universal model choice is the existing
counit-normalized model; the laws use its normalization and do not depend on that choice.

Validation: scompile.py compiled the consolidated module cleanly in both sandbox
and library modes against the live server build (22.1 s and 16.1 s). The only
postponed proofs are the six named normalization/existence helpers and the item
theorem; all definitions have actual data. The dependency traversal found no
path back to the item from any statement dependency. The prescribed deliver2.py
--no-push dry run passed preflight and both delivery compile checks (704732540cf).
Its staged set contains only this report, the item node and the consolidated
item module; neither restored dependency node has a diff from live main.
No statement correction or STATEMENT-DISPUTED issue was needed.


## New nodes

`def-pur-quotient-constant-system` is an existing:true definition node for
`WeilConjectures.SemilinearSections.quotientConstantRing` and `quotientConstant`
in the already published `Sheaf.Paper.QuotientSystemFlatModels`. It adds no Lean
module or construction. Its definition-only stmt_deps are
`def-weil-pbc-sites-and-cohomology`, `def-coef-ringed-sequence-site`,
`def-weil-sheaf-of-modules-category`, and `def-coef-semilinear-system-models`.
The statement introduces the three independent universes, essential smallness,
the site and ring, the projection, its constant ring, and its module functor,
including the action, all vertical and horizontal restrictions, and map components.
These match the existing definitions' full signatures and bodies. Their generic
Mathlib construction is continuous precomposition; the module functor uses the
identity coefficient identification. The source is Zheng Construction 4.1, read
in the local PDF: the inverse image from the inverse-sequence topos is constant
of the given value, before its tensor change to the varying ring.

The prescribed searches were run afresh: LeanSearch query `The constant sequence
ring sheaf and constant module system on the vertical sequence site are
precomposition with the projection` returned eight generic constant-sheaf results;
Loogle query `CategoryTheory.Functor.sheafPushforwardContinuous` returned twelve
continuous-precomposition results; Mathlib grep query
`quotientConstantRing|quotientConstant|sheafPushforwardContinuous` in
`CategoryTheory/Sites` returned twenty-five generic occurrences. The exact existing
specializations were found by rg only in `lean/Sheaf/Paper/QuotientSystemFlatModels.lean`,
with none in `lean/WeilConjectures`. `grep -rl`/rg in dag/nodes found the two exact
names recorded only by the enclosing flat-model theorem, not by any definition
node. `blueprint_refs.py search 'constant sequence'` returned zero blueprint nodes.
The search log and new node preserve the actual tool queries and results.

## Returned delivery baefca2c503e repair

1. Replace the item's statement dependency
   `lem-weil-finite-free-completed-scalar-comparison` by the existing definition
   owner `def-trf-completed-scalar-identity-unit`, exactly as directed. The used
   `completedOrdinaryScalarExtension`, `completedScalarTensorSection`,
   `completedDerivedScalarExtension`, `completedScalarCounit`,
   `completedOrdinaryScalarComplex`, and `completedScalarComparison` are plain
   definitions from its module. The finite-free theorem is still a proof
   dependency, where its invertibility/completeness conclusion is actually used;
   the node's accepted proof plan is unchanged.
2. Replace the item's statement dependency `lem-pur-quotient-system-flat-models`
   by new existing:true `def-pur-quotient-constant-system`, described above.
   This definition node has only definition nodes in stmt_deps, and records both
   existing declarations without duplicating them or modifying their module.
3. Retain `lem-pur-derived-change-of-rings`: the helper `model` explicitly uses
   `nonempty_derivedChangeOfRingsCochainModel.some`, so its theorem conclusion,
   rather than just a plain definition in its module, is needed in the statement.

The item module is byte-identical to baefca2c503e (SHA256
0275366b97d6d0078619c7ea04258abca7308e6c571527646983ae8e1330b957).
All existing dependency records are unchanged from live main. The prior repair's
ownership and cycle corrections remain intact. The item changes only lean and
stmt_deps relative to live; its mathematics, both laws, all seven sorry bodies,
and all definitions are unchanged. Fresh scompile.py validation passed in sandbox
and library modes (22.1 s and 16.1 s). The prescribed deliver2.py --no-push dry
run passed preflight and per-file compilation at 68e78e3f382. Its staged set has
only the item module, item node, new existing:true definition node, and this report.
Neither restored dependency record has a diff from live. The earlier validation
above is historical.

## Second reading by Q90

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
