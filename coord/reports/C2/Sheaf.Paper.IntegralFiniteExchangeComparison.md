## What changed

The original signature of
`AlgebraicGeometry.ProEtale.CondensedRing.integralFiniteExchange_comparison`
is unchanged. Its proof now obtains the integral-to-residue Arrow comparison, proves
that ℓ vanishes in the residue quotient, obtains the residue-to-etale Arrow comparison,
and composes the two isomorphisms. Neither comparison assumes properness or a Cartesian
square. The unit `sk-thm-properbasechange` and every node in its `realized` record remain
unchanged.

Four supporting parts of the argument are fully implemented in new modules:

- `IntegralResiduePerfect.lean`: `integralResidue_isDualizable`. Pull the proved integral
  reduction short exact sequence to the scheme, identify both regular integral modules
  with tensor units, apply the proved derived short-exact dualizability lemma, and identify
  the third term using `mapModComapIso`.
- `IntegralReductionTensor.lean`: `integralReduction_restrictTensor`. Prove that the
  underlying tensor-presentation isomorphism is integral-linear, lift it to internal
  modules, construct the derived counit using exact restriction, and prove its left
  derived universal property by the K-flat criterion. The residue module need not be flat.

- `InternalModuleAbEquivalence.lean`: `CategoryTheory.internalModuleAb_equivalence`.
  Evaluate internal actions on pure tensors and construct ordinary module actions;
  construct internal actions by the integer-tensor universal property. Prove fullness,
  faithfulness and essential surjectivity. The resulting equivalence functor forgets
  definitionally to the original abelian groups and maps.

- `ConstantInternalModuleSheafEquivalence.lean`:
  `CategoryTheory.constantInternalModuleSheaf_equivalence`. Construct the pointwise
  presheaf encoding, lift the monoidal sheafification adjunction to modules, and use
  its invertible counit and unit on additive sheaves to prove the sheaf encoding is
  fully faithful and essentially surjective. Prove compatibility with forgetting to
  abelian sheaves by lifting the underlying presheaf identification.

The main proof supplies the coefficient results to `integralResidueExchange_comparison`
and the sheaf encoding to `finiteDiscreteExchange_comparison`. The pointwise encoding
is used inside the proved sheaf-encoding module.
The two remaining comparison statements occupy separate new modules. All five imports
needed only by the main proof are nonpublic. The old proof-only imports are removed.
The item's DAG proof now records this actual composition and these proved inputs.
No existing definition, public import, statement, visibility, or target was changed.

## Proved and sorry left

Closed the item's one direct hole:
`AlgebraicGeometry.ProEtale.CondensedRing.integralFiniteExchange_comparison`
(`lem-weil-pbc-integral-finite-exchange-comparison`). Its proof has no direct hole.

Also proved, with no holes in their modules:

- `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_isDualizable`
  (`lem-weil-pbc-integral-residue-perfect`).
- `AlgebraicGeometry.ProEtale.CondensedRing.integralReduction_restrictTensor`
  (`lem-weil-pbc-integral-reduction-tensor`), including its private linearity and K-flat
  helpers.
- `CategoryTheory.internalModuleAb_equivalence`
  (`lem-weil-pbc-internal-module-ab-equivalence`), including the proved private action,
  fullness, faithfulness and realization constructions.
- `CategoryTheory.constantInternalModuleSheaf_equivalence`
  (`lem-weil-pbc-constant-internal-module-sheaf-equivalence`), including the proved
  private presheaf equivalence, monoidal-module localization and sheaf descent helpers.

Added exactly two direct holes, each in its own public theorem with source, complete
proof in words, and a matching node:

- `AlgebraicGeometry.ProEtale.CondensedRing.integralResidueExchange_comparison`
  (`lem-weil-pbc-integral-residue-exchange`). What remains: bounded constructibility
  of the actual derived reduction; identify the supplied left-derived tensor model
  with the monoidal derived tensor; implement the finite-perfect projection comparison
  in the internal module categories; prove the units/counits/composition equations for
  the actual coefficient comparisons, and transport through the restricted bounded
  constructible adjunctions. Perfectness and the relative-tensor derived universal
  property are already proved and are explicit inputs, not new holes.
- `AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteExchange_comparison`
  (`lem-weil-pbc-finite-discrete-exchange-comparison`). What remains: the constant
  discrete condensed ring identification with the sheafified constant ring;
  transfer through the proved constant-ring sheaf encoding and transport the intrinsic
  bounded constructibility property to finite etale origin;
  compare the actual site adjunction mates for an arbitrary commutative square.
  The source library's D+ site comparison covers the derived site part. The full
  equivalence between internal modules over the sheafified constant ring and
  module-valued sheaves, including the underlying abelian sheaf comparison, is now
  proved here and supplied explicitly. The pointwise equivalence is its proved input.
  No action or descent theorem remains hidden in that supplied input.

This is a decomposition, not a full mathematical closure: one old direct hole is closed
and two lower holes are added (net −1 before the ledger's closure accounting). The four
new proved supporting lemmas add no holes. Existing transitive source holes have not
been hidden or counted as closed.

## No longer needed

Removed the main module's proof imports:

- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`, node
  `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. Its ringed-topos `SheafOfModules`
  comparison is not used by this route; the coefficient step is formulated directly for
  internal `CategoryTheory.Mod` objects. The main node no longer has this proof edge.
  Its exclusively reachable descendants can be pruned by the maintainer's queue.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`, node
  `prop-weil-pbc-site-comparison-finite-level`, as a direct import/dependency of the
  item. This node is still needed in the lower finite-discrete comparison plan and
  is not claimed globally unnecessary.

`lem-weil-pbc-finite-ring-constructible-derived-origin` is likewise moved from the main
node's direct proof dependencies to the finite-discrete comparison. It remains needed;
its missing Lean attachment is described below. The coefficient definition node remains
needed for the quotient calculation and coefficient instances. No unit-realizing module
is bypassed. The lower finite-comparison plan no longer uses
`Sheaf.AlgebraicGeometry.ModuleSheafConstantRingEquivalence`
(`lem-weil-pbc-module-sheaf-constant-ring-equivalence`): the new proved encoding
constructs internal constant-ring modules directly, without going through
`SheafOfModules`. This removes that proof edge from this new plan; it is not a claim
that the module has no other users. No Lean module is withdrawn, and no other global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original proof dependency
`lem-weil-pbc-finite-ring-constructible-derived-origin` has no Lean attachment, although
the standing brief says the queue holds back such modules. Its sheaf-level predecessor
has a declaration, but that declaration uses `SheafOfModules`, while the item uses
internal modules in abelian sheaves. The finite-discrete comparison records this
constant-ring identification and derived-origin step rather than pretending the
encodings agree definitionally. The generic internal constant-ring sheaf encoding
itself has now been proved in this delivery.

`RingedTopoiCanonicalTensorPullback` also uses the `SheafOfModules` encoding. It cannot
be applied directly to the item's internal module objects. The existing source
`ChangeOfCoefficients.derivedPullIso` and `derivedPushHom` require flat scalar extension.
The quotient O_E → O_E/ℓ is not flat. The proved finite-resolution and K-flat tensor
arguments address this issue without asserting flatness.

The source `ProEtale.BaseChange.SmoothBaseChange.comparison_derivedBaseChangeMap`
requires `IsPullback`; the item assumes only `CommSq`. It therefore does not settle the
needed arbitrary-square coherence. No Cartesian hypothesis has been added to the item
or either remaining comparison.

The implicit `EssentiallySmall Profinite` search recursed in early generic coefficient
signatures. An explicit local universe-sized instance `essentiallySmallSelf.{0} _`
resolves it; no heartbeat, time, or instance-search limit was raised. All delivered
modules are compiled with the normal settings. There is no tool workaround or adaptation
of another group's module.

Edge cases checked before stating the new lemmas: the coefficient lemmas work for an
empty scheme and do not need finite-dimensionality of E; the finite comparison allows
the zero ring and zero complexes; every exchange remains an arbitrary commutative-square
morphism, with no invertibility assertion. The two comparisons concern different steps:
one changes coefficients on the pro-etale site and the other changes the site for
already finite coefficients. Neither repeats the original combined conclusion.

## New nodes

`lem-weil-pbc-integral-residue-perfect` / `Sheaf.Paper.IntegralResiduePerfect` records the
proved dualizability input from the two-term integral reduction sequence and exact
inverse image. Source: Bhatt–Scholze, Lemma 6.5.9(3), perfect coefficient input.

`lem-weil-pbc-integral-reduction-tensor` / `Sheaf.Paper.IntegralReductionTensor` records
the proved internal relative-tensor presentation and its derived universal property.
The private constructions have actual terms; no data is selected from an unproved
existence statement. Source: the coefficient tensor construction and Lemma 6.5.9(3).

`lem-weil-pbc-integral-residue-exchange` / `Sheaf.Paper.IntegralResidueExchange` isolates
bounded constructible coefficient reduction and the coefficient-mate compatibility.
It takes the two proved inputs above explicitly and contains no etale realization.
Source: Bhatt–Scholze, Lemma 6.5.9(3), Proposition 6.8.11(3), and the expanded mate
argument in the docstring. Its remaining work is listed above.

`lem-weil-pbc-finite-discrete-exchange-comparison` /
`Sheaf.Paper.FiniteDiscreteExchangeComparison` isolates the finite discrete coefficient
realization and site-mate comparison. Source: Bhatt–Scholze, Proposition 5.3.2 and Lemmas
5.4.1 and 5.4.3; Stacks Tag 09AL. Its remaining work is listed above.

`lem-weil-pbc-internal-module-ab-equivalence` /
`Sheaf.Paper.InternalModuleAbEquivalence` records the proved equivalence between
internal R-modules in Ab and ordinary R-modules, with equality of the underlying
forgetful functors. Source: the tensor universal property, expanded by the worker
for the pointwise encoding in Section 5.3. Its inverse objects and morphisms are
constructed explicitly; there is no unproved existence or data choice.

`lem-weil-pbc-constant-internal-module-sheaf-equivalence` /
`Sheaf.Paper.ConstantInternalModuleSheafEquivalence` records the proved equivalence
between internal modules over the sheafified constant ring and module-valued sheaves,
with its underlying abelian sheaf comparison. Source: Section 5.3 and Stacks Tag 093I,
with the tensor and monoidal sheafification argument expanded by the worker. It uses
the proved Ab encoding and constructs the presheaf and sheaf functors explicitly.

All inherit the item's chapter and unit and the nearest blueprint ancestor
`nt-target-proetale-e`. Whole-blueprint and source searches found no duplicate with the
same internal-module statement. The generic pointwise equivalence also works for
noncommutative rings and the zero ring; the finite comparison uses its specialization
to ULift of the actual finite residue ring. Three kinds of Mathlib searches are recorded for each;
LeanSearch returned an internal server error and that unavailability is recorded without
a fabricated verdict. No change record is required: existing public interfaces are
unchanged.


## Second reading by C2

1. **Interfaces: pass.** Read all seven delivered modules and diffed the only existing
   module, `IntegralFiniteExchangeComparison.lean`, against the shared repository.
   Its declaration, namespace variables, docstring, public imports and visibility are
   byte-for-byte unchanged; only private proof imports and the proof body change.
   The existing node changes only `proof`, `proof_deps` and `proof_origin`.
   There are no changes to definitions or targets and no forced adaptations.

2. **Proofs and axioms: pass, with the two declared holes.** Compiled all seven modules
   in import order through `lcompile.py --all`, without errors or warnings. Read the
   pure-tensor module action, linearity, full-faithful and realization constructions;
   the sheafification module adjunction and its unit/counit argument; the lifted
   scalar-tensor isomorphism and K-flat derived counit; and the short-exact-sequence
   dualizability proof. Every object is constructed or obtained from a proved
   equivalence; no definition selects data from either unproved comparison theorem.
   A scratch axiom check of all seven public theorems gives only `propext`,
   `Classical.choice`, `Quot.sound` for the four completed supporting results, and
   these plus `sorryAx` for the main result and the two named comparison holes.
   A source scan finds exactly those two `sorry` occurrences, each the entire proof
   of its named public theorem, and no forbidden declarations or options.

3. **Split statements: pass as a decomposition.** The integral-residue statement
   supplies the actual reduced object with constructibility and compares the two
   coefficient exchange arrows. The finite-discrete statement starts with a residue
   object and compares its exchange with etale realization. Neither restates the
   combined target; composing their arrow isomorphisms is a real reduction.
   Read Bhatt--Scholze arXiv:1309.1198v2, Proposition 5.3.2, Lemmas 5.4.1 and 5.4.3,
   Lemma 6.5.9(3), Definition 6.8.10 and Proposition 6.8.11(3). These supply the
   bounded-below site comparison and perfect-coefficient reduction arguments.
   The remaining work includes matching the library's finite-presentation
   constructibility encoding to the source notions, as already exposed in the report;
   the completed encoding equivalence does not itself assert that match.
   Checked empty schemes, zero complexes, the zero finite ring, the identity square,
   and non-Cartesian commutative squares: no invertibility of exchange, flatness of
   the quotient, properness or Cartesian assumption is used. The two completed
   coefficient inputs do not require finite-dimensional E; the residue's finiteness
   in the main application does. Independent LeanFinder searches used the phrases
   "Projection formula for derived scalar extension by a perfect quotient and
   compatibility with adjunction base change mates" and "Bounded below derived
   etale to proetale realization commutes with direct image and base change for
   discrete coefficients". Their hits concern ordinary ModuleCat scalar adjunctions
   and algebraic etaleness, respectively, and do not close the holes. Also searched
   the shared Lean library for projection formulas, coefficient comparisons, internal
   module encodings and site exchange comparisons. The nearby `derivedPushHom` and
   `derivedPullIso` require exact scalar extension; the existing site exchange
   compatibility requires `IsPullback`. Neither applies here. No remaining hole is
   a few-minute application of an existing result.

4. **Route and pruning: pass after import cleanup.** The main proof first supplies
   the proved perfectness and tensor results, then the proved constant-ring sheaf
   encoding, and composes the two comparison isomorphisms. All its added imports
   are proof-only. Checked the old four `proof_deps`: the coefficient definition
   remains, the finite-origin and site-comparison edges move to the finite step,
   and the ringed-topos tensor edge is removed. `## No longer needed` accounts for
   all of them. Read `dag/units/sk-thm-properbasechange.json`; its statement and every
   `realized` step are untouched. There is no claim of a globally withdrawn module.

5. **Nodes: pass.** Opened every delivered node and compared its mathematical
   statement and proof steps with its Lean declaration and the construction used.
   Every recorded Lean statement is an exact substring of its module. Each
   `proof_deps` is exactly the union of step dependencies, all references exist,
   and the new nodes have sources, search records, creation records, blueprint
   ancestry, chapter, unit and Lean attachments. The main node records the actual
   composition rather than the former ringed-topos route. The proved Ab encoding
   feeds the proved sheaf encoding; perfectness and the derived tensor presentation
   are supplied explicitly to the coefficient step.

**Second-reader changes.** Removed two redundant proof imports from
`ConstantInternalModuleSheafEquivalence.lean`:
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod` is publicly imported by
`ModuleObjects.MapMod`, and `WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory`
is publicly imported by `Sites.Monoidal`. Recompiled that module successfully.
No statement, definition or proof term was changed. Added this independent review.
The delivery closes one original hole, adds two strictly lower holes, and proves four
supporting results without new holes; it is a decomposition, not a completed target proof.
