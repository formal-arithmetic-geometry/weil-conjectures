## What changed

Reapplied the reviewed proof to the current restored source. The theorem
`AlgebraicGeometry.ProEtale.CondensedRing.condensed_wcontractible_lisse_evaluation`
retains its exact signature and has a complete combining proof.

Moved its thirty existing data declarations, with identical names, signatures,
attributes and bodies, into `Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel`.
The original module publicly re-exports them. This lets separate proof lemmas
refer to the actual canonical functors without importing the theorem that uses
them. A literal block comparison, apart from documentation blueprint labels,
verified the extraction. The change record is
`coord/changes/S1-condensed-lisse-evaluation-model.md`.

`Sheaf.AlgebraicGeometry.ContractibleLisseEvaluation` contains the fully written
categorical argument. It converts the explicit ring-duality criterion into
`IsDualizable`, proves the morphism bijection by transposition through both
triangle identities, restricts the adjunction, and constructs both inclusion
comparison isomorphisms. The source and target localization universes are kept
separate: the main module obtains the small sectionwise localization from the
proved Grothendieck module theorem before applying contractible evaluation.

`Sheaf.AlgebraicGeometry.CondensedComponentInverseImage` proves continuity,
strong braidedness, preservation of finite limits and preservation of finite
colimits for the fixed relative-test Lan/sheafification construction. It uses
the direct-image comparison and finite-limit clause of the declared relative
site theorem, representable flatness, and the explicit monoidal adjunction.
The remaining component lemma assumes these proved structures and asserts only
the coefficient and realization comparison data.

All seven Lean modules compile together through the remote single-file compiler
after reapplying the reviewed packet to the restored source. A fresh downstream
scan also includes `Sheaf.Paper.TAdmissibleDualizableTruncations` transitively;
its unchanged statement and definitions use the same public context.
The packet introduces no axiom, unsafe declaration, or holed definition.

## Proved and sorry left

The original file contained one hole, in
`AlgebraicGeometry.ProEtale.CondensedRing.condensed_wcontractible_lisse_evaluation`.
Its body is now complete. Its thirty data declarations are unchanged and contain
zero holes. Two further theorems have complete proofs:

- `AlgebraicGeometry.ProEtale.CondensedRing.contractible_lisse_evaluation`
  (`lem-zl-contractible-lisse-evaluation`), from the normalized adjunction and the
  existing perfect/dualizable criterion.
- `AlgebraicGeometry.ProEtale.CondensedRing.condensed_component_inverse_image`
  (`lem-zl-condensed-component-inverse-image`), from the existing relative-site
  theorem.

Three holes are added, each the complete body `by sorry` of a named public
source lemma in its own module:

- `AlgebraicGeometry.ProEtale.CondensedRing.Evaluation.contractible_realization_adjunction`
  (`lem-zl-contractible-realization-adjunction`): identify the fixed F and G with
  the derived module adjunction, prove its unit is invertible, and transport
  their strong tensor structures. This is the realization/unit part of HRS
  Lemma 4.1(1); it does not assert the perfect/lisse equivalence.
- `AlgebraicGeometry.ProEtale.CondensedRing.condensed_component_pullback_compatibility`
  (`lem-zl-condensed-component-pullback-compatibility`): the coefficient and scalar
  squares in HRS (4.1) and Proposition 4.3(3), assuming the independently proved
  continuity and exact braided inverse image.
- `AlgebraicGeometry.ProEtale.CondensedRing.condensed_profinite_scalar_compatibility`
  (`lem-zl-condensed-profinite-scalar-compatibility`): HRS Remark 3.2 on the
  profinite slice, without the unnecessary extremal disconnectedness hypothesis.

This is a decomposition: one original hole is replaced by three separate source
results, for a packet hole difference of -2 (one closed minus three added).
It is not a proof of the whole target with only the allowed axioms. The two
complete new theorems also use existing declared dependencies, including the
relative-site and ring-perfectness results. No existing dependency hole is
claimed closed. Each new hole has a source and a complete proof in words.

The new statements were checked mathematically on the empty profinite slice,
the empty affine scheme, and the zero coefficient ring. The balanced formulas
become zero comparisons and the module categories are trivial there. No
nonemptiness or nonzero hypothesis is introduced. The general adjunction lemma
retains the normalized monoidal evaluation hypothesis: exactness and colimit
preservation alone would not imply the required tensor assertion.

## No longer needed

No existing node or module is withdrawn or declared globally unnecessary. Both
restored parents still cite this item, and its original mathematical route
and all original proof dependencies remain reachable through the new nodes.
The unit record's realized statement and proof-step lists are empty; no fixed
unit route is bypassed.

The original module's direct proof imports of
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`,
`Sheaf.Paper.RingedTopoiDerivedPullback`,
`Mathlib.CategoryTheory.Functor.Derived.Adjunction`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Paper.CondensedPointBasisEvaluation`,
`Sheaf.AlgebraicGeometry.ProEtale.WContractibleClopenPartition`,
`Sheaf.Paper.KFlatRingedToposPullback`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
`Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`, and
`Sheaf.Paper.ConstantRealizationDerivedScalarExtension`
are removed there. They describe the remaining source lemmas' proof plans and
are recorded in those nodes; they are not needed to elaborate the current
combining proof. Unused private imports in the new holed modules were removed
for the same reason.

`Sheaf.CategoryTheory.DerivedCategory.RingDerivedDualizablePerfect` is now a
private proof import of `ContractibleLisseEvaluation`.
`Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor` needs no
additional direct proof import: the canonical model publicly exposes the
constant-realization interface used by its definitions. The thirteen original
public imports are retained in that model and publicly re-exported by the
restored item, preserving the original public context.

## Where the brief, the DAG or earlier work was wrong

The return from reviewer C-9b2e5 on head 9b2e5f6694 reports that the proof passed
review but could not land: the item had been restored after delivery base
38d3c220c by a813a49f8a. This repair reads the current restored source and
reapplies the extraction and combining proof to it. A literal comparison checks
all thirty data declarations against that source (only documentation blueprint
labels differ), and checks the theorem signature verbatim. The current node is
retained with only its proof-owned fields updated. Delivery is rebuilt on the
current sheaf-dag by deliver3.py. No mathematical statement in the brief or
original node was found false.

The original node's plan suppresses substantial normalization work: the
ringed-topos results supply derived adjunctions for specified presentations,
whereas F is a fixed composite of constant realization, a chosen universal
coefficient model, and an internal/sectionwise module equivalence, and G is the
fixed total right derived sections functor. The normalized contractible
adjunction lemma isolates exactly that missing identification and unit argument.
The sectionwise derived tensor theorem also uses localization universe u+1,
whereas the evaluation data fixes a standard u+2 sectionwise localization.
The new lemma states this transport explicitly; the combining proof obtains the
small localization without changing any existing data definition.

The component comparison needs the evaluation equivalence on both bases. The
complete categorical proof is therefore in a shared proof module, so the
component node can cite it without forming a dependency cycle through the
original theorem.

## New nodes

`def-zl-condensed-lisse-evaluation-model` owns the thirty unchanged canonical
data declarations extracted into `CondensedLisseEvaluationModel`.

`lem-zl-contractible-realization-adjunction` states the source realization,
invertible-unit and tensor-structure lemma in `ContractibleEvaluationAdjunction`.
It is one of the three remaining holes.

`lem-zl-contractible-lisse-evaluation` is the proved categorical argument in
`ContractibleLisseEvaluation`, from the normalized realization data to the
full perfect/lisse evaluation assertion.

`lem-zl-condensed-component-inverse-image` is the proved continuity, exactness
and strong symmetry theorem for the actual component inverse image in
`CondensedComponentInverseImage`.

`lem-zl-condensed-component-pullback-compatibility` states the remaining
coefficient, lisse and scalar squares in `CondensedComponentPullbackCompatibility`.
It does not repeat the separately proved inverse-image structure theorem.

`lem-zl-condensed-profinite-scalar-compatibility` states the independent scalar
associativity formula on the profinite slice in `CondensedProfiniteScalarCompatibility`.

The change record is `coord/changes/S1-condensed-lisse-evaluation-model.md`.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
