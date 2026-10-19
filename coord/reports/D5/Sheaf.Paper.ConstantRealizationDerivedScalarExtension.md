## What changed

In `Sheaf.Paper.ConstantRealizationDerivedScalarExtension`, proved the two ordinary
comparison theorems without changing any existing signature or definition.

`restrictionIso_existsUnique` now uses a general commuting square of coefficient
presheaves and ring sheaves. Separatedness and locally lifted sections identify the
two scalar actions on the common underlying abelian sheaf. The resulting identity
maps give the restriction/sheafification isomorphism; the abelian sheafification
adjunction proves uniqueness from the prescribed values on constant sections.

`moduleComparison_tensor` now constructs an inverse through the module tensor
adjunction followed by the module sheafification adjunction. Its values on constant
unit tensors identify both composites with identities. Linearity gives the stated
formula for an arbitrary scalar. Private helpers and local facts are proved and
used only in proofs.
The ordinary argument works on an empty site, for a zero ring, and for a nonflat
coefficient map: no injectivity, faithfulness, terminal object, or flatness is assumed.

Updated Step 4 of the existing node to record this route. The scalar-lift
constructions are locally irreducible after their computation lemmas. Three
auxiliary facts are local to their proofs. This version compiled with the full
delivery axiom probe in 27.8 seconds and checked all 44 public declarations.
Earlier delivery probes intermittently exceeded the 60-second limit. No
nonstandard axiom was reported; the two remaining direct holes are the original
derived theorems. Direct axiom printing also verified that `restrictionIso_existsUnique`
uses only `propext`, `Classical.choice` and `Quot.sound`.

The proof-scope change record is
`coord/changes/D5-constant-realization-proof-scope.md`.

## Proved and sorry left

Closed two of the four original holes, with no holes added:

- `CategoryTheory.ConstantScalarRealization.restrictionIso_existsUnique`.
- `CategoryTheory.ConstantScalarRealization.moduleComparison_tensor`.

Two original holes remain unchanged, both attached to
`lem-sfb-constant-realization-derived-scalar-extension`:

- `CategoryTheory.ConstantScalarRealization.constantRealizationDerivedScalarExtension`.
- `CategoryTheory.ConstantScalarRealization.constantRealizationDerivedScalarExtension_transitivity`.

This is a partial proof delivery, not a decomposition. All newly added private
helpers are proved, and there are no new modules, axioms, or holed definitions.

## No longer needed

Removed the proof import
`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor` and its
node dependency/tool-use entry `lem-pc-sites-module-sheafification-tensor`.
The ordinary tensor comparison is proved directly by tensor and sheafification
adjunctions, so that separate tensor-sheafification comparison is unnecessary for
this route. Existing dependencies for the two unproved derived clauses remain;
their K-flat preservation, representative computation and composition arguments
are not claimed proved or pruned. Removed unused proof imports of the following
modules, which are not needed by the implemented proofs (their nodes remain in the
plans of the two original derived holes):

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`.
- `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral`.
- `Sheaf.Paper.KFlatRingedToposPullback`.


## Where the brief, the DAG or earlier work was wrong

The earlier unverified scalar-lift candidate failed because Lean inferred the
restricted R-action where the section needed its original S-action. Explicitly
typing the target module and composing the coefficient naturality equality avoids
that inference and the expensive congruence search. The tensor formula likewise
needs the section's target type made explicit before simplifying pure tensors.

A temporary exploratory ordinary composition helper was removed; it is not part
of the delivered proof. Earlier service failures did not verify any candidate and
no prior delivery was pushed. The two remaining derived theorems still need their
full K-flat representative and localization arguments.

The dispatcher reset the reference clock on continuation: the preserved earlier
start was `1792425878.985005`; the current start is `1792434085.4858305`. These
are continuation attempts of D5 on the same item after provider interruptions.
The worker did not edit the budget file.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
