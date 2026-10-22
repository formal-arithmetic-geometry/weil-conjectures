## What changed

The item's public statements and definitions retain their original signatures and data.
The coefficient map still comes from its uniquely normalized limit property. The chain
augmentation, multiplication and identity-unit proofs present in the snapshot copied at
claim time are retained; the shared source subsequently displayed those holes again.
The packet does not claim their original discovery. The new descent proof uses full
faithfulness of whiskering with the existing good-complex localization. A generic
homotopy-counit construction avoids elaborating a concrete category's naturality equation.
The cochain model is built from the generic derived-change-of-rings witness before
specialization, avoiding repeated expansion of its concrete chosen fields.

`CompletedIntegralFiniteFree` proves the arithmetic coefficient clause: construct the
integral basis, prove positive ramification, identify lifted quotient towers, apply the
existing adic basis-limit theorem, and transport the basis to the uniquely prescribed
completed scalar map. The main proof combines this calculation with the existing
finite-free completion exchange core. It identifies the resulting unit with the specified
comparison using localization uniqueness, and obtains target completeness from the same
one-field unit criterion. The identity formula is proved from the chain augmentation's
specified product and shifted-product coordinates.

Two separate source results are stated in new modules: a one-field completion-unit
criterion and a balanced actual-tower comparison. They are strictly separate parts of
the argument. The former contains no extension of coefficient fields. The latter has
neither a finite-free nor a completeness hypothesis and makes no assertion that its unit
is invertible. The proof combining them is real Lean in the item. Their docstrings give
the complete remaining proofs, including transport of quotient maps, cone coordinates,
and universal counits, rather than just objectwise isomorphisms.

The exchange uses its existing proved `exchangeFromCochains` core, the normalized
principal-model existence theorem and the finite-free quotient Roos comparison directly.
Its wrapper carries an unused exact-product hypothesis on abelian sheaves; no such
instance or monicity proof is needed by the core. Exact products for the two module
categories follow directly from `ProEt.products_exact`. All existing declarations
remain intact.

The zero complex, identity inclusion and empty scheme are included. No boundedness or
constructibility hypothesis is added. Only new modules, the item's proofs, its proof-route
record, three new node records and the proof-elaboration change record are changed;
there are no consumer adaptations,
source-library edits, public definition repairs or target changes.

Validation: all four modules compile through lcompile.py. The fully assembled item
compiled in 54.2 seconds; the arithmetic module took 12.0 seconds, and the two new statement
modules took 0.2 and 9.2 seconds. The first preflight axiom probe hit its 60-second limit
and will be retried by delivery and merge. An audit confirms that all 20 original public
statement texts and definition bodies are unchanged.

## Proved and sorry left

The current shared item has five theorem holes. This packet closes their bodies:

- `WeilConjectures.completedScalarChainComparison_existsUnique` (retained proof).
- `WeilConjectures.completedScalarComparison_existsUnique` (localization descent).
- `WeilConjectures.completedScalarIdentityMultiplication_existsUnique` (retained proof).
- `WeilConjectures.completedScalarIdentityUnit_existsUnique` (retained proof, with its
  coordinate calculation factored into a proved private helper).
- `WeilConjectures.finiteFreeCompletedScalarComparison` (decomposition and assembly).

`WeilConjectures.completedCoefficientMap_existsUnique` was already proved and remains
proved. The new `WeilConjectures.completedIntegralFiniteFree` has no holes. Every private
helper and definition in the packet has a complete proof or construction.

The packet adds exactly these two named theorem holes:

- `WeilConjectures.completedIntegralPrincipalUnitCriterion`, node
  `lem-weil-completed-integral-principal-unit-criterion`.
- `WeilConjectures.completedIntegralQuotientModelComparison`, node
  `lem-weil-completed-integral-quotient-model-comparison`.

There are no holes in the item itself. The main theorem's mathematical middle clause is
reduced to these separate results; that part is a decomposition, not a proof with all
new dependencies closed. Relative to the current five-hole item, five bodies are closed
and two holes are added, for a packet net of three. The final closure ledger, not this
local count, determines project progress.

## No longer needed

The parent proof no longer uses these former proof dependencies:

- `lem-weil-pbc-constant-completion-equivalence`
  (`Sheaf.Paper.ConstantCompletionEquivalence`): use the proved actual completed-quotient
  presentation and normalized principal model instead.
- `lem-pur-finite-free-quotient-completion`
  (`Sheaf.Paper.FiniteFreeQuotientCompletion`): use the independent-universe finite-free
  completion exchange, which already supplies the unit-preserving derived comparison.
- `lem-pur-unit-power-completeness`
  (`Sheaf.CategoryTheory.UnitPowerCompleteness`): positive ramification is supplied
  directly to that exchange; no separate change of local completeness predicates is used.

The main proof also avoids the exchange wrapper's unused monicity and abelian-sheaf
exact-product hypotheses; the temporary private monicity helper was removed. Regular
quotient presentations are still needed in the one-field criterion.

These are removals from this proof route, not withdrawals of their declarations or claims
that no other parent needs them. No module is deleted. The unit's finite-basis,
regular-quotient, finite-free exchange and balanced-tower route remains intact.
Other former direct dependencies move under the new arithmetic and one-field nodes;
they are retained transitively, rather than falsely reported as pruned.

Removed direct imports from the item (some remain available through used dependencies):

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`
- `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Mathlib.LinearAlgebra.FreeModule.PID`
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.CategoryTheory.RingedKoszulCompletionReflector`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.DerivedComplete`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.ExtendedCechCompletionModel`
- `Sheaf.Paper.IntegralReductionTowerCanonical`
- `Sheaf.Paper.WeilCompletedTensorReflector`
- `WeilConjectures.Algebra.Homology.RoosComplex`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`
- `WeilConjectures.RingTheory.FiniteOverCompleteRing`

The ordinary `IntegralScalarExtensionWellDefined` proof import is replaced by `import all`
for its existing private normalization APIs. `DerivedChangeOfRingsCochainModel` remains a
proof import. All four original public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The general regular-quotient unit criterion is formulated on a small site with equal site
and coefficient universes. Applying it to the actual pro-etale site is not a direct Lean
application: it needs the normalized canonical-small-model transport and the actual
constant residue comparison. This is now an explicit one-field node.

Likewise, the principal model's abstract cokernel tensor tower is not definitionally the
actual integral scalar reduction tower. Its balanced tensor isomorphism and both strict
cone coordinates must be checked before identifying units. This is the second new node.

A high-priority upstream sheafification instance fixes the coefficient universe at the
site size. It is disabled locally so that the existing independent-coefficient instances
are used. This does not change any public construction or impose equality of universes.

The known Roos/intrinsic-completeness equivalence was not imported: its recorded dependency
closure returns to this item. The chosen completion exchange, regular-quotient criterion,
strict replacement and small-model definitions were checked for a path back to this node;
none has one. The proposed new graph also has no cycle.

## New nodes

`lem-weil-completed-integral-finite-free` is the proved arithmetic specialization of the
adic basis-limit theorem to the actual completed coefficient map. Its module contains one
public theorem and proved private transport helpers.

`lem-weil-completed-integral-principal-unit-criterion` is the one-coefficient-field
specialization of the regular completion-unit criterion to the actual integral reduction
tower, with independent universes and any normalized principal completion model.

`lem-weil-completed-integral-quotient-model-comparison` is the balanced tensor and
counit-normalized localization comparison between principal completion of ordinary scalar
extension and the actual strict integral scalar extension. It includes the full unit
equation and its zero shifted-coordinate normalization, without any completeness premise.

All three records are under `dag/nodes/sec-smooth-purity/`, with the parent's chapter and
unit. The three required kinds of Mathlib search are recorded for each new node.
`coord/changes/finite-free-completed-scalar-proof-elaboration-F1.md` records the local
elaboration commands, private helper universes, and unchanged effect on each direct user.
Existing public statement texts and construction data are unchanged.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
