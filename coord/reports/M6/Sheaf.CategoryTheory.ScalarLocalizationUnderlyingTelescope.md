## What changed

Retained the original theorem signature and all definition bodies. Moved the unchanged
scalarLocalizationTelescopeUnitSections declaration to the publicly imported tensor helper
to avoid an import cycle; its name, visibility, signature and body are identical. Replaced the prior unsound abstract split with an ordinary module-colimit statement, its proved degreewise complex assembly, and normalized derived-unit shift coherence. Proved the abstract inverse-scalar leg laws and scalar-factorization identity. Added the general abelian specialization of the already-proved complex homotopy-colimit argument to ComplexColimitHomotopyColimit, without altering existing declarations. The chosen complex representative, coproduct,
successor map and colimit map are kept abstract after their equations are recorded,
avoiding repeated unfolding of their large constructions. Repaired the tensor-unitor
normalization proof using mapped isomorphisms, the adjunction triangle identity and
explicit composition/evaluation equations; its module now compiles in about 17 seconds.

## Proved and sorry left

Closed CategoryTheory.scalarLocalization_underlyingTelescope without changing its signature.
Proved CategoryTheory.scalarLocalization_complexColimit by applying the ordinary module
colimit degreewise and assembling the differential and the normalized legs.
Proved CategoryTheory.scalarLocalization_moduleColimit by tensoring the regular-module
fraction colimit with M. The tensor--Hom adjunction preserves that colimit. The proved
SheafOfModules.exists_extensionTensorComparison identifies the apex, and its pure-tensor
formula identifies the zeroth leg. An induction cancels the invertible target scalar to
normalize every inverse-power leg. CategoryTheory.scalarLocalization_regularColimit is
proved sectionwise from the existing ModuleCat.localization_away_colimit and then descends
through module sheafification. The existing module-localization theorem remains an upstream
dependency; this delivery adds no hole there.

Also proved CategoryTheory.scalarLocalization_unit_commShift,
CategoryTheory.scalarLocalizationTelescopeLegLaws,
CategoryTheory.scalarLocalization_unit_factors, and
CategoryTheory.complex_colimit_homotopyColimit.
Original item: 1 hole; remaining in item: 0; holes added: 0. Every new theorem and
definition in this delivery has a complete proof or construction. Validation: all nine delivery modules compile in import order with no errors or warnings
(scratchpad/all-after-module-proof.log). The main item checks in 28.3 seconds, the
module-colimit helper in 18.1 seconds and the complex-colimit helper in 20.6 seconds.
The first completed dry run found only two missing LeanSearch metadata categories;
ran and recorded both searches. The corrected dry run passed (commit 2a47b46163, review class CODEX).
Its repeated probes for ComplexColimitHomotopyColimit and ScalarLocalizationModuleColimit
timed out; the launcher explicitly leaves those probes to the merge. Both files pass
normal compilation, and the first completed dry run reported no axiom-probe failure.
The first push attempt stopped before pushing when the regular-colimit file exceeded
60 seconds. A diagnostic recompilation at 100000 heartbeats checked the entire file
in 24.2 seconds without a deterministic timeout; the profile showed routine instance
synthesis and checking spread across declarations. Removed diagnostic options. The repeated delivery timeout prompted folding the chosen
regular-module colimit isomorphism (after recording its fraction formula) and the
presheaf colimit witness with clear_value. The revised packet compiles in import order
with no warnings (scratchpad/all-regular-folded-equations.log): regular colimit 21.7s,
module colimit 54.5s, complex colimit 42.8s, item 47.8s. No new sorry is split off. The proof keeps the coefficient-action instances abstract
until the sectionwise calculations and uses a folded localization-ring construction
plus its existing normalization API to avoid expensive definitional unfolding.

## No longer needed

Removed the following proof imports from the item:
Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses,
Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses,
Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed,
WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful,
Mathlib.Algebra.Module.LocalizedModule.Basic,
Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification and
Mathlib.CategoryTheory.Localization.Predicate and
Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor.
The new helpers provide the ordinary-colimit and unit arguments; the remaining direct
imports and existing public statement dependencies supply everything used by the proof. The direct TR3 comparison and lem-sf-triangle-morphism-iso are unnecessary for the existential telescope statement: the proof uses the canonical cone and its explicit comparison. The proved ordinary-colimit lemma retains the tensor and fraction dependencies; they have not been pruned from its argument. No unit statement or unit proof step is bypassed. The declared dependencies
lem-weil-pbc-exact-functor-derived-factorization and
lem-weil-pbc-localization-universal-property remain used in the shift helper through
Mathlib's canonical factorization and faithful-whiskering APIs. The module colimit
uses the proved source tensor--Hom adjunction directly in place of its compatibility
package tensorClosed. The derived telescope uses Grothendieck exactness directly;
the precoverage-specific module-sheaf colimit specialization is replaced by its
proved general abelian form. Removed obsolete top-level tool_uses
approvals for lem-pc-sheaf-modules-tensor-closed,
lem-weil-pbc-module-sheaves-colimits-forgetful and
lem-weil-pbc-exact-functor-derived-factorization from the item node: the ordinary-colimit
child owns the tensor argument, the proof uses Grothendieck exactness directly, and the
derived functors and their factorization maps are already supplied by the item hypotheses.

## Where the brief, the DAG or earlier work was wrong

The retained earlier sandbox had false helpers: its abstract telescope-existence statement allowed arbitrary adjunctions, and its shift-law statement omitted compatibility of the adjunction with shifts and linearity of target shifts. Neither was delivered. The replacement helpers include the missing hypotheses. The existing site-specific complex homotopy-colimit API assumes a precoverage with pullbacks, whereas the item assumes only a Grothendieck topology. The same existing proof works in any abelian category with exact sequential colimits, and the new proved theorem exposes that generality. All existing signatures stay unchanged; no consumer proofs require adaptation.
The launcher classifies the additive theorem in ComplexColimitHomotopyColimit as a
forced-adaptation review item; the actual file diff only appends that theorem, leaving
all originals unchanged. The reviewer can verify the additive extension directly.

The inherited attempt clock was reset externally: original start 1792425806.7881174,
resumed start 1792435885.810598 (session allowance 86400 seconds). No worker edits to
that metadata were made; proof work continued through the reset.

## New nodes

lem-weil-pbc-scalar-localization-complex-colimit: proved ordinary complex colimit with
fraction-normalized legs, assembled degreewise from the module colimit.

lem-weil-pbc-scalar-localization-module-colimit: proved ordinary module-sheaf colimit,
with normalized unit and inverse-power legs. Checked t=0, nilpotent t, zero divisors,
unit t, zero ring and empty site: the statement has no regularity assumption.

lem-weil-pbc-scalar-localization-regular-colimit: proved regular-module fraction colimit
by sectionwise module localization and the module sheafification adjunction.

lem-weil-pbc-extension-tensor-comparison: proved restricted scalar-extension comparison,
normalized on local pure tensors, with the regular tensor unitor and naturality API.

lem-weil-pbc-scalar-localization-unit-shift: coherence of the actual normalized derived unit; proved by sectionwise extensionality and faithful precomposition by localization. Includes every complex and every section, so its termwise normalization is unique; it does not assert a functorial cone.

lem-weil-pbc-scalar-localization-telescope-leg-laws: proved generic naturality and shift algebra with the necessary hypotheses.

lem-weil-pbc-scalar-localization-unit-factors: proved generic factorization identity; no linearity over the target coefficient ring is assumed for restriction.

The existing lem-kun-complex-colimit-hocolim node also attaches the new general abelian
API in lean.declarations. No existing declaration or statement was changed.

Change record: coord/changes/M6-complex-colimit-general-abelian.md.

Change record: coord/changes/M6-scalar-localization-unit-sections-move.md.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
