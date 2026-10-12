## What changed

Proved `AlgebraicGeometry.module_cohomology_iso_underlying_abelian` in
`Sheaf.AlgebraicGeometry.ModuleAbelianZariskiCohomology`, preserving its signature,
universe, `hE` assumption, and explicit `hasExt_of_enoughInjectives` on the right.
The module contains two fully proved private comparison helpers:
`topCohomologyEquiv` identifies terminal-open representable Ext with constant-integer Ext;
`topCohomologyIsoDerived` compares this with derived abelian evaluation, separately treating
zero and positive degrees. The main proof forgets an injective module resolution, proves
that its augmentation remains a quasi-isomorphism, uses termwise acyclicity, and composes
homology comparisons for the identical underlying section complexes.

Added proof-only imports of the proved source finite-colimit forgetful instance,
Ext precomposition equivalence, and Leray acyclic-resolution comparison, plus the existing
proved Ext/evaluation bridge. All three public imports stay unchanged. Updated the item's
node `proof`, `proof_deps`, and `proof_origin` to record the implemented route.
No definition, target, or public statement changed; no new unresolved statement was added.

## Proved and sorry left

Proved the one original sorry:
`AlgebraicGeometry.module_cohomology_iso_underlying_abelian`
(node `lem-sc-module-abelian-zariski-cohomology`). Both private helpers are proved.
No sorry remains in the delivered module, and none is added elsewhere.

The proof deliberately uses the existing unresolved theorem
`CategoryTheory.injective_module_abelian_acyclic`
(node `lem-sc-injective-module-abelian-acyclic-zariski`, module
`Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic`). It is the remaining
mathematical dependency, not a relocated copy of this theorem. The module-side
`moduleSheaves_abelian_enoughInjectives`, the source acyclic-resolution comparison,
and the existing Ext/evaluation comparison are proved. Local compilation is clean.

Edge cases: q = 0 is handled with the degree-zero adjunction and derived-zero isomorphism;
q = n+1 uses n+1 > 0. No assumption of nonempty space, nonzero module, affineness,
Noetherianity, or positive q is introduced. All constructions apply unchanged to the
empty scheme and the zero sheaf. Forgetting injectives is only asserted to give acyclic
objects, never injective abelian sheaves.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`: the proved source instance
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` supplies
  finite-colimit preservation directly. The node
  `lem-weil-pbc-module-sheaves-colimits-forgetful` remains a proof dependency for exactness;
  its larger packaging theorem and module are not used by this proof.
- `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives` and the proof dependency
  `lem-weil-pbc-scheme-modules-enough-injectives`: replaced by the already-proved
  ringed-space theorem `lem-sc-ringed-space-module-sheaves-enough-injectives` that the
  module-cohomology definition already imports.
- `Sheaf.Paper.PQFCohomology` and proof dependency `pqf-def-cohomology`: no higher-direct-image
  or delta-functor packaging is needed. The concrete definition
  `def-sc-ringed-space-module-cohomology` suffices.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`: replaced as a
  direct import by its proved `RightDerived.Acyclic` extension, which actually provides
  `rightDerivedObjIsoOfResolution`. LongExactSequence remains a transitive dependency
  of Acyclic; this is not a claim that its module can be removed from the library.

The old proof dependency `lem-weil-pbc-site-sheaves-enough-injectives` is unnecessary here:
the unchanged statement already assumes `hE`. `def-sc-zariski-site` remains a statement
dependency and need not also be a proof dependency. The shorter direct proof does not
use `Sheaf.CategoryTheory.RightDerivedExactComposite` or `lem-sc-ext-derived-composite`;
these were examined but never made part of the delivery. No unit statement or realized
unit step is bypassed (`sk-prop-cd.realized` is empty).

## Where the brief, the DAG or earlier work was wrong

The existing theorem docstring says forgetting gives an injective resolution. Exactness
only gives an exact resolution, whose terms are Gamma-acyclic by the existing injective
module acyclicity theorem. The node's original step 3 correctly used this distinction;
the Lean proof implements it. The original docstring is preserved and this discrepancy
is reported for review.

The DAG's scheme-specific enough-injectives step and additional site-enough-injectives
citation are redundant for this precise Lean statement. Module cohomology already uses
the proved ringed-space enough-injectives theorem, while abelian enough injectives is hE.
Mathlib does not directly supply finite-colimit preservation for `toSheaf`, but the
proved source extension does. No missing bridge had to be stated: the existing proved
`new-sheaf-cohomology-derived-evaluation` plus elementary terminal-open Ext glue closes it.


## Second reading by F3

1. Compared the complete delivered module with the repository version and checked
   existing declarations with the delivery signature parser: no existing signature,
   universe, assumption, definition, or public import changed. No change record is
   needed. Verdict: pass.
2. Compiled the module locally without errors or warnings. Searched the delivered
   source for prohibited declarations and holes: no new axiom or forbidden mechanism,
   and no sorry remains. Compiled a scratch copy with `#print axioms` for both private
   helpers and the main theorem. Both helpers use only propext, Classical.choice and
   Quot.sound. The main theorem additionally uses sorryAx through existing open
   dependencies, in particular injective_module_abelian_acyclic. This closes the
   item's one direct hole, not its transitive mathematical obligations. Verdict: pass.
3. No new split-off statement or new node is delivered. Reviewed the fully proved
   private helpers: every open maps uniquely to the top open, so its representable
   is constant singleton and its free abelian sheaf is the constant integer sheaf.
   Ext precomposition and derived evaluation have the stated orientation. Degree
   zero is treated independently; successors are strictly positive. These arguments
   require no nonempty-space or nonzero-sheaf assumption, so include the empty scheme
   and zero sheaf. An additional differently worded msearch grep query for terminal
   open Ext and constant integers found no match. Verdict: pass.
4. Read the existing Ext/evaluation bridge, exact forgetful instance, and source
   acyclic-resolution comparison. The proof uses these existing proved results;
   it does not assume forgetting preserves injectives. All new imports are proof-only
   and supply used declarations or instances. The report accounts for every old
   proof dependency omitted from the new proof_deps. Checked sk-prop-cd.realized:
   its statement and step arrays are empty, and this delivery changes no unit route.
   The existing docstring's inaccurate phrase about an injective resolution after
   forgetting remains explicitly flagged above. Verdict: pass.
5. Compared each DAG proof step with the Lean: exactness preserves the augmentation's
   quasi-isomorphism, the existing acyclicity theorem gives termwise Gamma-acyclicity,
   the source comparison computes derived evaluation, and exact module forgetting
   commutes with homology of the common section complex. proof_deps is exactly the
   union of step uses; proof_origin identifies the source and implemented route.
   No new-node fields need checking. Verdict: pass.

Second-reading change: corrected the DAG proof description's `H.equiv_zero` to the
actual Mathlib declaration `H.equiv₀`. No Lean proof needed repair. Added this review
record and explicit axiom-check results; no holes or modules were added.
