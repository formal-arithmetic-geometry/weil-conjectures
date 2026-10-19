## What changed

Proved `AlgebraicGeometry.ProEtale.ellCohomologicalDimension_etale_comparison` without changing its signature, hypotheses, definitions, universes or visibility. Only its module and the proof fields of `det-cd-etale-comparison` change.

The torsion equivalence is proved generically for additive, finite-limit-preserving, colimit-preserving functors reflecting isomorphisms, including an arbitrary isomorphism to the resulting coefficient object. The proof constructs the natural kernel comparison and the isomorphism of canonical cocones, then preserves and reflects their colimit property. The absolute and relative comparison clauses apply the existing declarations in `Sheaf.AlgebraicGeometry.CohomologicalDimension`. For the bound, a separate proved private calculation shows that an additive colimit-preserving functor to abelian groups takes a primary torsion object to a torsion group. Applying this to geometric stalks and the existing local torsion characterization gives the input to the assumed vanishing bound. The final supremum argument is explicit Lean.

Added proof-only imports of `WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful`, `WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion`, `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`, and `Mathlib.Algebra.Category.Grp.Zero`. The public imports are preserved.

Validation: the retained final module was recompiled against the current library through
`lcompile.py` on 2026-10-19 in 4.2 seconds with exit code 0 and no warnings.
An exact text comparison against the current source confirmed that the public theorem
signature is unchanged. There are zero `sorry` tokens and no lines over 100 characters.

The edge cases remain covered: the zero object and empty supremum; exponent zero gives the kernel of the identity; arbitrary prime including residue characteristic; arbitrary X and Y for the relative statement. No bounded-exponent assumption is introduced. The field-valued stalk calculation is used only on the etale site.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.ProEtale.ellCohomologicalDimension_etale_comparison` (`det-cd-etale-comparison`). Added 0 holes. Left 0 holes in the item and added no modules or nodes. All private helper lemmas are proved.

The proof uses the existing, independently assigned declarations `AlgebraicGeometry.ProEtale.cohomologicalDimension_eq_etaleCohomologicalDimension` and `AlgebraicGeometry.ProEtale.relativeCohomologicalDimension_eq_etale` from `sk-def-cd`; their existing proof obligations remain in that module and are not claimed as closed here.

## No longer needed

The three original public imports are preserved. Removed six unused proof-only imports from the current source:

- `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`

The first five supply the longer route replaced by the existing comparison declarations and direct abelian-category argument. The last already enters through the preserved statement interface. No module is claimed globally pruned.

The direct proof dependencies `det-pe-classical-sheaves-modules`, `sk-prop-sf-comparison`, `sk-thm-pe-direct-image-comparison`, `def-sfb-right-derived-functor`, `def-weil-pbc-etale-cohomology`, and `lem-weil-pbc-module-sheaves-colimits-forgetful` are unnecessary as additional proof dependencies of this node. The absolute and relative comparison theorems already exist in the declared dependency `sk-def-cd`, which is the shorter route. The underived generic comparison instances suffice for coefficient transport. Geometric stalks give local torsion without constructing the sheafified sectionwise union. The obsolete top-level tool approval for `lem-weil-pbc-module-sheaves-colimits-forgetful` is withdrawn. These dependencies can remain needed transitively elsewhere, in particular by `sk-def-cd`; this report does not claim their global removal. The etale cohomology declaration also remains a statement dependency.

## Where the brief, the DAG or earlier work was wrong

The preceding attempt saved the complete proof but could not reach preflight before its hard stop because the delivery tool was waiting for worktree capacity. This resumed attempt retains that proof and checked it against the current sources. A fresh single-file compile passed in 4.2 seconds without warnings, and an exact text comparison confirmed the public theorem signature is unchanged. The first completed dry run flagged the extra file-level universe command needed by private helpers; their universe parameters are now declared on the private theorems themselves, preserving the original file-level commands and public interface.

The original proof plan duplicates the absolute and relative comparison theorems already supplied by its `sk-def-cd` dependency. They can be applied directly. The exact fully faithful comparison is available for AddCommGrpCat itself, so no transfer through integer modules is necessary. The unit record `sk-def-cd` has no separately realized statement or proof steps that this reuse bypasses. The remaining transport and bound arguments are proved here, rather than re-stated as new obligations. No statement was disputed or repaired.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
