## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.formalClosedSupportII` with its original
signature, predicate, coefficient hypotheses and canonical tensor shift structure unchanged.
All proof helpers are private, proved, and contained in the assigned module. The retained
attempt's two subclaim modules have been consolidated into that module; neither is delivered.

The proof constructs product preservation for the support kernel and immersion pullback,
passes to the right derived functor on products of K-injectives, and proves left t-exactness
using the bounded-below injective resolution. Exact open restriction gives the second clause.
Finite locally free tensor preserves products by descent of the finite biproduct comparison.
Its derived-tensor comparison is built from the tensor counit on the flat single complex,
and descended through the localization. Finally an explicit triangle isomorphism transports
every Roos triangle using the projection-normalized product comparison and the given shift
comparison. Rank zero is covered by the empty finite biproduct; arbitrary covers, including
an empty cover of the empty scheme, use the existing joint-conservativity theorem.

The existing node's eight proof steps, proof dependencies and proof origin now describe the
actual proof. Public imports are retained, including `Sheaf.Paper.FormalClosedSupport`, so
the unit's support construction remains in the route. Proof imports alone were changed.
No definition or public interface changes or consumer adaptations are needed. The change
record `coord/changes/FormalClosedSupportII-proof-environment.md` documents the additional
instance-search option and namespace opening required by the private proof helpers.
The downstream check found 220 modules in the import closure; textual uses of each of
the three public declarations occur only in the item itself. Their types are unchanged.

Validation: the consolidated single file compiled through lcompile.py in 43.6 seconds;
after import pruning it compiled in 40.7 seconds, with no diagnostics. The resumed
session recompiled the retained proof against the current build in 40.5 seconds, also
with no diagnostics. All lines are at most
100 characters. The required delivery dry run passed compilation, preflight, and declaration-axiom
checks (candidate 0f2a7fd499; CODEX review class). The earlier retained search log was checked, and fresh leanfinder, loogle and grep
searches found generic exact-derived constructions but no theorem for the complete item.

## Proved and sorry left

Closed the original single hole in
`AlgebraicGeometry.ProEtale.CondensedRing.formalClosedSupportII`
(node `sk-lem-formal-closed-support-ii`): **1 of 1 proved**.
Added holes: **0**. Remaining holes in the delivery: **0**. Split-offs: **0**.
All thirteen private supporting theorems, including the retained product-preservation and
tensor-comparison subclaims, are proved. Dependencies may still contain their own already
recorded holes; no claim is made that the target's full axiom closure is finished.

## No longer needed

Removed the following direct proof imports (their declarations may remain transitively
available; this list does not assert they leave the targets' entire import closure):

- `Sheaf.Paper.CartesianCoefficients`
- `Mathlib.CategoryTheory.Adjunction.Limits`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.Algebra.Homology.KInjectiveProductsTermwise`
- `Sheaf.Algebra.Homology.KInjectiveProducts`
- `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`

`Sheaf.Paper.CondensedFiniteFreeTensorExact` is retained as `import all`, because the proof
also reuses its proved private tensor-restriction and limit-comparison helpers.
`CondensedFiniteFreeInternalHomColimits` is imported for its proved finite-free internal-Hom
identification and cover-conservativity helpers; its colimit theorem is not assumed.

The separate site-derived tensor descent theorem and its K-flat sheaf-module encoding
(`lem-weil-pbc-site-derived-tensor-descent`) are not used: the comparison is constructed
with the existing tensor counit for the actual internal module category. No existence of a
chosen derived limit (`lem-weil-derived-limit-existence`) is needed, since the statement
transports every supplied Roos triangle. Generic Grothendieck and K-injective instances
already available for the actual internal category replace the separately stated ringed-site
resolution interfaces. The old tool approvals for these unused interfaces, and the separate
sheaf tensor-closed interface, were withdrawn from this node. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The retained report was stale: it described two remaining sorries and a moved assertion
predicate, whereas the retained Lean files already contained complete proofs of both
subclaims and the assertion predicate remained in the original module. This delivery
consolidates those proofs and records the actual zero-hole result.

The original planned comparison used the sectionwise sheaf tensor descent interface,
which does not directly name the actual internal module tensor. The proved internal
monoidal tensor counit and single-complex comparison give the required isomorphism directly.
Products in internal module categories are obtained by transferring the exact-products
theorem along `sectionModuleEquivalence`; this explicitly checks the encoding bridge.
The node now records `def-weil-pbc-internal-abelian-sheaf-module-equivalence` and
`det-pe-products-exact` as supporting dependencies. They serve only the product calculation;
they do not replace a unit's geometric or homological route.

No statement was disputed, weakened, or repaired. No new nodes.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
