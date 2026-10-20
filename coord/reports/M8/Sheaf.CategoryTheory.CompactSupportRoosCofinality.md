## What changed

Proved both assigned declarations in
Sheaf.CategoryTheory.CompactSupportRoosCofinality without changing their
statements, public definitions or public imports. Retained and completed the
four auxiliary modules already present in the interrupted sandbox.

The cofinal map is the actual shifted cone map of selection and finite-block
summation. Product extensionality proves naturality and augmentation
compatibility. Finite telescoping and a nested finite-sum identity prove strict
identity and composition, including transport between equal restricted towers.
For quasi-isomorphism, use a K-injective tower resolution, the recorded strict
Roos derived-limit comparison, preservation of K-injectives by restriction,
and initiality of the arithmetic index functor. The resulting two commuting
squares and two-out-of-three prove the specified map is a quasi-isomorphism.

Finite-free scalar extension preserves products through a natural finite-power
identification after forgetting the coefficient action. The generic additive
cone comparison then supplies the normalized complex isomorphism, naturality,
and cofinal compatibility. The final augmentation equality is proved directly
from the product comparison and the two biproduct projections.

Local irreducibility of the cone constructions and scalar functor prevents
expensive accidental unfolding; their coordinate APIs and explicit object/map
formulas perform the computations. The final main module compiled cleanly in
34.5 seconds. All four retained auxiliary modules also compiled successfully.
The final assembly uses private lemmas over abstract categories for arithmetic
composition, augmentation and preservation of products on complexes. A private
countable-product instance explicitly lifts the products on the base category.
The scalar functor has proved object/map equations, so the final proof keeps
its sheafified tensor construction folded. A typed private augmentation wrapper
fixes its codomain. None of these changes alters a public interface.
The earlier delivery-validation attempts were externally killed with exit 137;
neither pushed anything. On this continuation the required initial dry run
compiled the four auxiliary modules, then the main module exceeded 60 seconds.
A direct compile also exceeded that limit. Temporary profiling was confined to
the sandbox and removed afterwards; the retained complete proof then compiled
cleanly in 26.1 seconds with the normal options. The delivery validation below
uses this complete, unprofiled file.

Updated the parent node's proof and dependencies to the argument actually used.
No existing statement/definition repair or consumer adaptation is needed.
The local proof context is documented in
coord/changes/compact-roos-private-proof-context.md for the static interface check.

## Proved and sorry left

Closed both original holes:
- CategoryTheory.compactSupportRoosCofinality
- CategoryTheory.compactSupportRoosFiniteFree

Added zero holes. Every delivered module has zero direct sorry tokens.
The four new auxiliary results are also proved:
- CategoryTheory.strictRoosAdditiveComparison
- CategoryTheory.constantFiniteFree_preservesCountableProducts
- CategoryTheory.constantFiniteFree_underlyingPowerIso
- CategoryTheory.constantFiniteFree_sectionBasis

These proofs use the project's stated comparison and resolution declarations;
this is not a claim that every transitive dependency is already sorry-free.
There are no split-off unfinished results and no hollow definitions.

## No longer needed

Removed proof imports:
- Mathlib.LinearAlgebra.TensorProduct.Basic: the tensor helper uses Pi instead.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses: scalar extension
  uses the actual change-of-rings construction and module sheafification;
  a monoidal structure on cochain module sheaves is unnecessary here.
- Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionCochainModel: no declaration
  from this attempted route is used. The map and its block identity come from
  StrictRoosAdditiveComparison; restriction of K-injectives comes from
  StrictTowerArithmeticRestrictionResolution.

The explicit kernel section and contraction in the original node's proof
steps 2–4 are not needed: the recorded derived-limit comparison gives the
shorter quasi-isomorphism argument described above. Those steps did not have
separate nodes or modules to withdraw. The tensor-product and constant-sheaf
nodes remain needed through the finite-basis helpers. No existing module is
withdrawn, and no unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The saved report was stale: it described an open coefficient-basis theorem and
an unfinished cofinality composition clause. Both are now proved. Some old
compiler logs reported temporary compile-service failures, but the service is
currently returning diagnostics and successful compilation. No such old failure
is being used as a reason to stop.

The initial active file contained an incomplete experiment. The fuller theorem
statements were restored from the saved sandbox, then the identity,
composition, ordinary-limit coordinate comparison and finite-free assembly
were repaired and compiled. Explicit product families are required for the
limit projection rewrites. Restricting unfolding avoids expanding the entire
shifted cone and change-of-rings construction during elaboration.

The parent DAG's old contraction route was a plan; its revised proof now
records the actual K-injective argument. Existing public signatures and the
paper's conclusion are preserved, including the initial indices before e.
The finite-basis proof covers rank zero, zero rings, the empty site and objects
with an empty covering; it does not assume every section of a constant sheaf
is globally constant.

## New nodes

lem-pur-constant-finite-free-products, module
Sheaf.CategoryTheory.ConstantFiniteFreeProducts: preserves countable products
by transporting finite-power preservation and reflecting limits. Fully proved.

lem-pur-constant-finite-free-power-iso, module
Sheaf.CategoryTheory.ConstantFiniteFreePowerIso: the underlying scalar-extension
functor is naturally a finite power, via the compatible coefficient bases and
the sectionwise tensor universal property followed by sheafification. Fully proved.

lem-pur-roos-additive-comparison, module
Sheaf.CategoryTheory.StrictRoosAdditiveComparison: shifted cone maps and the
normalized comparison for additive functors preserving the relevant products,
including strict naturality and arithmetic restriction. Fully proved.

lem-pur-constant-finite-free-section-basis, module
Sheaf.CategoryTheory.ConstantFiniteFreeSectionBasis: constructs compatible bases
for sections of constant coefficient sheaves by sheafifying constant modules,
proving the coefficient comparison locally bijective, and transporting the
finite basis. Fully proved.

All four nodes were retained from the earlier attempt. Added the missing
LeanSearch record for the section-basis node: LeanFinder and Loogle count as
one search kind. Added coord/changes/compact-roos-private-proof-context.md
to document the local proof commands conservatively flagged by preflight.
No additional node was introduced during this continuation.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
