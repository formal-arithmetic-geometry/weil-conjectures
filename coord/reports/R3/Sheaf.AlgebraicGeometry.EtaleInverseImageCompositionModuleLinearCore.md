## What changed

Wrote an unverified candidate replacement for the proof hole in
`AlgebraicGeometry.etaleInverseImageCompositionModuleLinearCore` without changing its
statement. The proof identifies the constant-ring maps using sheafification uniqueness,
constructs the module direct-image comparison with `pushforwardCongr₂` and
`pushforwardComp`, and constructs the module inverse-image comparison with
`conjugateIsoEquiv`. Compatibility with the given abelian comparisons follows from
sectionwise evaluation, the two specified hom-equivalence equations, and the mate
unit identity. Private categorical lemmas prove the composition and unit formulas over abstract
categories, and the concrete module proof applies them to the supplied data. No
definitions or other modules were changed.

Updated the existing node's proof, proof dependencies and proof origin to describe
this construction. The unit `sk-thm-p1` and all its realized steps are retained.

Validation failed: the final delivery dry run exceeded the 60-second compilation limit.
Nothing was pushed. The candidate proof is not a verified proof or a delivery.

## Proved and sorry left

Original hole addressed, but not verified closed:
`AlgebraicGeometry.etaleInverseImageCompositionModuleLinearCore`
(node `lem-weil-pbc-inverse-image-composition-module-linear-core`).

Holes added: zero. Split-off statements: zero. No `sorry` remains in the delivered
module. The proof uses the supplied module adjunction compatibility hypotheses;
it does not assume that the imported theory has already become axiom-free.

## No longer needed

Removed the redundant private imports
`Sheaf.CategoryTheory.RingedSiteModules` and
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`. Replaced the
private import `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` with
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`, whose proved mate
identity is used. The public exact-inverse-image interface supplies the other
required definitions and Mathlib APIs.

The node `lem-weil-pbc-constant-sheaf-maps-global-sections` is unnecessary for this
proof. Rather than evaluating only at the terminal object, `sheafify_hom_ext`
compares the two ring maps after the constant-presheaf unit on every object;
naturality of `toSheafify` finishes the comparison. Its role is replaced by
`def-weil-pbc-sheafification`, whose declarations already exist in Mathlib.

Mathlib's natural-isomorphism constructors provide naturality and inverses, so
separate inverse-linearity and module-naturality lemmas are unnecessary. No
blueprint unit or realized unit step is bypassed. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No incorrect mathematical statement was found. The DAG's global-sections argument
was more specialized than needed: uniqueness in sheafification gives the ring-map
comparison directly. The existing module-adjunction hypotheses already provide the
data needed for the categorical mate argument; the proof does not need to choose
inverse-image functors again from `etaleInverseImageModulesExact`.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
