## What changed

Proved `CategoryTheory.DerivedInternalHomSectionsModel.derived_internalHom_sections_model` by the recorded K-flat resolution and natural derived-sections comparison argument. The existing `tensorRightAdjoint_iso` proof and both public signatures are preserved.

Added the proved module `Sheaf.Algebra.Homology.GlobalTensorHomCochainsOfUniverses`. Its tensor–Hom cochain equivalences respect the differential and have independent site and coefficient universes. The proof reuses presheaf currying, sheafification naturality, and the generic categorical cochain equivalence; private constructions identify the actual sheaf Hom complex, including its sign convention. No adopted source module changes.

The representative comparison uses the existing independent-universe quasi-isomorphism theorem. The sections comparison uses the natural right-derived functor unit and proves it invertible on the Hom models by replacing the source with a K-flat complex. The final assertion uses Mathlib's ordinary Hom-complex cohomology and K-injective localization results in every integer degree.

## Proved and sorry left

Closed the one original hole, `CategoryTheory.DerivedInternalHomSectionsModel.derived_internalHom_sections_model` (node `lem-sfb-derived-internal-hom-sections-model`).

Proved the new supporting theorem `CategoryTheory.global_tensorHom_cochainsOfUniverses` (node `lem-sfb-global-tensor-hom-cochains-universes`). All private helpers are proved.

Original holes: 1. Holes closed: 1. Holes added: 0. Holes remaining in delivered modules: 0. No unfinished statement was split off. Dependencies already stated elsewhere remain available as required by stage 3.

Validation: `lcompile.py --all` compiled both delivered modules in import order without warnings (49.6 seconds for the cochain lemma; 47.5 seconds for the assigned module). Both original public signatures, the existing `tensorRightAdjoint_iso` proof, and the original public imports match the repository source. Neither delivered Lean file contains `sorry`.

## No longer needed

Removed the direct imports `Sheaf.Algebra.Homology.KInjectiveHomComplex` and `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`. The former supplies only the specialized K-injectivity result, so the present argument proves the needed independent-universe version directly from the new cochain lemma. The latter is replaced by `Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses`.

Removed the corresponding direct proof dependencies and old `tool_uses` entries `lem-pur-hom-kflat-into-kinjective` and `lem-pur-rhom-well-defined`. Their independent-universe replacements and the actual argument are recorded in the node. The previously proved tensor-adjoint argument still uses the derived closed structure, whose own imports include specialized Hom-complex theory: no claim of global withdrawal or of an unreachable module is made. No module is withdrawn.

No global Hom-complex shift lemma, higher sheaf Ext construction, or bounded-below resolution result is required: Mathlib's all-degree ordinary Hom cohomology comparison gives the formula directly. The natural comparison is defined before choosing a K-flat resolution, so no functorial K-flat replacement or independence-of-resolution split is needed. `def-pur-sheaf-hom` is now a dependency of the new cochain lemma rather than a direct step of the model proof. All other remaining original proof-dependency families are used.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid and is followed. Two imported specializations do not cover the item's independent coefficient universe. The quasi-isomorphism companion already exists, and the new proved tensor–Hom cochain statement supplies the generic K-injectivity step without changing any definition or source-library signature.

The generic categorical internal Hom complex has a different differential convention from the sheaf Hom complex. The private comparison multiplies the degree-(p,p+n) component by `(-1)^(pn)`; its differential compatibility is proved. Currying and tensor symmetry then recover the ordinary tensor–Hom cochain differential.

## New nodes

`lem-sfb-global-tensor-hom-cochains-universes`, in `dag/nodes/sec-six-functors-basics/`, is the fully proved global-cochain consequence of Stacks Tag 0A90 (`lemma-compose`). It is strictly the tensor–Hom portion of the K-injectivity argument, not a renamed version of the model theorem. Its statement includes arbitrary unbounded complexes and every integer degree; zero complexes and the empty site require no exceptions. It carries the same unit `sk-lem-int-ext`, whose route is preserved. Preflight requests a record for the proof-local commands: `coord/changes/X9-derived-internal-hom-sections-proof-commands.md`. The record checks the existing theorem consumer and documents that no existing statement, definition, or public import changes.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
