## What changed

Preserved every existing public declaration, signature, definition and public import.
Proved AlgebraicGeometry.ProEtale.coefficient_finite_descent_lisse by assembling
finite-field object models, finite-stage morphism lifts and the complete equality
criterion on representatives. Its private helpers prove ordinary scalar faithfulness
using the existing coefficient-linear projection, coherence of the canonical extension
comparisons, transition invariance, and both directions of the EqvGen criterion.

Added two new modules, each with a proved theorem and its DAG node:
Sheaf.Paper.LisseFiniteCoefficientModel and Sheaf.Paper.LisseFiniteHomLift.
The first refines the trivializing cover to a finite affine cover, supplies standard
free local models over the base field, applies the existing finite local-model gluing
theorem, and transports back through the canonical identity coefficient comparison.
The retained local identifications prove that the resulting model is lisse.

The second uses internal Hom continuity, the coefficient complex colimit evaluated
in degree zero, and qcqs unit-section continuity to lift the scalar adjoint to a
finite stage. A complete calculation of adjunction units identifies the resulting
map with the canonical conjugation required by the original statement.

Updated all three node copies to follow these proofs. Added the required change record
coord/changes/lisse-finite-descent-proof-commands.md for the added section commands
and local irreducibility attributes. No existing statement, definition, visibility or
public import changes.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.ProEtale.coefficient_finite_descent_lisse
(det-lem-coefficient-finite-descent-lisse).

Both new intermediate theorems are proved, without sorry:

- AlgebraicGeometry.ProEtale.exists_lisse_finiteCoefficient_model
  (lem-sfb-lisse-finite-coefficient-model).
- AlgebraicGeometry.ProEtale.exists_lisse_finite_hom_lift
  (lem-sfb-lisse-finite-hom-lift).

Actual delivery hole count: zero. Holes closed: one original; holes added: zero.
No sorry remains in any delivered theorem or definition. These are proofs from
existing declarations, whose own transitive obligations are not claimed closed.
In particular, the old report's two remaining obligations have both been proved.

All three modules compile cleanly through the required lcompile.py workflow.
The complete sandbox compiled with the object model in 12.0 seconds, Hom lifting
in 10.4 seconds, and the parent module in 37.6 seconds, all with exit code 0. Empty schemes, zero ranks and
varying ranks are retained; no global constant-rank assumption is introduced.

## No longer needed

Removed these direct proof imports from the item module:

- Sheaf.CategoryTheory.SiteCoveringAxioms
- Sheaf.CategoryTheory.SheafTensor
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
- Sheaf.CategoryTheory.SiteModuleSheafGluing
- Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
- Sheaf.Paper.CoefficientFiniteDescentSections
- WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars

The object proof reuses the existing finite local-model gluing interface, which
implements the same finite overlap descent and sheaf-gluing step. It therefore
needs no separate new matrix-descent or generic site-gluing obligation. The Hom
proof uses internal Hom and the existing coefficient colimit instead of a new
local matrix gluing argument. Their updated node proof_deps list the actual route.
Original geometric dependencies may remain needed transitively by the gluing
interface; no module is claimed globally unreachable.

For the representative equality criterion, coefficient section injectivity,
local difference matrices and morphism gluing are unnecessary: the existing
split unit proves ordinary scalar faithfulness on all module objects. The
canonical comparison coherence and directed composita then give the two-edge
zigzag at a common field. All original public imports are retained.

Removed the following original direct proof dependencies from the parent node
because its updated argument uses the two proved helpers and split-unit faithfulness:

- def-weil-pbc-sites-and-cohomology
- def-weil-pbc-proetale-covering
- lem-weil-pbc-qcqs-morphism-permanence
- sk-def-pe-site
- def-pur-localized-ringed-site
- sk-def-sfb-module-objects
- sk-def-sfb-sheaf-tensor
- def-pur-sheaf-tensor-product
- det-lem-coefficient-finite-descent-sections
- lem-weil-pbc-site-module-sheaf-gluing
- lem-pur-sheaf-hom-cover-gluing
- def-sfb-subfield-coefficient-map

These removals concern the parent proof route; definition and transitive uses remain
where required. Removed the obsolete top-level tool_uses approvals for
lem-weil-pbc-site-module-sheaf-gluing, lem-pur-sheaf-hom-cover-gluing, def-pur-sheaf-tensor-product, def-weil-pbc-sites-and-cohomology. Their old direct gluing route is replaced by
the existing local-model and internal-Hom interfaces listed in the helper nodes.

## Where the brief, the DAG or earlier work was wrong

The retained report was stale: it listed the finite-stage Hom lift as a hole,
although its complete proof was already in the retained sandbox. The remaining
object-model obligation is now also proved using the existing stronger local
model interface, without assuming a noetherian base.

The injectivity plan is longer than necessary: the existing coefficient-linear
projection also proves ordinary scalar faithfulness. The canonical scalar
comparison coherence must still be checked, and is fully proved here.

The new uses of local-model gluing, internal-Hom continuity and coefficient
complex colimits are generic tools from the proper-base-change unit. Object
descent still refines a finite affine cover and descends its free local models;
the unit's object/morphism descent steps and conclusion are preserved.

The resumed dry run compiled and passed its axiom probes but requested a change
record for the added proof commands. That record is now included.

The first required dry run was refused by the elapsed-time guard while one new
sorry remained. Work continued and removed it. One compile request received no
server answer within 193 seconds; the next request compiled and exposed a
coefficient-transport type mismatch, which was repaired. These transient tool
results are not claimed as mathematical failures or delivery success.

## New nodes

lem-sfb-lisse-finite-coefficient-model, realized by
lean/Sheaf/Paper/LisseFiniteCoefficientModel.lean, records the finite affine free
cover, the existing finite enlargement/gluing theorem, and the coefficient
comparison transport. Its theorem is proved.

lem-sfb-lisse-finite-hom-lift, realized by
lean/Sheaf/Paper/LisseFiniteHomLift.lean, records internal Hom continuity,
finite-stage factorization and the exact canonical comparison equation.
Its theorem is proved. The parent proves representative equality separately.

Change record: coord/changes/lisse-finite-descent-proof-commands.md.

Both nodes record actual logged LeanSearch, Loogle and grep queries. Their
public signatures are the original clauses needed by the parent, with object
and morphism existence separated from the equality argument; neither is a
renaming of the complete parent statement.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
