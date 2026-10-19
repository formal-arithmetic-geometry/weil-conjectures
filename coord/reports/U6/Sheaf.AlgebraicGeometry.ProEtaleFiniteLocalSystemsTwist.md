## What changed

Proved AlgebraicGeometry.ProEtale.finiteLocalSystemsTwist, with its original full statement.
Its helper etaleCover_of_finitelyPresentedModels constructs a cover using the proved
proEtale_model_type_opens and the generalized uniform-model Isom-sheaf argument. The comparison
lower star and canonical counit then give descent without constructing a separate gluing datum.
The reverse preservation uses constant comparison and slice localization. Full faithfulness and
the invertible unit are existing library results. The finite-ring clause uses Mathlib's
Module.finitePresentation_of_finite. No predicate definition or existing public signature changes.

Generalized the private finite-set arguments in the unclaimed
Sheaf.Paper.ProEtaleUniformModelEtaleCover to finite generating sets, and added the proved
AlgebraicGeometry.Scheme.etale_cover_of_proetale_uniform_finiteType_model. The original theorem
is preserved verbatim as a specialization. The old direct consumer
Sheaf.Paper.ProEtaleEtaleFiniteModels compiled unchanged against the new module. The continuation dry run on 2026-10-19 passed compilation and preflight (CODEX,
commit 488e4a7f82). Both changed modules also passed lcompile.py --all in this
continuation. A source comparison verified that the four predicate definitions and
original main theorem signature are unchanged. Neither delivered file contains a sorry.
Existing dependencies may still contribute sorryAx; this delivery closes its assigned
hole without claiming the entire transitive dependency closure is proved.

Change record: coord/changes/proetale-finite-type-uniform-model.md. It includes the full 1262-row
consumer listing. No module held by another group was adapted.

## Proved and sorry left

Closed the one original hole AlgebraicGeometry.ProEtale.finiteLocalSystemsTwist
(node det-pe-finite-local-systems-twist). Original holes: 1; proved: 1; added holes: 0;
remaining holes in delivered files: 0; split off: 0. Both new public helper statements are proved.
The retained draft's origin_part and transport_part holes were removed, and its etale-cover hole
was proved. They were never landed, and are not counted as original project holes.

## No longer needed

Removed proof imports:
- Sheaf.AlgebraicGeometry.ProEtaleComparisonTorsor
- Sheaf.AlgebraicGeometry.ProEtaleFiniteConstantHom
- Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsType
- Sheaf.AlgebraicGeometry.TorsorComparisonGlue
- Sheaf.CategoryTheory.RingedSiteModules
- Sheaf.CategoryTheory.SiteCoveringAxioms
- Sheaf.CategoryTheory.SiteModuleSheafGluing
- Sheaf.CategoryTheory.Sites.ConstructibleTorsor
- Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
- Sheaf.Paper.SliceSiteLocalization
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver

The item no longer needs the intrinsic ringed-module finiteConstantHom interface or its
finiteLocalSystemsType representative-set interface: the existing fixed-coefficient
proEtale_model_type_opens performs the required isomorphism-type decomposition directly on
models occurring in the given cover, including empty overlaps. This retains the unit's
model-type partition followed by the Isom-sheaf descent route. Its Isom sheaf is proved locally
constant with a finite generating set, so torsorComparisonGlue and ComparisonTorsor are not
needed as separate interfaces. The canonical counit and local conservativity replace the
explicit SiteModuleSheafGluing cocycle. SliceSiteLocalization is replaced by the proved
comparison/localization isomorphisms and the counit compatibility theorem. The size-convention
representative-set construction is unnecessary because the original cover indexes the models.

Direct node dependencies pruned: det-pe-finite-local-systems-type,
det-pe-finite-local-systems-hom, def-weil-size-convention, lem-weil-pbc-open-immersion-etale,
def-pur-localized-ringed-site, def-weil-pbc-sites-and-cohomology,
def-weil-sheaf-of-modules-category, def-constructible-torsor, def-pe-comparison-torsor,
det-pe-torsor-comparison-glue, lem-weil-pbc-slice-site-localization,
lem-weil-pbc-site-module-sheaf-gluing, def-weil-pbc-sheafification,
def-weil-pbc-constant-sheaf, def-weil-proetale-locally-constant-sheaf.
Removed obsolete tool_uses approvals for lem-weil-pbc-site-module-sheaf-gluing and
lem-weil-pbc-slice-site-localization, retaining the other approvals in their original order.
Some remain indirect prerequisites of used library declarations; no claim is made that the
whole project can delete those modules. The main node records its actual direct dependencies.

## Where the brief, the DAG or earlier work was wrong

The retained draft described two conjunctive split holes as complete progress, omitted its
third etale-cover hole, and gave circular new-node proof dependencies. Those splits were never
landed and are removed from this delivery. The DAG's intrinsic and fixed-coefficient module
interfaces are different: its finiteLocalSystemsType cannot be applied directly to this F.
The existing fixed-coefficient open-locus theorem supplies the same decomposition instead.
The finite-set restriction in the existing uniform-model proof was stronger than needed:
finite generators suffice for both equalizer detection and local lifting. Empty schemes,
empty overlap schemes, zero models, zero rings, and empty generating sets are covered in Lean.

Used tool nodes from the comparison unit: lem-sf-proetale-model-type-opens and
lem-sf-proetale-comparison-counit-localization, plus the locally-classical etale-section theorem
inside the uniform helper. Their precise fixed-coefficient signatures avoid recreating ringed
module equivalences. Any required tool_uses approvals are left to the maintainer.

## New nodes

- `det-pe-finite-local-systems-etale-cover`: proved etale trivializing cover with the original
  finitely presented models, strictly the cover-construction part of the twist.
- `det-pe-uniform-finite-type-model-etale-cover`: proved fixed finitely generated model descent,
  with explicit finite-generator image/equality arguments. No remaining obligation.

The existing finite-model helper node now records specialization of the latter theorem.
Blueprint search for finite/local-system variants returned no existing node for this stronger
fixed-coefficient finite-type statement; the current twist detail gives its source argument.
All search records are actual launcher search receipts.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
