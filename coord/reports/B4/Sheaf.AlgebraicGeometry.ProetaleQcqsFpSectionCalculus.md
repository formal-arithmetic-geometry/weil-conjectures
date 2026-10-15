## What changed

Proved `AlgebraicGeometry.proetale_qcqs_fp_section_calculus`, with its existing signature
unchanged. The section calculation uses finite affine refinements, qcqs pullbacks, local
representatives for sheafification, finite filtered cocones, and sheaf gluing. The Hom
calculation applies internal Hom continuity and then the section calculation at the terminal
object. Both eventual-equality clauses use the actual colimit coprojections.

Added two fully proved modules:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteGlobalPresentationInternalHomColimit`:
  internal Hom from a globally finitely presented module preserves filtered colimits.
  The proof constructs the unit/free internal Hom isomorphisms, proves first-variable finite
  limit preservation using slice restriction and Yoneda, and applies exact filtered colimits
  to the opposite of the presentation cokernel cone.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteFinitePresentationInternalHomColimit`:
  passes from finite global presentations to local finite presentations. Restriction commutes
  with colimits and internal Hom, and restrictions to a covering family detect isomorphisms.

All new imports in the existing item are proof-only. The two new modules publicly import
only the interfaces used by their statements. Updated the existing theorem's proof docstring
and DAG route, and added the two matching auxiliary nodes. No existing definition, statement,
visibility, or other group's module was changed. No change record or forced adaptation is needed.

Repair of the landing-tools return at `e5da88ea2`: made every category, ring and module
binder explicit on the two private lemmas `PresheafOfModules.SiteFinitePresentation.map_id_apply'`
and `PresheafOfModules.SiteFinitePresentation.homObjUnitInvApp_app_one`. Their binders require
`C : Type (u + 1)` with `[Category.{u} C]`, whereas the corresponding source-library lemmas
require `C : Type u` with `[Category.{u} C]`. Thus their elaborated types differ despite the
previously identical statement text after the inherited variables. This uses the return's
explicit-binder remedy. Added docstrings explaining the distinction; no proof body, import,
or public theorem signature changed. The second reading below records the earlier delivery.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.proetale_qcqs_fp_section_calculus`.

Also proved, without holes:
`SheafOfModules.internalHom_preserves_filteredColimit_of_finitePresentation` and
`SheafOfModules.internalHom_preserves_filteredColimit_of_isFinitePresentation`.

There are no remaining `sorry` declarations in any of the three delivered modules, and no
new holes were added. The private constructions contain no postponed proofs. This is a proof,
not a decomposition leaving obligations for another worker. Empty finite presentations and
empty covers are included; filteredness supplies an index in the latter case. The final
single-file compiles succeeded without warnings: approximately 19.2 s, 26.9 s, and 12.8 s
for the finite global presentation, site reduction, and original module respectively.
Explicit `#print axioms` checks on all three public theorems show exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no transitive postponed proof. The required
`deliver3.py --no-push` dry run checked every delivered declaration and printed OK:
compiles and passes preflight except for the second reading, which the second reader writes.
Nothing was pushed.

Repair validation: all three modules compiled again without warnings in 29.4 s, 38.9 s,
and 19.8 s, respectively. The scratch `UniverseProbe.lean` deliberately tries the existing
`PresheafOfModules.map_id_apply'` and `PresheafOfModules.homObjUnitIso` at the site's
universes. Both attempts report a type mismatch: the source requires morphism universe
`u + 1` when the objects and modules are in universe `u + 1`, whereas this site has
morphism universe `u`. The probe is outside the delivered `lean/` tree.
Reran `tools/import_prune_check.py` on `FiniteGlobalPresentationInternalHomColimit`
as a new module against the repository: exit status 0, with no duplicate-statement finding.

## No longer needed

Removed these imports from the original item:

- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`
- `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`
- `Sheaf.Paper.SiteSheafificationSectionsLocal`
- `Sheaf.Paper.SiteRestrictionExact`
- `Sheaf.AlgebraicGeometry.ProEtaleQcqsSiteLimits`

The old proof route no longer needs these DAG lemmas as proof dependencies:

- `lem-weil-pbc-qcqs-morphism-permanence`: use Mathlib quasi-compact/quasi-separated
  morphism permanence directly.
- `lem-weil-pbc-proetale-qcqs-site-limits`: the proved source-library
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale` supplies the pullbacks and
  preservation by the forgetful functor directly.
- `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`: the section argument uses
  the sheafified presheaf colimit directly. The finite global presentation auxiliary uses
  Mathlib's exact filtered colimits for abelian groups and sheaves.
- `lem-pc-sites-sheafification-underlying-sets`: use Mathlib's locally bijective
  sheafification comparison directly.
- `lem-weil-pbc-site-sheafification-sections-local`, module
  `Sheaf.Paper.SiteSheafificationSectionsLocal`: local surjectivity/injectivity of the
  sheafification unit gives the required assertions without this generic packaged statement.
- `lem-weil-pbc-site-restriction-exact`, module `Sheaf.Paper.SiteRestrictionExact`:
  slice restriction preservation is proved via its abelian left adjoint and the module
  forgetful functor; first-variable left exactness follows from Yoneda.
- `lem-weil-pbc-filtered-colimits-commute-finite-limits`: use Mathlib's exact-colimit
  instance and an explicitly compared finite cone.
- `def-weil-sheaf-of-modules-category`: remains a statement dependency and is used through
  the internal Hom auxiliaries; the original item's proof no longer cites it directly.
- `def-weil-size-convention`: remains a statement dependency; the proof works in the fixed
  universes of the unchanged Lean signature without a separate universe-enlargement step.

The second reading also removed two redundant proof imports from
`FiniteGlobalPresentationInternalHomColimit`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`
is already publicly imported through `Quasicoherent` and `Generators`, and
`Mathlib.CategoryTheory.Limits.Yoneda` through `Limits.Preserves.FunctorCategory`.

The current second reading removed ten further redundant proof imports, all available
through retained public import paths:

- From the item: `Mathlib.CategoryTheory.Sites.PreservesSheafification`,
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`, and
  `Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered`.
- From the finite global presentation auxiliary:
  `Mathlib.CategoryTheory.Sites.CoverLifting`,
  `Mathlib.CategoryTheory.Limits.Preserves.Opposites`,
  `Mathlib.CategoryTheory.HomCongr`,
  `Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory`,
  `Mathlib.CategoryTheory.Limits.Preserves.Limits`, and
  `Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels`.
- From the site auxiliary: `Mathlib.CategoryTheory.Sites.CoverLifting`.

These redundant direct imports remove no further dependency nodes or modules from the
import closure. All existing public imports remain byte-for-byte unchanged.

These are cuts from this proof route; other parents may still need the old modules. Existing
statement dependencies remain unchanged, and no blueprint unit's realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery hid the universe distinction of two private lemmas in section variables,
so the textual duplicate-statement check could not see it. Both lemmas now state those binders
explicitly. Their source counterparts cannot be substituted at these universes; a scratch
compiler probe tests this directly. The general additivity lemma from the same source module
continues to be imported and reused.

No false statement was found. The eight-step plan is mathematically sound, but its final local
morphism gluing is unnecessary once internal Hom continuity is proved on a general site:
apply the already proved section theorem to internal Hom instead.

The source-library unit/free internal Hom and finite-presentation kernel results cannot be
applied directly in the required universes: the unit/free constructions specialize to a
category whose object and morphism universes coincide, while the pro-etale site has objects
in `Type (u + 1)` and morphisms in universe `u`. The existing finite-presentation kernel
result also specializes to opens of a topological space. The delivery reuses the general
presheaf additivity and iterated-slice isomorphisms, and supplies the missing universe-correct
unit/free calculations and Yoneda argument as proved private helpers. No source definition
or signature had to be changed.

LeanSearch returned an Internal Server Error; both new nodes record its unavailability,
and Loogle, LeanFinder, and grep searches were completed.

The actual slice module restriction includes restriction of scalars along the identity.
An explicit componentwise identity isomorphism to pure presheaf restriction avoids expensive
unfolding during naturality proofs. Each delivered module compiles independently below the
60-second limit.

## New nodes

`lem-weil-pbc-finite-global-presentation-internal-hom-colimit`, in
`dag/nodes/sec-proper-base-change/`, attaches the fully proved finite global presentation
auxiliary. Its proof is the finite-free and kernel part of Stacks Tag 0GMZ. It has no hole.

`lem-weil-pbc-site-finite-presentation-internal-hom-colimit`, in the same directory, attaches
the fully proved covering-family reduction from Stacks Tag 0GMZ. It has no hole. Both nodes
carry the exact Lean declaration signatures, source, proof steps, dependency lists, searches,
and the original item's chapter and unit.

## Earlier second reading (a previous round; superseded)

1. Compared the original module with the repository version. Its sole existing declaration's
   entire signature is byte-for-byte identical; all five public imports are unchanged. The
   existing node changes only `proof`, `proof_deps`, and `proof_origin`. The other two modules
   and nodes are new. No existing definition, visibility, or statement was changed.
   Verdict: pass; no change record or forced adaptation is required.
2. Read all three modules, including every private construction. Compiled all three in import
   order without errors or warnings (22.0 s, 27.0 s, 13.4 s). Searched all delivered Lean for
   forbidden constructs and holes: none. Independently compiled a scratch axiom check of the
   three public theorems; each reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
   Every constructed object has an explicit construction or a proved universal property.
   Verdict: pass; one original hole closed, zero holes added, zero split-off holes remain.
3. Neither new theorem is an unproved restatement: both are completely proved, with different
   roles (finite global presentation and restriction to a presentation cover). Checked zero
   generators, zero relations, empty covers, and filtered categories with parallel arrows.
   The source [Stacks Tag 0GMZ](https://stacks.math.columbia.edu/tag/0GMZ) gives precisely the
   restriction, finite-free, and kernel argument. Independent searches used the alternative
   terms "sends cokernels in the first variable to kernels" (LeanFinder),
   `"homFunctor", "PreservesFiniteLimits"` (Loogle), and kernel/cokernel and filtered internal
   Hom patterns (grep). No applicable existing continuity theorem was found. Read the existing
   topological-space continuity/kernel statements and the universe-restricted unit theorem;
   they do not apply to this site's universes. Verdict: pass.
4. Checked the proof from the original theorem downward. Local sheafification representatives,
   finite affine refinements, synchronization by filtered wide spans, and gluing implement
   [Stacks Tag 0738(4)](https://stacks.math.columbia.edu/tag/0738); the final natural isomorphism
   uses the actual colimit coprojections in both equality clauses. No shorter applicable
   library route was found. Each public import supplies a statement interface; new proof
   imports are plain imports. Removed two redundant proof imports in the global-presentation
   module and recompiled it cleanly (20.9 s). Compared the full old/new dependency sets and
   completed `No longer needed` with the two omitted definition nodes. The item's node is an
   auxiliary below the unit; none of the statement or step nodes in
   `dag/units/sk-thm-properbasechange.json` is removed or bypassed. Verdict: pass.
5. Compared all three nodes with the Lean arguments, checked every referenced dependency exists,
   and checked each `proof_deps` is exactly the union of its proof steps' `uses`. Both new
   `lean.statement` fields match their Lean signatures verbatim. Source, proof origin,
   creation, searches, blueprint origin, chapter, and unit fields are present and appropriate.
   Verdict: pass.

Second-reading changes: removed the two redundant proof imports listed above, completed the
pruning report, and added this independent review. No proof body or theorem signature needed
repair. The delivery is one original theorem proved out of one, with two additional proved
auxiliaries and no remaining holes. The required delivery dry run and its axiom probe provide
the final checks of the edited set.


## Second reading by B4

1. Compared every delivered module with the shared repository. The item is the only
   existing module; its original theorem signature is byte-for-byte identical, as are
   its five public imports. The other two modules are new. The existing node changes
   only `proof`, `proof_deps`, and `proof_origin`; no definitions, existing statements,
   visibility, or another group's files change. No change record is required.
   Verdict: pass.
2. Read all three modules, including the private constructions.
   Independently compiled the complete delivery in import order: no errors or warnings
   (31.7 s, 44.7 s, 28.4 s). A fresh scratch copy of each module with its public theorem's
   `#print axioms` appended also compiled (27.5 s, 35.1 s, 15.0 s); all three use exactly
   `propext`, `Classical.choice`, and `Quot.sound`. No forbidden construct or `sorry`
   occurs in the delivered Lean. Every private definition explicitly constructs its
   data; none chooses an arbitrary witness from an unproved existence theorem.
   Independently reran `UniverseProbe.lean`: the two expected type mismatches confirm
   that the upstream unit calculation cannot serve the site's unequal universes.
   Read the return at `e5da88ea2` and verified both repaired private lemmas now expose
   their distinct category, ring and module binders explicitly. Verdict: pass.
3. No split-off statement remains unproved. Both new public results are fully proved
   components of the argument. Checked empty generators, empty relations, empty covers,
   and general filtered categories with parallel arrows: finite biproducts, filtered
   nonemptiness, and `wideSpan`/`coeqHom` handle these cases. Read
   [Stacks Tag 0GMZ](https://stacks.math.columbia.edu/tag/0GMZ): the restriction, unit,
   finite-free, kernel, and exact-colimit steps match its proof. Independent searches
   used Loogle (`"homFunctor", "PreservesFiniteLimits"`, zero hits), LeanFinder
   (internal morphisms out of finite presentations and filtered direct limits on a
   Grothendieck site), and local grep for Hom/presentation/colimit variants. The
   LeanFinder results concern ind-objects and categorical finite presentability;
   none supplies the needed sheaf-module continuity. Read the existing
   `FinitePresentationHomColimit` and `HomFinitePresentationKernel`: they apply to
   topological spaces, and the former is still open. Read `InternalHomUnit`: its unit
   section requires coincident universes, while its general additive lemmas are reused.
   No applicable duplicate theorem was found. Verdict: pass.
4. Read the proof from the item downward. The finite affine refinements and qcqs
   overlaps justify finite gluing; local sheafification representatives and eventual
   equality give section preservation. This implements
   [Stacks Tag 0738(4)](https://stacks.math.columbia.edu/tag/0738). The Hom part applies
   the proved site continuity result, then section evaluation at the terminal object.
   Both equality clauses concern the actual cocone coprojections. No shorter applicable
   existing route was found. Checked public import paths and removed ten redundant
   proof imports, enumerated in `No longer needed`; the retained public imports still
   supply each statement's interfaces. The pruning report accounts for all nine old
   proof dependencies removed from the original node. The auxiliary is below the unit
   level; none of the statement or step nodes in `sk-thm-properbasechange.realized` is
   bypassed. The edited set compiled cleanly again (24.9 s, 32.3 s, 14.2 s). Verdict: pass.
5. Checked all three nodes against the Lean arguments. Every referenced dependency
   exists, and each `proof_deps` is exactly the union of the proof steps' `uses`.
   Both new `lean.statement` fields match their signatures verbatim. Their source,
   creation, blueprint origin, searches, chapter, and unit fields are present.
   Corrected the existing node's description of the terminal-section equivalence:
   restriction sends global morphisms to sections, and evaluation at terminal arrows
   recovers global morphisms. The former text incorrectly called restriction the
   inverse. Verdict: pass.

Second-reading changes: removed ten redundant proof imports and corrected the DAG's
explanation of the terminal-section equivalence; updated the pruning report and added
this independent review. No Lean proof body or declaration signature needed repair.
Closed: `AlgebraicGeometry.proetale_qcqs_fp_section_calculus`, the sole original hole.
Added holes: none. Two additional public auxiliary theorems are fully proved. This is
one original theorem proved out of one, with zero split-off holes.

Final validation: `deliver3.py B4 Sheaf.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
--no-push` printed OK at dry-run commit `4826c63143`: the final three-module set
compiles, its declaration axiom probes pass, and preflight passes. Review class CODEX
reflects the two new proved modules/nodes and the repaired returned delivery.
