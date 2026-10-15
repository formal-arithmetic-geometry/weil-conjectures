## What changed

Repair of the landing refusal at head `42465774c`: generalized the two private transport
helpers in place, as the return permits. `fp_of_iso` now applies to `Mod C R` for any abelian
monoidal category with additive tensor and right-exact `R ⊗ -`, rather than only pro-etale
abelian sheaves. `lfp_of_iso` now applies to any closed symmetric monoidal Grothendieck
abelian coefficient category `A`, rather than just `Ab`. Every category binder is explicit;
the proofs compose the presentation isomorphism and transport each member of the cover.
These are strict mathematical generalizations, not renamings or changes of variable names.
The existing specialized lemmas in `TwoColimit` are private, and that module imports this
item, so importing those lemmas here would be both inaccessible and cyclic. No downstream
module or public signature is changed by this repair, and no shared-module import is added.

Proved both declarations in `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre`, with their
original signatures unchanged. All new helpers are private and proved. The second reading
removed two unused public wrapper imports; the four public imports needed by the statements
remain public.
No other Lean module is changed, and no intermediate theorem with `sorry` is added.

The proof implements the existing seven-step argument: inverse-image transport of finite
presentations, fibre-product refinement of stratifications, existing coefficient local
triviality, finite-matrix cokernels, split-epimorphism kernel presentations, image factorization,
and split extensions. Local triviality is used only on the noetherian strata; covering schemes
are never assumed noetherian.

Local splitting is proved here from `Sheaf.isLocallySurjective_iff_epi'`. Sections at the terminal
site object give maps from the abelian unit using integer multiples and the sheafification
adjunction. Localization restriction identifies their local lifts with inverse-image maps;
`Mod.regularLift` makes them linear. All basis vectors are lifted simultaneously by applying the
one-generator construction to a finite biproduct of the epimorphism. The existing smallness
instance for `propQCPrecoverage` produces a cover indexed in `Type u`. The argument is adapted
from the already proved source `ProEtale/Adic/Extension.lean`, without importing that module.

For finite coefficients, an explicitly constructed continuous ULift ring-sheaf isomorphism
allows the existing local-triviality theorem to apply in every scheme universe. For closure
coefficients, the invertible coefficient comparison converts `CondensedRing.upperStar` to the
ordinary `mapMod` pullback used by the constructibility predicate.

Added proof imports: `Mathlib.Algebra.Field.ULift`, `Mathlib.CategoryTheory.Sites.EpiMono`, and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`. Updated only
`proof`, `proof_deps`, and `proof_origin` of the item's existing DAG node to describe the Lean
argument and its actual dependencies. The proper-base-change unit's statement and steps stay.

## Proved and sorry left

Repair validation: the generalized helpers and both public theorems compile cleanly through
`lcompile.py` (18.5 seconds). The return's `import_prune_check.py` check is rerun against the
repository baseline and passes (exit code 0). No holes were introduced or moved by the generalization.
The required delivery dry run also passes with review class CODEX; nothing was pushed.

Closed both original holes:

- `AlgebraicGeometry.ProEtale.isConstructibleModuleObject_serre_padicSubfield`.
- `AlgebraicGeometry.ProEtale.isConstructibleModuleObject_serre_padicAlgCl`.

Both belong to `lem-weil-pbc-condensed-constructible-serre`. Holes closed: 2; holes added: 0;
split off: 0. No `sorry` remains anywhere in the delivered Lean file. This is a proof from the
existing statements, not a decomposition into additional assumptions.

The existing coefficient local-triviality declarations remain dependencies:
`exists_finiteFree_cover_of_condensedField_lfp`
(`lem-weil-pbc-condensed-lfp-local-triviality`) and `condensedQbar_lfp_locally_free`
(`lem-weil-pbc-condensed-qbar-lfp-local-triviality`). Those modules are unchanged and their
remaining proofs are subsequent work. Existing coefficient-comparison instances from
`Sheaf.Paper.ProfinitePointPullback` also remain in the import closure.

Validation: repeated single-file compilations through `lcompile.py`, including the complete
proof with all unused direct proof imports removed, pass without warnings in about 20 seconds.
Compared each original theorem signature with the repository text: both are identical.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for
`freeEpiLocalSplitting` and `lfp_serre_of_locally_free`; the two public results still report
`sorryAx` through the unchanged upstream local-triviality/coefficient dependencies, as expected.
The empty-basis case is covered by finite-biproduct constructions; empty strata and covers use
the same existing cover and stratification operations without nonemptiness assumptions.

## No longer needed

Removed these direct imports (the last two were unused public imports):

- `Sheaf.CategoryTheory.SitePullbackAbelianExact`.
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`.
- `Sheaf.CategoryTheory.SiteCoveringsCommonRefinement`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`.
- `Sheaf.CategoryTheory.RingedSiteModules`.

Removed direct proof-dependency edges to `lem-weil-pbc-site-pullback-abelian-exact`,
`lem-weil-pbc-module-sheaves-colimits-forgetful`,
`lem-weil-pbc-site-coverings-common-refinement`, and `def-weil-sheaf-of-modules-category`.
The source-library exactness and internal-module forgetful APIs already supply the required
properties. Covers are combined directly using `bind` and `pullback₁`, and finite simultaneous
basis lifting needs no separately stated finite-cover-refinement lemma.

The current repository baseline also directly imports `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`;
that unused direct wrapper import is absent from this delivery. The inverse-image dependency
node stays: the actual source inverse-image API is supplied by the retained imports.

These are direct-edge removals. Some removed modules remain reachable through the unchanged
local-triviality dependencies; no claim is made that all seven leave the global targets closure.
A source-graph comparison finds `Sheaf.CategoryTheory.SiteCoveringsCommonRefinement` removed
from this item's import closure, and the newly reached, sorry-free `Mathlib.Algebra.Field.ULift` module. The global `TargetsCheck` closure
still reaches it elsewhere, so this delivery does not claim a globally pruned module.
No node realizing a statement or step of the proper-base-change unit is bypassed. The proof
uses the existing `Scheme.Stratification`, not the separate `LocallyClosedStratification`
wrapper, and internal `Mod`, not `ringedSiteModules`; those two unused direct imports were
removed during the second reading. Their modules remain transitively reachable. The
conceptual stratification dependency stays because the common-refinement argument uses
exactly that finite locally closed partition notion on the noetherian base.

## Where the brief, the DAG or earlier work was wrong

The previous delivery duplicated the exact `Ab`-specialized signatures of the private
`finitePresentation_of_iso` and `localFinitePresentation_of_iso` in the downstream
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`. The previous second
reading below predates this landing refusal. This repair uses the permitted in-place
generalization: arbitrary internal-module categories for finite presentation and arbitrary
coefficient categories for local finite presentation. It retains the original public
Serre statements, dependency route, and all previous pruning.

The planned forgetful theorem is about `SheafOfModules`; this item uses internal `Mod` objects
in abelian sheaves. The proved source `Mod.forget` and `Functor.mapMod` exactness APIs apply
directly, so no new equivalence or category is needed. The generic site-pullback theorem likewise
need not be instantiated: exactness of this specific source inverse image is already proved.

The source `ProEtale/Adic/Extension.lean` lifting argument uses legacy inverse-image modules
whose notation declarations conflict with the current finite-coefficient inverse-image API.
Porting its abelian-unit argument locally avoids that import conflict. Its lift is generalized
to arbitrary ring objects, rather than transferring a constant-coefficient theorem unchanged.

The existing finite-field local-triviality theorem places the field in the scheme universe;
finite intermediate fields here live in `Type 0`. The explicit continuous ULift isomorphism
resolves this mismatch without changing either theorem or imposing a universe restriction.
The small-cover-index requirement also needs the existing `Precoverage.Small` restriction;
a raw covering sieve gives an index in `Type (u + 1)`.

Searches for a shorter complete theorem used LeanFinder, Loogle, the provided grep service,
and repository/Mathlib searches. No complete Serre-closure match was found. The useful existing
proof was the local-lifting construction described above. No definitions or statements were
changed. The public-import cleanup is recorded in
`coord/changes/CondensedConstructibleSerreImports.md`; no forced adaptation is required.

## Earlier second reading (a previous round; superseded)

1. **Interfaces and scope — pass.** Independently read the entire 1007-line submitted
   module, the repository version, their textual diff, and both versions of the node.
   Extracted each existing theorem header through `:= by`: both headers are byte-for-byte
   identical. The scheme universe, noetherian-space hypothesis, prime hypothesis, arbitrary
   finite intermediate field, all morphisms, both kernel/cokernel conclusions, and the
   short-exact extension conclusion are unchanged. There are no changed existing definitions
   or other delivered modules. The four retained public imports supply the predicates,
   coefficient rings, finite-field indexing, and short-exact complexes used in the signatures.
   Removed the unused public imports of `LocallyClosedStratification` and `RingedSiteModules`.
   `tools/downstream.py --uses` found no `ringedSiteModules` user and only a direct import of
   the stratification wrapper in the downstream descent module, which already imports it
   itself. No statement or definition is changed. The preflight requires a record even
   for removed unused public imports, so the export cleanup is documented in
   `coord/changes/CondensedConstructibleSerreImports.md`, with all 11 downstream users.

2. **Proof and axioms — pass.** Independently compiled the submitted module cleanly
   (17.5 seconds), then compiled a scratch copy after the two import removals (18.2 seconds).
   The scratch copy prints axioms for all 51 named declarations, including every private
   construction. All 47 declarations preceding the coefficient specializations use only
   `propext`, `Classical.choice`, and `Quot.sound`. Only `finite_lf`, `algcl_lf`, and the two
   public results additionally use `sorryAx`, through the existing local-triviality results.
   No delivered theorem contains `sorry`; no forbidden axiom, unsafe declaration, opaque
   declaration, implementation override, or external implementation occurs. The explicitly
   constructed kernel/cokernel isomorphism, finite-biproduct isomorphism, section-to-unit
   maps, regular-module comparison, and continuous ULift coefficient isomorphism contain
   actual data and proofs. No definition chooses an arbitrary witness from an unproved
   mere-existence theorem.

3. **Split statements and small cases — pass, none split.** There are zero new nodes and
   zero new holes. Checked the proved private reductions mathematically: for a section `s`
   of an epimorphism `f`, `1 - f ≫ s` induces the inverse to
   `kernel f ≅ cokernel (f ≫ s)`; the cokernel is presented by an endomorphism of the finite
   free source. For a general morphism the proof first presents the global cokernel,
   presents its kernel via `cokernel.π`, transfers the image with `Abelian.imageIsoImage`,
   then presents the kernel of `factorThruImage`. These are proper parts of the argument,
   all proved, not renamed copies of the Serre assertion. Rank zero uses empty biproducts;
   the identity epimorphism gives zero kernel, and a split projection gives the expected
   complementary summand. Empty strata and schemes require no point or nonempty basis.
   The coefficient ULift maps are pointwise inverse ring homomorphisms, with the given
   topology and norm transported to the lifted field.

4. **Top-down route and pruning — pass after import cleanup.** Re-ran LeanFinder for
   locally finitely presented sheaf Serre closure, Loogle for local surjectivity, and grep
   for finite-presentation kernel/cokernel and locally free extension results. LeanFinder
   returned the distinct Mathlib `SheafOfModules.IsFinitePresentation` API; Loogle returned
   the local-surjectivity API used here. No complete shorter internal-module Serre theorem
   was found. Also read `ProEtaleModuleConstructiblePullback`, the source
   `ConstructibleSheaf/ProEtaleModule/DerivedCategory`, and the unit-lifting and extension
   arguments of `SixFunctors/ProEtale/Adic/Extension.lean`: its existing theorem concerns
   `AdicSheaf`, while this item concerns internal modules over pulled-back condensed rings.
   The adapted abelian-unit argument is appropriate. Each retained proof import provides
   an actually used API. The report lists all seven removed imports and all four removed
   old proof-dependency edges. Read `dag/units/sk-thm-properbasechange.json`, including its
   unchanged `realized` statement and all three steps: none is bypassed. This remains
   coefficient infrastructure below those unit steps, with no globally pruned-module claim.

5. **DAG agreement — pass after metadata correction.** Compared the node JSON fields:
   only `proof`, `proof_deps`, and `proof_origin` differ from the repository. Opened each
   retained dependency's statement and Lean or Mathlib record. The dependency set is exactly
   the union of the seven proof steps' `uses`. The finite theorem supplies the local free
   cover after ULift transport; the closure theorem supplies it after removing extension
   of scalars along the invertible coefficient comparison. `Scheme.Stratification.inter`
   gives actual fibre-product projections, and immersion embeddings establish
   noetherianity of each stratum. `Sheaf.isLocallySurjective_iff_epi'` supplies precisely
   the local section lifts. Checked the localization unit comparison and finite-biproduct
   simultaneous lift against the source argument. Crucially, local triviality is applied
   only to modules on the original noetherian stratum, including its global image and
   cokernel; the covering objects are never assumed noetherian. Marked step 4
   `elementary: false`: the fully proved local-splitting construction is substantial,
   although its ingredients are existing APIs. The recorded proof origin names that
   adapted source argument and the unchanged local-triviality dependencies accurately.

Second-reading changes: removed two unused public imports, added their required export-change
record, corrected the report's import accounting (including the newly reached sorry-free
Mathlib ULift module), and marked the local-splitting DAG step non-elementary. No proof body, existing
signature, definition, unit, or additional module was changed. Holes closed remain 2;
holes added remain 0; split off remains 0.

## Second reading by B3

1. **Interfaces and scope — pass.** I compared the delivered module with the repository
version. The two public theorem signatures are byte-for-byte unchanged, and no target or
definition is altered. The only interface edits are the two unused public import removals
recorded in `coord/changes/CondensedConstructibleSerreImports.md`.

2. **Proof and axioms — pass.** I compiled the delivered module with `lcompile.py`; it
completes without errors or warnings. The file has no `sorry`, forbidden declarations, or
hollow definitions. The scratch axiom check reports only the permitted axioms for the new
private proof declarations; the public results inherit `sorryAx` only through unchanged
upstream local-triviality declarations.

3. **Split statements and small cases — pass.** No statements were split off and no new
nodes or holes were added. The finite-biproduct constructions include rank zero, and the
kernel, cokernel, empty-stratum, and empty-cover cases are handled by the same universal
property arguments.

4. **Top-down route and pruning — pass.** The proof follows the unit route: inverse-image
transport, common stratification, coefficient local triviality, finite presentations,
local splitting, image factorization, and split extensions. I checked the recorded searches
and removed only imports and proof dependencies unused by the actual proof. No unit statement
or realized unit step is bypassed.

5. **DAG agreement — pass.** The delivered node changes only `proof`, `proof_deps`, and
`proof_origin`; these describe the declarations and APIs used by the Lean proof. The node
retains the original statement, unit, chapter, and source metadata, and the dependency list
is the union of the proof steps' actual uses.

The second reading changed the report by adding this section and corrected the import and DAG
accounting already recorded above. No Lean proof, signature, definition, unit, or node
statement was changed during this reading.
