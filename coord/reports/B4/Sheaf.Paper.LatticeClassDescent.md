## What changed

Return repair (2026-10-16): removed the duplicate private `latticeExtension_unit`
and `latticeTensorUnit` from `LatticeGluedRationalizationIso`. The existing declarations
in `LatticeSheafBasic` are now public with identical types and bodies, and the local
rationalization proof uses that imported theorem. The tensor unit is exposed because
it occurs in the theorem's signature. See `coord/changes/lattice-tensor-unit-reuse.md`.
This supplements the earlier visibility changes recorded below and in the historical
second reading; every pre-existing public signature and data body remains unchanged.


Proved `exists_latticeClassPresentation` with its original signature. The presentation uses actual embedded image families rather than a quotient of large lattice-pair data. Constructed restriction of lattice pairs, local membership in their images, the separated image presheaf, the compatible-tuple integral module and its finite local freeness, its glued embedding, and the induced rationalization map. Effective descent and the original presentation now have complete Lean proofs from the proved local invertibility theorem.

The unclaimed module `Sheaf.Paper.LatticeSheafBasic` exposes its unchanged integral embedding and tensor map, with proved image-locality APIs. See `coord/changes/lattice-descent-embedding-api.md`. No existing public statement or data body changes.

The second reader corrected proof-only import visibility, added missing primary-theorem
proof docstrings, repaired search provenance and pruning accounting, cached existing slice
sheafification instances locally, and verified restriction naturality on unit tensors to
avoid costly definitional comparison. All old signatures and data bodies remain unchanged.

## Proved and sorry left

Return repair validation: the direct `tools/import_prune_check.py` checks for
`LatticeSheafBasic` and `LatticeGluedRationalizationIso` both exit 0. The declaration
parser reports no changed existing theorem signatures. All eight delivered modules
contain zero `sorry` or `admit`. The repair adds no holes and no new nodes. The full local compile passes without
warnings for all eight modules; the slowest file takes 47.8 seconds.

Original holes: one, `AlgebraicGeometry.ProEtale.exists_latticeClassPresentation`. Closed that hole with its original signature. New holes: zero. Sorries left in the item and all newly supplied modules: zero.

The main supporting results proved are `IntegralLatticePair.mem_image_of_locally_mem`, `IntegralLatticePair.restrict_image`, `latticeClassPresheaf_isSeparated`, `gluedLatticeModule_finiteLocallyFree`, `exists_gluedLatticeEmbedding`, `rationalizeEmbedding_unit`, `gluedLatticeRationalization_isIso`, and `exists_latticePair_of_compatible_classes` (all in `AlgebraicGeometry.ProEtale`).

In particular, `AlgebraicGeometry.ProEtale.gluedLatticeRationalization_isIso` is proved: the generic tensor comparison identifies its restrictions with the chosen local rationalizations after an integral-module isomorphism. A proved local criterion for module-sheaf morphisms then establishes its invertibility. The integral module, finite local freeness, embedding, rationalization morphism, unit formula, separatedness, effective descent, and final presentation are all proved. Every data definition is an actual construction. All eight delivery modules compile without warnings after the second-reading repairs (slowest 52.8 seconds). `#print axioms AlgebraicGeometry.ProEtale.exists_latticeClassPresentation` reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The original theorem signature was compared verbatim and is unchanged.

## No longer needed

Return repair: the duplicate private theorem `latticeExtension_unit` and duplicate
private definition `latticeTensorUnit` in `LatticeGluedRationalizationIso` are removed.
Their existing Basic declarations are reused. No additional module or import is pruned.


Against the current repository version, the item removes four proof-only imports: `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`, `Sheaf.CategoryTheory.RingedSiteModules`, `Sheaf.CategoryTheory.SiteCoveringAxioms`, and `Sheaf.CategoryTheory.SiteModuleSheafGluing`. The tensor, ringed-site, and covering APIs remain available transitively through the concrete supporting modules. The original public import `Sheaf.Paper.LatticeSheafBasic` is retained. The planned dependency `Sheaf.CategoryTheory.SiteModuleSheafGluing` is replaced by the proved compatible-tuple construction `Sheaf.CategoryTheory.SiteModuleCompatibleTuples`. The item route no longer uses `lem-weil-pbc-site-module-sheaf-gluing`: it constructs and verifies the transition maps itself. The former quotient construction is unnecessary. The old direct proof-dependency edges `def-pur-localized-ringed-site` and `def-pur-sheaf-tensor-product` are also removed from the item: their generic slice and tensor APIs remain needed transitively below the new concrete interfaces and are retained in those supporting nodes. The former direct proof-dependency edges to `def-weil-pbc-sites-and-cohomology` and `def-weil-sheaf-of-modules-category` are replaced by the concrete module APIs. These are item-route changes only; no assertion that these modules are globally unreachable is made. No unit statement or realized unit proof step is bypassed.

The second reading also removed the redundant proof import `Mathlib.CategoryTheory.Sites.CoversTop.Basic` from `LatticeGluedRationalization`; it is already available through the public locally-free API. `LatticeClassPresheaf` now publicly imports only `LatticeSheafBasic` and privately imports `LatticePairRestriction`. The rationalization-isomorphism proof privately imports the restriction API explicitly.

## Where the brief, the DAG or earlier work was wrong

The returned delivery re-proved a private Basic theorem verbatim in the isomorphism
module. The import-pruning check correctly rejected this duplication. The repair
exposes and reuses the original theorem and its tensor unit instead; the corresponding
DAG proof now records its image-classification dependency explicitly.


The planned argument was mathematically sound but did not provide usable slice tensor comparisons, restriction of finite local freeness, or local membership in an integral image. Those interfaces are now proved. A direct comparison of entire nested-slice module structures caused expensive elaboration; componentwise module isomorphisms avoid unfolding these structures repeatedly. There was no false statement and no target-signature change. The second reading found a
public import used only in proofs, missing primary-theorem proof docstrings, inaccurate
LeanSearch labels on Lean Finder results, and incomplete direct-edge pruning accounting;
these are corrected. Repeated instance synthesis and definitional comparison of chosen
tensor restriction maps also exceeded the compile limit under load and were repaired
without altering statements or component maps.

## New nodes

`lem-weil-pbc-lattice-image-locality`: injective embeddings, restriction of images, and locality of image membership; proved in LatticeSheafBasic.

`lem-weil-pbc-lattice-pair-restriction`: scalar extension commutes with slice restriction, finite local freeness restricts, and embedded images restrict; proved in LatticePairRestriction.

`lem-weil-pbc-lattice-class-presheaf`: the presheaf of represented image families and its separatedness; proved in LatticeClassPresheaf.

`lem-weil-pbc-lattice-pair-descent-data`: explicit transitions, compatible-tuple module, local identifications, and finite local freeness; proved in LatticePairDescentData.

`lem-weil-pbc-lattice-glued-rationalization`: glued embedding and scalar-extended rationalization morphism with its unit formula; proved in LatticeGluedRationalization.

`lem-weil-pbc-lattice-glued-rationalization-isIso`: the proved local invertibility theorem, in LatticeGluedRationalizationIso.

`lem-weil-pbc-lattice-pair-effective-descent`: complete proof of effectivity from the constructed module and its rationalization isomorphism, in LatticePairEffectiveDescent.

Change records: `coord/changes/lattice-descent-embedding-api.md` and
`coord/changes/lattice-tensor-unit-reuse.md`. No node is added by the return repair.


## Earlier second reading (a previous round; superseded)

1. **Unchanged interfaces — pass.** Compared both existing modules with the repository by
   `diff` and the declaration parser. `exists_latticeClassPresentation` has its original
   signature byte for byte, including the absence of a local-freeness assumption on `L`.
   Every old public declaration and every old data body in `LatticeSheafBasic` is unchanged.
   Only `pairTensorMap` and `pairEmbedding` lose `private`, exactly as declared in
   `coord/changes/lattice-descent-embedding-api.md`; their bodies are identical. The other
   six supporting modules are new. No target or file held by another group is altered.

2. **Proof and data audit.** Read all eight modules, including restriction comparison,
   common-image transitions, finite-free cover refinement, gluing through sheaf Hom,
   rationalization on unit tensors, the local isomorphism criterion, effective descent,
   and the final three presentation clauses. There is no `sorry`, added axiom, unsafe
   declaration, external implementation, or hollow definition. Local representatives are
   chosen from the actual supplied image-class subtype, whose existence property is
   proved. The tuple module is constructed explicitly. The glued embedding is chosen
   from a proved gluing theorem, and its covering formula determines it by separatedness.
   The local isomorphism proof identifies restrictions using tensor adjunction and the
   slice comparison, then invokes Mathlib's local criterion; it assumes no global rank.
   Final compile and axiom results are recorded below.

3. **New statements — pass.** No statement is left split off with `sorry`: seven new nodes
   carry proved intermediate constructions. Checked each node against its Lean hypotheses
   and conclusion. The generic injectivity assumption is discharged for the original
   coefficient map in the main theorem. Checked zero modules, varying local ranks, empty
   test spaces, and empty covering sieves: no choice requires an inhabitant of a cover,
   and the sheaf/local-isomorphism arguments still apply when an empty sieve covers.
   Repeated searches with “sheaf of submodules” and “local membership in a range”, Loogle,
   and `rg` on the library and Mathlib. Lean Finder returns local-generator APIs; Loogle
   does not know the project's finite-locally-free extension; grep finds the local
   isomorphism criterion already used. LeanSearch returns generic stack descent, which
   requires an established stack, and module/basis APIs, with no direct replacement.

4. **Route and pruning — pass after corrections.** Starting at the final presentation,
   the proof uses image classification, separated image families, and the concrete
   compatible-tuple descent API. It does not rename the main hole or assume effectivity.
   Checked `dag/units/sk-thm-properbasechange.json`: neither the item nor the pruned
   planned gluing dependency realizes a unit statement or step, and all `realized`
   entries remain unchanged. The report now names all five removed old direct dependency
   edges, distinguishing transitive slice/tensor use from removed direct edges. Removed
   the redundant CoversTop import and made the restriction API a proof-only import.
   No globally unreachable module is claimed pruned.

5. **DAG agreement — pass after corrections.** Read all eight delivered nodes and their
   recorded dependencies. The main node records the image-family route. Restriction and
   image locality support separatedness; compatible tuples support the module; gluing
   and scalar extension support its rationalization; local invertibility supports
   effective descent. `proof`, `proof_deps`, and `proof_origin` agree with these proofs.
   New nodes have the source, creation, blueprint ancestry, Lean declarations, and search
   records. Corrected records that called actual Lean Finder searches “leansearch” and
   added the separately executed LeanSearch query with its actual results. Added source
   and proof docstrings to the four supporting nodes' primary theorems that lacked them.

Second-reading changes: import visibility and redundancy; complete pruning accounting;
accurate search provenance plus a new LeanSearch; missing primary-theorem proof docstrings.
The second reading also added two named local instances that cache existing additive slice
sheafification and local-bijectivity instances. Profiling showed repeated synthesis of those
instances; the scratch full file then compiled in 53.0 seconds under the same load. These
helpers are proved by `infer_instance`, have no new hypotheses, and their instance attributes
are local to the module. The supporting modules activate the caches with `attribute [local instance]`.
The descent-data module also caches the existing strong sheafification instance on a slice
and the weak/strong sheafification and local-bijectivity instances on iterated slices.
Those four aliases are local instances there and are activated locally in the later
descent proofs; all are proved by `infer_instance`.
The restriction unit naturality proof now uses tensor extensionality and the existing
pure-tensor formulas for the two restriction maps. This avoids an expensive comparison of
the chosen maps by definitional equality. The scratch full restriction file compiled
without warnings in 41.4 seconds. Its component maps and all signatures are unchanged. The change record was refreshed against the 27 current downstream users; none
mentions the formerly private embedding or tensor-map names.
No existing declaration signature or data body changes.
No theorem statement or mathematical construction was changed or weakened.

Final second-reader verification: all eight delivered modules compiled without warnings.
The observed times were 52.8, 43.5, 7.7, 45.1, 32.3, 29.8, 12.4, and 7.0 seconds
for Basic, Restriction, ClassPresheaf, DescentData, GluedRationalization,
GluedRationalizationIso, EffectiveDescent, and the original item respectively.
A scratch copy of the original item, with explicit proof-API imports, compiled and
printed the axioms of the main theorem and seven primary supporting theorems listed
in points 2–3: each has exactly `propext`, `Classical.choice`, and `Quot.sound`; none
uses `sorryAx`. No scratch file is part of the delivery.

The required dry run exposed a further restriction-file timeout under load, after
Basic compiled in 51.6 seconds. The restriction module now also caches the existing
strong slice instance and the three weak/strong sheafification/local-bijectivity
instances on iterated slices, using four named local aliases proved by `infer_instance`.
The full scratch version compiled without warnings in 50.4 seconds while the
uncached profiled version timed out. These aliases are recorded in the restriction
node and do not alter any statement, component map, or downstream instance attribute.


## Second reading by B4

1. **Interfaces — PASS.** Compared both existing modules with the current repository by
   `diff` and the declaration parser. The target signature is byte for byte unchanged;
   the parser reports no changed existing theorem signatures in either module. All old
   data bodies are unchanged. The four declarations exposed in Basic are exactly those
   named in the two change records: `pairTensorMap`, `pairEmbedding`, `latticeTensorUnit`,
   and `latticeExtension_unit`. The six other modules are new. No target statement or
   module held by another group changes.

2. **Proofs and constructions — PASS.** Read the image-locality additions and all six
   supporting modules from the final presentation downward. All eight modules compiled
   without errors or warnings through `lcompile.py --all`, taking respectively 45.0,
   34.5, 7.5, 40.1, 26.4, 23.8, 12.0, and 7.1 seconds in import order. A scratch copy
   checked the axioms of the target and the seven primary supporting theorems: every
   result uses exactly `propext`, `Classical.choice`, and `Quot.sound`. No delivered
   module contains a proof hole or forbidden declaration. The tuple module and tensor
   maps are constructed; local representatives are chosen from proved representation
   properties, and the glued embedding is chosen from a proved gluing theorem.

3. **Supporting statements — PASS.** There are no split-off holes. The seven supporting
   nodes state proved intermediate constructions, each genuinely part of the descent
   argument. In particular, local invertibility is proved by restriction and the local
   isomorphism criterion, rather than assumed under another name. Zero modules, varying
   ranks, and empty covering sieves introduce no extra hypotheses or inhabitance choices.
   Searched the current library for subsheaves, sheaves of submodules, covering-local
   gluing, common-image equivalences, and the tensor-unit declarations. The return repair
   correctly reuses Basic's original tensor-unit naturality theorem with its unchanged
   type and proof, and removes the duplicate private declarations.

4. **Route and pruning — PASS after report correction.** The target uses represented
   image families, local image membership, explicit compatible tuples, their finite
   local freeness, and the proved rationalization isomorphism. The unit record
   `sk-thm-properbasechange.realized` is unchanged; neither the item nor the replaced
   generic gluing dependency realizes a required unit step. All removed old direct DAG
   edges are listed. Corrected the outdated claim that no imports were removed: against
   the current base, four proof imports are removed, now explicitly listed above.
   No globally unreachable module is claimed pruned. The public imports support
   statements or data; the proof-only restriction and local-isomorphism imports are
   private.

5. **DAG — PASS.** Checked every delivered node's `proof`, `proof_deps`, and
   `proof_origin` against the actual route. For all eight nodes, `proof_deps` is exactly
   the union of the proof steps' uses. The seven new nodes have the required source,
   creation, blueprint ancestry, chapter/unit, search, status, and Lean records. The
   isomorphism node explicitly records reuse of Basic's tensor-unit theorem. No new
   node or proof hole is added by the return repair or this reading.

Current second-reading changes: corrected the pruning report against the current base
and appended this review; no further Lean or DAG edit was needed. Holes closed:
`AlgebraicGeometry.ProEtale.exists_latticeClassPresentation` (one). Holes added: none.
