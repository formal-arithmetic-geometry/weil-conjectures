## What changed

Replaced the sorry in `Sheaf.AlgebraicGeometry.AffineOpenLocalizedModel` by a complete
Lean reduction. The theorem's signature and public imports are unchanged.
The proof uses the existing `exists_affine_module_complex_representative`, constructs
the termwise comparison from hT, transports pseudo-coherence through the supplied
derived isomorphism, forms the subtype of suitable localizing elements, applies
`IsCompact.elim_finite_subcover`, and enumerates the resulting finset using
`Fintype.equivFin`. It then applies the local detection theorem to the actual cover.

Two new modules isolate the remaining local arguments:
`AffineOpenPseudoCoherentLocalizationPoint` and `AffinePrincipalCoverQuasiIsoDetection`.
Their public theorems are strictly parts of the argument: the first has a fixed M
and one point, with no compactness or finite cover; the second has a fixed cover and
chain map, with no representative existence or pseudo-coherence hypothesis.
Their docstrings and DAG nodes record complete natural-language proofs and sources.
No definition, existing signature, target, or other group's module was changed.

Local compilation of the three-module set succeeded with no errors or warnings.
The statements were checked on empty U, an empty family (which forces U empty in the
detection lemma), zero rings, zero complexes, unit localizing elements, and principal
opens contained strictly inside X. They require no unit-ideal condition: the opens
cover U only. All choices of representatives occur inside existential proofs; no
arbitrary witness defines library data.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.exists_affine_open_localized_model`
(node `lem-sc-affine-open-localized-model`). There is no sorry in the item's module.

Added two holes, each the entire proof of one named public theorem:

- `AlgebraicGeometry.Scheme.affine_open_pseudoCoherent_localization_point`
  (`lem-sc-affine-open-pseudo-coherent-localization-point`).
- `AlgebraicGeometry.Scheme.affine_principal_cover_quasiIso_detection`
  (`lem-sc-affine-principal-cover-quasi-iso-detection`).

This is a decomposition, not an unconditional proof: one original hole closed,
two strictly smaller holes added, net holes minus one. The finite-cover construction,
representative comparison, pseudo-coherence transport, and combination of the two
local statements are proved in Lean. The affine representative and principal-model
interfaces may themselves depend on previously recorded holes, as stage 3 permits.

## No longer needed

Removed the item's direct proof imports:

- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`.
- `Sheaf.AlgebraicGeometry.AffinePseudoCoherentPrincipalModel`.

The updated parent node directly uses `lem-pc-affine-module-complex-representative`,
`def-pur-pseudo-coherent-complex`, and the two new local nodes. Its previous direct
proof dependencies `lem-pc-affine-qcoh-derived-equivalence`,
`lem-pc-affine-pseudo-coherent-principal-model`, and
`lem-weil-pbc-spec-module-tilde-sections` are no longer direct parent dependencies.
They remain needed beneath the local nodes or affine representative; this delivery
claims no whole module pruned from the targets' import closure. The whole-spectrum
`AffinePseudoCoherentLocalizationCover` and global pseudo-coherence gluing are not
imported or used: they would require pseudo-coherence on all X and a unit-ideal cover.
The unit record has no realized node at this lower level; its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The parent plan correctly identifies the mathematics, but its existing interfaces do
not supply the transport of local finite-free models from the open scheme U through
X.isoSpec, nor the natural principal-localization comparison for arbitrary chain maps.
Those are the two local arguments split off, rather than asserting that the
whole-spectrum cover theorem applies to U. The existing affine module representative
already implements the parent plan's first step and avoids repeating its equivalence
and essential-surjectivity construction.

The Stacks TeX sources are listed as obtained but absent in this local clone. Read
Stacks Tags 08EE, 08E7 and 06Z0 through their official online pages. The new proofs are
marked agent-written elaborations of the local transport and final sheafification
steps, with those source places stated. No mathematical source error was found.

Searches: LeanFinder returned general affine-local and derived localization facts;
Loogle and Mathlib grep found no exact matches for the two local statements.
LeanSearch returned Internal Server Error, recorded as unavailable. Direct searches
of Sheaf and WeilConjectures found the existing affine representative, principal-model
lemma, whole-spectrum cover lemma, private open-cover quasi-isomorphism criterion,
and derived open-restriction detection. None has either new theorem's interface.
Blueprint-wide searches for pseudo-coherent localization and quasi-isomorphism
principal found no duplicate. The official sources used are
https://stacks.math.columbia.edu/tag/08EE,
https://stacks.math.columbia.edu/tag/08E7 and
https://stacks.math.columbia.edu/tag/06Z0.

## New nodes

`lem-sc-affine-open-pseudo-coherent-localization-point`, in
`lean/Sheaf/AlgebraicGeometry/AffineOpenPseudoCoherentLocalizationPoint.lean`, gives one
pseudo-coherent localization near a specified point of U for a fixed module complex.
Its proof transports a local finite-free model and applies the existing principal
model theorem; no finite-cover or global-representative conclusion is moved into it.

`lem-sc-affine-principal-cover-quasi-iso-detection`, in
`lean/Sheaf/AlgebraicGeometry/AffinePrincipalCoverQuasiIsoDetection.lean`, detects the
invertibility of a fixed derived restricted map from quasi-isomorphisms on a supplied
principal-open cover. Its proof is natural principal-localization comparison, exact
tilde, and local detection on homology sheaves. It neither constructs a cover nor
uses pseudo-coherence. Its local sheaf-isomorphism criterion is a generic tool from
another unit; no step of the Serre-duality unit is replaced by that tool.

No change record is required: existing interfaces and public imports are unchanged.

## Second reading by Y2

1. **Interface and accidental changes — PASS.** Read all three modules and diffed
   the existing module against the repository. Its only changes are the three plain
   proof imports replacing two plain proof imports, and the body of
   `exists_affine_open_localized_model`. The complete declaration signature,
   docstring, universes, instances, visibility and public imports are byte-identical.
   Both other modules are new. No definition or target changes, no forced
   adaptations and no change record. Checked all three recorded Lean signatures
   verbatim against the actual declaration headers (including their named arguments).

2. **Proof and trust — PASS as a decomposition.** Compiled the complete three-module
   set using lcompile.py: the pointwise module, detection module and item took
   approximately 5.4, 5.5 and 25.5 seconds, with no errors or warnings. Read the
   representative comparison direction: Q(c) composed with eM.symm gives Q(T M)
   to E'. The restriction of that isomorphism composed with eU goes to E; further
   restriction composed with each hP gives exactly the pseudo-coherence witnesses.
   The subtype retains both containment in U and localized pseudo-coherence;
   compactness extracts a finset, and the equivalence with Fin enumerates every
   member, so hcover has no surjectivity gap. The detection theorem is applied to
   this actual family. Scratch-copy #print axioms checks for all three public
   declarations returned only propext, Classical.choice, Quot.sound and sorryAx.
   The sole two delivered sorries are the entire named public local theorems;
   there is no axiom, unsafe, opaque, implemented_by, extern or hollow definition.
   Temporary probe files were removed. The original hole is closed syntactically,
   but its dependencies remain open; this is not an axiom-free proof of the item.

3. **Split statements, sources and duplication — PASS after a prose repair.** Read
   the official [08EE](https://stacks.math.columbia.edu/tag/08EE),
   [08E7](https://stacks.math.columbia.edu/tag/08E7) and
   [06Z0](https://stacks.math.columbia.edu/tag/06Z0) pages and the actual declarations
   of the affine representative, principal model, scheme-isomorphism equivalence,
   tilde adjunction, quasi-coherent kernel and local sheaf-isomorphism criterion.
   The pointwise statement fixes M and one point; its hypothesis supplies a genuine
   local finite-free model on U. Transport the neighbourhood and its model to
   Spec Gamma(X), refine by a principal open, and the principal-model theorem
   applies with precisely its bound, ranks and model isomorphism. The extra
   derived-category universe is independent, as its stated interface allows.
   Detection fixes F, M, alpha and a supplied cover, uses no model construction,
   and follows from the natural localization comparison and exact tilde followed
   by local homology detection. Neither theorem restates the parent conclusion.
   Empty U makes the pointwise claim vacuous; an empty detection family forces U
   empty. Zero rings/complexes, f=1, ranks zero and opens strictly smaller than X
   introduce no excluded case. Containment and coverage are of U, not of X;
   no unit-ideal hypothesis is silently used.

   Repeated searches with different wording: LeanFinder for finite-free local
   derived models on principal neighbourhoods, and for homology detection by
   localized associated-sheaf complexes; Loogle `"tilde", "restrict"`; Mathlib grep
   `IsPseudoCoherent.*(over|iso)|basicOpen.*QuasiIso`. These found only generic
   homology/localization facts or finite-type sheaf facts, no exact match.
   Direct rg searches in Sheaf and the upstream WeilConjectures checkout found
   the whole-spectrum localization cover and private open-cover detection, and
   inspected AffinePrincipalSheafComplexTransport in full. Its localization
   comparison is private and its public conclusion constructs a finite-free
   sheaf complex from an existing model, so it supplies neither new interface.
   Closing either remaining theorem requires substantial open-site transport,
   not a few-minute application of an existing public statement.

4. **Top-down route and pruning — PASS.** The item uses the existing affine module
   representative instead of reproving essential surjectivity. Its remaining Lean
   argument is isomorphism transport, finite-subcover extraction and application
   of two local statements, all below the unit level. The original node's three
   obsolete direct proof dependencies are all listed under No longer needed:
   affine derived equivalence, principal model and tilde sections. They remain
   needed transitively, so no entire module is claimed pruned. Statement imports
   stay public; the imports used only by the proof or the recorded open proof
   plans are plain. Opened sk-thm-picard-duality.json: realized.statement and its
   step realization are empty, and the imported lower-level tools do not replace
   the Serre-duality unit's route. No unit record was changed.

5. **DAG alignment — PASS after a prose repair.** Only proof, proof_deps and
   proof_origin differ on the existing node. Its four steps match the four
   substantive blocks of the Lean reduction; proof_deps is the union of their
   uses. Both new nodes have self-contained statements matching the Lean headers,
   docstring proofs, sources, creation and Lean records, searches, blueprint
   origin, chapter and unit. Checked the statements of the cited dependencies,
   not merely their names. The kernel dependency asserts quasi-coherence of a
   sheaf kernel, rather than tilde preserving kernels by itself. Expanded the
   detection node's second proof step and its new theorem docstring: Gamma
   preserves kernels as a right adjoint; the affine unit identifies global
   sections of tilde modules; the counit identifies the quasi-coherent kernel
   with tilde of that module kernel, naturally in the kernel arrow. Together with
   colimit preservation this proves exactness. No new dependency or hole is
   introduced by this repair.

**Changes by this reader:** expanded that kernel-preservation justification in
AffinePrincipalCoverQuasiIsoDetection's docstring and matching DAG proof step;
added this independent review and repeated search evidence. No Lean proof,
interface, import or hole count changed. Final accounting remains one original
hole closed, two holes added: a decomposition with net closure progress -1.
