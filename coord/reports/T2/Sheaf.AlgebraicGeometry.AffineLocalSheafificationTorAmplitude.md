## What changed

Proved `AlgebraicGeometry.Scheme.finiteTorAmplitude_of_affine_sheafification_of_open_tor`
with its signature and all original public imports unchanged. Added proof-only imports of
`AffineTorAmplitudeCriterion`, `OpenImmersionTensorVanishingTest`, and the source exact
derived-functor comparison module. The repair replaces the direct `KFlatResolution` import
with non-public `import all Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal`.

The proof constructs the comparison between restricting the derived pullback to W along
`j = hU.isoSpec.inv ≫ S.homOfLE hUW` and the termwise tilde complex of P. It uses a K-flat
representative to compare derived pullback with exact restriction, the composition of
restriction functors, the given representing isomorphism, and explicit cancellation of
the affine over equivalence and spectrum isomorphism. Testing the original interval on
`j_*G` then gives the sheaf-side premise of the existing affine Tor-amplitude criterion.

Added a proved, general single-degree theorem
`AlgebraicGeometry.openImmersion_tensor_vanishing_test` in its own module. Its proof
restricts the K-flat witness, uses the monoidal inverse tensorator and the open-immersion
counit, and computes tensor with a degree-zero sheaf through the proved source
`CochainComplex.mapBifunctorSingle₂Iso`. No new unproved statement or definition is added.
Shared sheaf categories are typed explicitly to avoid the separate `Scheme.Modules`
category instances. No existing signature or visibility changes; no forced adaptations.

Repair of the refused landing: removed the two duplicate private declarations
`AlgebraicGeometry.Scheme.exists_kFlat_model` and
`AlgebraicGeometry.Scheme.open_pullback_model_iso`. The main proof now calls the exact
existing `AlgebraicGeometry.exists_kFlat_model` and
`AlgebraicGeometry.open_pullback_model_iso` from `TorAmplitudeOpenLocal`. Their private
visibility requires `import all`; ordinary import cannot resolve their names. No upstream
module, signature, visibility, or proof was changed. The import-direction check permits
this dependency. The delivery tool rebases the sandbox changes on freshly fetched
`origin/sheaf-dag` during the dry run. The repaired main module compiles through
`lcompile.py` in 31 seconds without warnings, and `tools/import_prune_check.py` now
passes (exit 0), including the exact check that refused the previous landing.

## Proved and sorry left

Closed the item's only hole:
`AlgebraicGeometry.Scheme.finiteTorAmplitude_of_affine_sheafification_of_open_tor`
(node `lem-pc-affine-local-sheafification-tor-amplitude`).

Also proved the new theorem `AlgebraicGeometry.openImmersion_tensor_vanishing_test`
(node `lem-pc-open-immersion-tensor-vanishing-test`). No holes added; no `sorry` remains
in either delivered module. This is a proof from existing library declarations, not a
claim that every imported theorem is free of transitive `sorry` dependencies.

## No longer needed

All five original public imports remain: they provide the unchanged statement and its
category instances. Removed the original proof-only imports
`Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses` and
`Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses`. No additional unused
proof import remains.
The repair removes the now-redundant direct
proof import `Sheaf.Algebra.Homology.KFlatResolution`; it is available through the reused
module. Both duplicate private declarations are removed, not renamed or restated.

The proof does not need the following original planned dependencies:

- `lem-pc-derived-tensor-open-restriction-universes`, module
  `Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses`.
- `lem-pc-derived-pullback-open-restriction-universes`, module
  `Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`.
- `lem-weil-pbc-spec-module-tilde-sections` as a proof dependency. Its Mathlib module
  `Mathlib.AlgebraicGeometry.Modules.Tilde` remains necessary through affine
  sheafification and the statement, so this is not a claim of whole-module pruning.

The first two comparisons are not directly applied by the main proof: it uses exact
restriction and explicit representing isomorphisms. After this repair,
`DerivedTensorOpenRestrictionUniverses` is nevertheless reached transitively through
`TorAmplitudeOpenLocal`, so it is not claimed as a pruned module. The general tensor
comparison is not applied in this proof because the
second factor is a sheaf in degree zero. The affine criterion is retained. Whether any
of these modules leave the full target closure is for the maintainer's ledger to decide.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated two private statements already in `TorAmplitudeOpenLocal`.
The repair imports that module with `import all` and uses the existing theorems exactly.
This resolves the landing refusal without an upstream interface change.

The old plan omitted the single-degree restriction/direct-image-counit interface needed
to use the Tor hypothesis on W. The new proved theorem supplies it for arbitrary open
immersions and independent localization universes, without an affine model or Tor
interval. Its edge cases include the empty source, an isomorphism (in particular an
identity), zero sheaves and arbitrary unbounded representatives; each construction
uses actual restriction, adjunction, and complex isomorphisms valid in those cases.

The source files were absent from this machine's read-only literature directory; read
Stacks `cohomology.tex` and `perfect.tex` from the official source into the sandbox
scratchpad. In particular read `lemma-quasi-coherence-tensor-product` (08DX), its local
calculation, and `lemma-tor-amplitude`/`lemma-tor-amplitude-pullback` in cohomology.tex.
The proof follows the original affine-test route; the unit record has no realized
statement or steps to bypass. No mathematical statement was corrected or disputed.

Searches run: LeanFinder for the full affine-neighbourhood statement (only t-structure
bounds found), Loogle for torAmplitudeIn (no hits), and grep for torAmplitude/TorDimension
(no Mathlib hits). For the helper, LeanSearch was unavailable (HTTP 500), Loogle found
`Scheme.Modules.restrictFunctorAdjCounitIso`, and grep found that declaration and its
isomorphism instance. Blueprint searches for tensor vanishing, tensor cohomology and
direct image/restriction found no matching statement; open restriction found only an
unrelated scheme-image lemma. Reading the library supplied the existing affine
criterion, pullback monoidal structure, K-flat pullback and bifunctor-single comparison.

## New nodes

`lem-pc-open-immersion-tensor-vanishing-test` records the proved single-degree restriction
test. It is strictly part of the affine argument: it has no affine-open hypothesis,
module model, representing isomorphism, or Tor interval. It lives in the item's chapter
and unit and traces back to `lem-sc-finite-duality`, the blueprint ancestor already
recorded by the item's originating delivery. Its Lean module contains a complete proof.
The item's node is updated only in `proof`, `proof_deps`, and `proof_origin` to follow
the actual proof. The conservative static command-interface check requires
`coord/changes/affine-local-tor-proof-commands.md`, which records the added open,
elaboration options and local-instance commands. No public signature changes.


## Second reading by T2

1. Compared the complete main-module diff with the read-only repository version.
   The existing theorem signature and docstring are byte-for-byte unchanged; all
   original public imports remain. Only proof imports, proof-local commands,
   a private constructed cancellation isomorphism and the proof body change.
   The command changes have the existing change record
   `coord/changes/affine-local-tor-proof-commands.md`. No definition used by a
   target changes. Verdict: pass.
2. Compiled both delivered modules in import order through `lcompile.py`: clean,
   10.8 seconds for the helper and 28.6 seconds for the item. Searched both files
   for forbidden declarations and sorry: none. The only new data definition,
   `affine_cancel`, explicitly composes equivalence counits and restriction
   isomorphisms; it does not choose an arbitrary unproved witness. Independently
   checked axioms in a scratch module for the item, cancellation isomorphism and
   helper: each uses only propext, Classical.choice and Quot.sound, with no
   sorryAx. Verdict: pass.
3. No unproved statements were split off. Read the proved helper from its
   hypothesis witness down to its conclusion: restriction preserves K-flatness,
   the counit replaces restricted direct image by G, the bifunctor-single
   comparisons identify the complexes, and exactness transports zero homology.
   Identity immersions, empty source, zero sheaves and unbounded complexes
   require no additional hypothesis. Its docstring and node describe that proof.
   Independent LeanFinder search for exact restriction and direct-image tensor
   cohomology found restriction composition and adjunction, not this statement;
   Loogle for mapHomologicalComplexHomologyIso and Mathlib grep for
   restrict.*tensor|tensor.*restrict found no hits. Repository searches also
   checked the related affine_sheafification_tensor_vanishing_test: that is an
   affine-specific theorem still using sorry, not the general proved helper.
   Verdict: pass; no duplicate statement or disguised restatement of the item.
4. Read the argument from its final affine criterion back through its explicit
   representing isomorphism and the reused private upstream comparisons.
   The original affine-test route is retained; the unit sk-thm-picard-duality
   has empty realized statement/step lists, so no realized route is bypassed.
   All three old proof dependencies now unused are named under No longer needed;
   the affine criterion remains. The two removed comparison imports are
   proof-only; transitive reachability prevents claiming full module pruning.
   The helper's public ExactFunctor import is needed by its statement's
   mapDerivedCategory expression. Verdict: pass.
5. Compared the existing node JSON: only proof, proof_deps and proof_origin
   change. Their steps follow the compiled proof, including reuse via import all
   of TorAmplitudeOpenLocal's private helpers. The new node has the source,
   searches, creation and blueprint records, verbatim Lean signature and proof
   dependencies; the listed dependency union matches its steps. Verdict: pass.

Second reading changed only this report: corrected the inaccurate claim that no
original import was removed, naming both removed original proof imports explicitly,
and added this independent review. No Lean or node repair was necessary.
