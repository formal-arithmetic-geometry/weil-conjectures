## Worker report

The module `Sheaf.AlgebraicGeometry.FlatMonoQuasiAffineNeighbourhood` states
`AlgebraicGeometry.Scheme.exists_quasiAffine_open_neighbourhood_of_flat_mono`, with
`by sorry` as its entire proof. It defines no new notion. The node is unchanged
except for its `lean` record.

Read the item's statement, source, all four proof steps, and all five statement
dependency nodes and their recorded declarations. The primary source was read at
https://www.numdam.org/article/SAC_1967-1968__2__A5_0.pdf, printed pp.14–15:
Proposition 3.4 (heading 3.5 in the scan), with Lemmas 3.6 and 3.7 and the proof.
The primary statement agrees with the node; no correction is needed.

Clause-by-clause correspondence:

- Schemes X and T and their morphism f: `{X T : Scheme.{u}} (f : X ⟶ T)`.
  The universe `u` is explicit and arbitrary, without any dimension, field,
  nonemptiness or size restriction on either scheme beyond the usual common
  universe for the category of schemes.
- Quasi-compact morphism: `[QuasiCompact f]`. Mathlib's definition requires
  compact inverse images of compact opens; the affine basis makes this equivalent
  to compact inverse images of affine opens, as stated in the node. This explicitly
  retains the source's hypothesis even though the other hypotheses imply it.
- Flatness: `[Flat f]`, equivalent to flatness of every stalk map by
  `Flat.iff_flat_stalkMap` in `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- Monomorphism: `[Mono f]`, whose `right_cancellation` field quantifies over every
  object W of the scheme category and every pair of morphisms W → X. This is
  precisely injectivity of postcomposition on Hom(W,X), not merely injectivity on
  the underlying points.
- Quasi-affine X: `[X.IsQuasiAffine]`. The class in
  `Mathlib.AlgebraicGeometry.QuasiAffine` extends `CompactSpace X` and
  `IsImmersion X.toSpecΓ`; the instance immediately following it upgrades this to
  `IsOpenImmersion X.toSpecΓ`. Consequently X is a quasi-compact open subscheme of
  the affine scheme `Spec Γ(X, ⊤)`. Conversely, Mathlib's
  `Scheme.IsQuasiAffine.of_isImmersion`, applied to an open immersion into an affine
  scheme with compact source, gives this class. Thus the node's compact-open
  convention is exactly respected; arbitrary noncompact opens are not substituted.
- Quasi-separated T: `[QuasiSeparatedSpace T]`. The equivalence
  `quasiSeparatedSpace_iff_forall_affineOpens` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` identifies this with the
  compactness of all intersections of two affine opens, the node's definition.
- An open subscheme of T: `∃ U : T.Opens`, with its canonical scheme structure
  `U.toScheme` and open immersion `U.ι`, using the existing open-subscheme API.
- Quasi-compactness of the open: `IsCompact (U : Set T)`. Compactness of this
  subset is equivalent to compactness of its subspace, the underlying space of
  `U.toScheme`.
- Quasi-affineness of the open: `U.toScheme.IsQuasiAffine`, with exactly the same
  convention as for X. The explicit compactness conjunct is retained to display
  both adjectives of the node's conclusion.
- Containment of the entire image: `Set.range f ⊆ (U : Set T)`, using the canonical
  coercion of f to its underlying continuous function. It makes no assertion that
  f itself is an open immersion or that the image equals U.
- The negative hypothesis clause is respected: neither `LocallyOfFinitePresentation`
  nor a Noetherian, finite-type, separated-target or field assumption is present.

Dependency interfaces used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, and `Scheme.Opens`,
  in `Mathlib.AlgebraicGeometry.Scheme`; their signatures and docstrings were read.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat` and its stalkwise equivalence,
  in `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `def-weil-pbc-scheme-conventions`: this is a convention-only record without a
  module or declaration. Its named Mathlib notions are used directly:
  `QuasiCompact` and `QuasiSeparatedSpace` from the quasi-compact and
  quasi-separated morphism modules. No private convention definition is created.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, in
  `Mathlib.AlgebraicGeometry.Scheme`, used through the existing quasi-affine
  interface rather than a second spectrum or embedding construction.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`, in
  `Mathlib.AlgebraicGeometry.OpenImmersion`, and the canonical `U.toScheme` API.

The docstring carries the node's four proof steps, with each proof dependency
named. The already stated proof dependencies are imported without `public`:
`Sheaf.AlgebraicGeometry.QuasiAffineOpenPrincipalComparisonCover`
(`Scheme.quasiAffine_open_principal_comparison_cover`),
`WeilConjectures.Topology.ProconstructibleClosureSpecialization`
(`Topology.exists_mem_iInter_closure_singleton`), `Mathlib.Topology.Constructible`
(`Topology.IsConstructible`), and `Mathlib.Topology.Spectral.Basic`
(`SpectralSpace`, the recorded Mathlib match for the spectrality node).
The first two declarations were read with their complete signatures and docstrings.
The nodes `lem-sfb-proopen-global-section-extension` and
`lem-sfb-quasiaffine-principal-neighbourhood-criterion` have no Lean record or
Mathlib match in the read checkout: they are used only by the future proof and
are named in the proof docstring; no unstated module is imported. Neither is
needed to type the statement.

Edge cases checked before drafting:

- X empty: U may be the empty open; it is affine, the spectrum of the zero ring,
  and hence quasi-affine and compact. There is no nonempty or nontriviality binder.
- T empty: any f forces X empty, giving the same witness.
- X and T affine and f the identity: the whole open works, including the zero ring.
- A localization such as Spec Q → Spec Z: this is a quasi-compact flat
  monomorphism with nonopen image, covered by U = Spec Z. The formulation does not
  accidentally assert that all flat monomorphisms are open immersions.
- A non-quasi-compact target is allowed: only its quasi-separatedness is assumed,
  and U is required compact independently. No target compactness is smuggled in.
- Arbitrary characteristic and non-Noetherian rings are allowed. In particular,
  the Mathlib flat-monomorphism open-immersion lemma requiring local finite
  presentation was not used as a replacement statement.

Searches actually run using `/home/ubuntu/weil-launcher-all/batch2/msearch.py`
with group NA and this item:

- LeanFinder: "A quasi-compact flat monomorphism with quasi-affine source into a
  quasi-separated scheme has a quasi-affine open neighbourhood" returned 8 hits,
  including `Scheme.IsQuasiAffine.of_isImmersion`, `.of_isAffineHom`, and
  `.of_forall_exists_mem_basicOpen`, but no neighbourhood theorem.
- Loogle: `"QuasiAffine", "Flat"` returned 0 hits.
- LeanSearch: "Quasi-compact flat monomorphism from a quasi-affine scheme has
  quasi-affine open neighbourhood in quasi-separated target" returned 8 hits,
  including `IsOpenImmersion.of_flat_of_mono`; that declaration has the extra
  local finite-presentation hypothesis, so it does not state this node.
- Grep service: `quasi.?affine.*(flat|mono|neigh)|(flat|mono|neigh).*quasi.?affine`
  under `AlgebraicGeometry` returned 0 hits.
- Local rg with the same pattern in `lean/WeilConjectures` and `lean/Sheaf`
  returned only unrelated schematic-image and quasi-affine descent material.
  The upstream node-id grep returned no hits. The analogous search in
  `dag/lean_names_upstream.json` returned no match. Searching the proposed full
  declaration name in Mathlib, both project roots and that name index found none.
  `Mathlib/AlgebraicGeometry/QuasiAffine.lean` was read in full to check the class
  convention and its immersion lemmas.

No new node, unusable statement dependency, hollow definition, statement dispute,
or source error was found. All variables and the sole universe are bound explicitly;
`autoImplicit` is disabled in the module. Only the expected theorem sorry is left.

## Second reading by NA

Author's second reading (the maintainer supplies the independent review): reread
both the complete node and the final Lean signature. The five explicit assumptions
are respectively quasi-compactness of f, flatness, monomorphism, quasi-affineness of
X, and quasi-separatedness of T, with the same schemes and morphism throughout.
The conclusion binds an actual open of T and separately requires compactness,
quasi-affineness of its canonical open scheme, and containment of the entire range
of f. Checked the definitions of `Mono` and `IsQuasiAffine`, rather than replacing
them by pointwise injectivity or a possibly noncompact open. Empty schemes remain
allowed. No mismatch was found and no statement or dependency record was changed.
The docstring was reread against all four proof steps, including the constructible
shrinking and the final principal-neighbourhood criterion.

Validation: `scompile.py NA lem-sfb-flat-monomorphism-quasiaffine-neighbourhood`
compiled this single delivered file successfully as both the sandbox module and
its final library module; exit code 0, no errors or warnings were printed.
The final library compile reported 5.7 seconds. A local text check found no Lean
line over 100 characters and confirmed that `lean` is the only changed node field.
