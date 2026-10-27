## Worker report

Item: `lem-pur-vector-bundle-finite-type-frames`. The new module is
`Sheaf.AlgebraicGeometry.VectorBundleFiniteTypeFrames`; its sole declaration is
`AlgebraicGeometry.VectorBundleZeroSection.finite_type_frames`. It states the node with
one `sorry`, and introduces no definition or axiom. The node copy changes only `lean`.
No statement correction, new node, dependency repair, or disputed statement is needed.

Hypotheses and conclusions, clause by clause:

- The field is `(k : Type u) [Field k]`. The finite-type k-scheme is `(S : Scheme.{u})`
  with its actual structure map `(f : S ⟶ Spec (.of k))`, `[LocallyOfFiniteType f]` and
  `[QuasiCompact f]`. This is the conjunction recorded by
  `def-weil-finite-type-morphism`; no separatedness of S is assumed.
- The module and its constant rank are `(d : ℕ) (F : S.Modules)` and
  `[F.IsFiniteLocallyFreeOfRank d]`. Naturals include rank zero.
- The bundle, projection and zero section are exactly `scheme S d F`, `π S d F` and
  `zero S d F` from `VectorBundleZeroSection`, not a selected arbitrary bundle or map.
- `∃ (hS : IsNoetherian S), ...` asserts the Noetherian conclusion for S. Its witness
  also supplies the existing construction's required instance, so no Noetherian
  hypothesis was added. `IsNoetherian (scheme S d F)` is the conclusion for V.
- `IsAffineHom (π S d F)`, `QuasiCompact (π S d F)`, `IsSeparated (π S d F)` and
  `LocallyOfFiniteType (π S d F)` assert the four morphism properties. The last
  together with quasi-compactness means finite type. `SmoothOfRelativeDimension d`
  asserts smoothness and pure relative dimension d; Mathlib's
  `SmoothOfRelativeDimension.smooth` supplies smoothness itself.
- `∃ (n : ℕ) (U : Fin n → S.affineOpens)` gives a finite affine cover, and
  `(⨆ i : Fin n, (U i).1) = ⊤` states coverage. Affineness is part of each `U i`.
  The canonical affine-spectrum identification is the existing
  `Scheme.isoSpec` of `(U i).1.toScheme`. Take its ring R_i to be
  `Γ((U i).1.toScheme, ⊤)`.
- `((Scheme.ΓSpecIso (.of k)).inv ≫ ((U i).1.ι ≫ f).appTop).hom.FiniteType`
  says that this actual coordinate ring is finitely generated over k, with the
  k-structure induced by f. The ΓSpec isomorphism removes the global-sections
  presentation of k; there is no auxiliary arbitrary algebra structure.
- `e : ∀ i, Trivialization S d F (U i).1` is a frame of the restricted *module*,
  defined upstream as its isomorphism to the free module on `ULift.{u} (Fin d)`.
- `IsIso (trivializationMap ... (e i))` asserts that the specific map induced by the
  frame is an isomorphism to `AffineSpace (ULift.{u} (Fin d)) (U i).1.toScheme`.
  Its composition with the affine-space projection is `(π S d F) ∣_ (U i).1`.
  Composing it with `zeroRestricted` gives `AffineSpace.zeroSection`, so the
  projection and zero section are the polynomial projection and coordinate origin.
- The additional `∃ φ` supplies the polynomial-spectrum isomorphism, with ring
  `MvPolynomial (ULift.{u} (Fin d)) Γ((U i).1.toScheme, ⊤)`.
  The equation `φ.hom = trivializationMap ... ≫ (AffineSpace.isoOfIsAffine ...).hom`
  identifies this with the same frame chart, rather than merely asserting that
  some unrelated polynomial-spectrum isomorphism exists. The latter canonical
  affine-space isomorphism uses constants as its structural map and the coordinate
  sections as its variables (its definition and `isoOfIsAffine_inv_over`).
- `(⨆ i, (π S d F) ⁻¹ᵁ (U i).1) = ⊤` asserts that the inverse-image opens cover V.
  For each such open, `IsAffine` is its affineness; `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact` applied to its inclusion followed by π
  and f say that it is a separated finite-type k-scheme.
- For every i, j and x in the overlap, `∃ (T : S.affineOpens) (hi : T.1 ≤ (U i).1)
  (hj : T.1 ≤ (U j).1), x ∈ T.1 ∧ ...` gives an affine neighbourhood inside the
  overlap. Pointwise existence is precisely an affine refinement cover; no
  affineness of the intersection is asserted. Its coordinate map to k satisfies
  the same `RingHom.FiniteType` condition.
- `ei ej : Trivialization S d F T.1` are required to have frame sections equal to
  the restrictions, along `F.presheaf.map (homOfLE hi).op` and the corresponding
  hj map, of the two original frames. Since these sections form bases, this
  specifies the restricted frames. Matrices G, H over `S.presheaf.obj (op T.1)`
  satisfy `G * H = 1` and `H * G = 1`. The next formula is exactly
  `e'_b = ∑ a, G a b • e_a`. The last formula applies the identical coefficients
  to the coordinates, after pullback by the restricted projection and the
  canonical `topIso`. Thus the same change of basis compares both charts.
- `(IsEmpty S → n = 0)` chooses the empty cover on the empty scheme. Coverage of V
  by these inverse images then gives its emptiness too.
- `d = 0 → ∃ e : scheme S d F ≅ S, e.hom = π S d F ∧ e.inv = zero S d F`
  states the canonical rank-zero identification. These specified maps force the
  identification uniquely, and its isomorphism identities say that projection
  and section become identities. It is not an arbitrary chosen comparison.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`.
- `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`: `scheme`, `π`, `zero`,
  `Trivialization`, `frameSection`, `coordinate`, `trivializationMap`, and
  `zeroRestricted`; also read `trivializationMap_spec` and `transition_spec`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its separatedness import:
  `IsProper`, `IsSeparated`, `UniversallyClosed`; only separatedness is asserted.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`,
  `SmoothOfRelativeDimension`, and `SmoothOfRelativeDimension.smooth`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, its structural projection,
  and `AffineSpace.isoOfIsAffine`; the source dependency's `mathlib_match` is usable
  despite having no `lean` record. `AffineSpace.zeroSection` comes from the public
  upstream affine-space dependency of VectorBundleZeroSection.

The imports also retain the recorded proof modules: the upstream smooth affine-space
result, symmetric-algebra basis equivalence, symmetric-algebra affine comparison,
relative Spec, and affine-local ring-map criteria. The remaining Mathlib proof leaves
(affine basis, finite type over Noetherian, affine/separated permanence, smoothness
locality) occur in the imported Mathlib geometry modules. The theorem docstring gives
all seven natural-language proof steps with the dependency node identifiers.

Searches:

- `msearch.py ... leanfinder "A finite rank algebraic vector bundle on a finite type
  scheme has finite affine frames and smooth affine projection"`: eight hits,
  including differential-geometric local frames, affine-space finite presentation,
  and the individual finite-type affine-pair criterion. None states this algebraic
  bundle theorem with its specified charts, zero section and overlap refinements.
- `msearch.py ... loogle "AlgebraicGeometry.SmoothOfRelativeDimension,
  AlgebraicGeometry.IsAffineHom"`: zero hits.
- `msearch.py ... grep
  "vectorBundle.*[Ss]mooth|[Ss]mooth.*vectorBundle|vectorBundle.*[Ff]initeType"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "algebraic vector bundle finite affine trivializing
  cover smooth finite type"`: eight topological/manifold vector-bundle hits;
  none is the algebraic assertion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `VectorBundleZeroSection`,
  vector-bundle finite geometry and finite frames found the existing bundle
  constructions and `Etale.vectorIntegration_geometry`. The latter states only
  affineness, local finite type and the Noetherian total space over an already
  Noetherian base; it does not supply this node's finite frames, smooth relative
  dimension, overlap refinements or finite-type-field conclusions.
- Searching `lean/WeilConjectures` for this exact node id found no declaration.
  Searching `dag/lean_names_upstream.json`, Mathlib and both project source roots
  for `VectorBundleZeroSection.finite_type_frames`, `VectorBundleFiniteTypeFrames`
  and `finite_type_frames` found no clash.
- Read the current blueprint unit and its proof under `literature/blueprint/latest/`,
  including the linear frame changes used in the deformation step. The supporting
  node supplies the detailed geometric preparation and Stacks references.

Edge cases checked: empty S permits n = 0 and the empty supremum; there is no Nonempty
assumption on a cover or scheme. Rank d = 0 permits the empty variable type, empty
matrices and empty sums and explicitly identifies the canonical maps. The zero ring
is permitted as an affine-open coordinate ring. Nonseparated finite-type bases are
permitted; refinements are inside overlaps and never require those overlaps to be
affine. All universes and variables are explicit (`autoImplicit false`); the coordinate
ULift has the scheme's universe and removes no finite ranks.

Validation: the delivered module compiled in module mode through scompile.py, both in
its sandbox check and as its actual library module, within the 60-second per-file limit.

## Second reading by Q116

This is the sole dispatched worker's second pass; the brief prohibits spawning other
agents and assigns independent delivery review to the maintainer. I reopened the node
and final module and matched every hypothesis and clause as listed above. In particular,
the Noetherian assertion is existential rather than an added hypothesis; the polynomial
isomorphism is the map induced by the actual module frame; the two overlap frames are
required to restrict the chosen original frames, and the coordinate matrix has the same
index convention as the frame matrix. The rank-zero isomorphism fixes both canonical
maps. No mismatch was found and no node correction was made. The final pass added explicit
imports for affine morphisms, Noetherian geometry and the proof's ring-map criteria.
