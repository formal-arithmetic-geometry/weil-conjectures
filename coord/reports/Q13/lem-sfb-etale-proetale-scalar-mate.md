## Worker report

The item is stated by `AlgebraicGeometry.ProEtale.etaleProEtale_scalar_mate` in
`Sheaf.Paper.EtaleProEtaleScalarMate`. Its proof is `sorry`; the statement and its
recorded `stmt_deps` are unchanged. The module also contains the canonical helper
interfaces needed by this statement. Those helpers are item-local declarations,
with docstrings naming the specialized dependency nodes, so no duplicate dependency
module is delivered.

Each hypothesis and clause is rendered as follows.

- `f` is a morphism `{X Y : Scheme.{u}} (f : X ⟶ Y)` with exactly
  `[QuasiCompact f] [QuasiSeparated f]`.
- `A` and `B` are arbitrary discrete commutative rings in the project universe:
  `{A B : Type (u + 1)} [CommRing A] [CommRing B]`, with ring map `a : A →+* B`.
  No flatness, finite presentation, completion, or Tor-amplitude hypothesis is added.
- `J` is
  `_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))`.
  The lower-bound hypotheses are exactly `hJ : ∃ n : ℤ, J.IsGE n` and
  `_hBJ : ∃ n : ℤ, ((pbcFixedScalarExtension X.smallEtaleTopology a).obj J).IsGE n`.
- `pbcFixedScalarExtension` is the published constant-coefficient scalar extension;
  `pbcComparisonReduction` is its published comparison-reduction map.
- `scalarPullbackProEtaleIso` and `scalarPullbackEtaleIso` are the inverses of the
  item-local reverse scalar-adjunction mates. Their invertibility is the item-local
  specialization of `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, proved as
  the postponed theorem `scalarPullbackReverse_isIso`.
- `directImageComparisonAmbient` is the item-local `mateEquiv` of the exact
  inverse-image comparison square. `directImageComparisonAmbientIso A f J hJ` is
  `asIso` of its component, using the item-local bounded-below theorem
  `directImageComparisonAmbient_isIso`; the inverse is taken only at `J`.
- The left side is the pro-etale scalar mate followed by
  `R(lowerStar B f).map ((pbcComparisonReduction X a).hom.app J)`.
  The right side is, in the displayed order,
  `T_Y.map (directImageComparisonAmbientIso A f J hJ).inv`, then the reduction at
  `R(Etale.lowerStar A f).obj J`, then the etale scalar mate under comparison, then
  `directImageComparisonAmbient B f` at the scalar extension of `J`.
  Every arrow is in the B-module derived category and the equality is exactly the
  node's displayed equality.

The item-local helper declarations are:

- `scalarPullbackReverseProEtale`, `scalarPullbackReverseEtale`,
  `scalarPullbackReverse_isIso`, `scalarPullbackProEtaleIso`, and
  `scalarPullbackEtaleIso` (specialized interface for
  `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`).
- `directImageComparisonAmbientPullbackIso`, `directImageComparisonAmbient`,
  `directImageComparisonAmbient_isIso`, and `directImageComparisonAmbientIso`
  (ambient interface for `sk-thm-pe-direct-image-comparison`).

The dependency declarations used by the helper constructions are the published
site comparison, exact inverse-image and restriction-scalar modules, the published
fixed scalar adjunctions and `pbcComparisonReduction`, the etale and pro-etale
geometric derived adjunctions, and `CategoryTheory.mateEquiv`. The four recorded
dependency node JSON files are left byte-for-byte unchanged; no dependency record
is re-pointed and no separate dependency module is delivered.

Edge cases checked before writing the statement: `f = 𝟙`, `a = RingHom.id`,
`J = 0`, zero rings, empty schemes, and nonflat maps such as `Z/4 → Z/2` remain
allowed. No identity or arbitrary-lift case is discarded. Site and coefficient
universes remain independent, with coefficients in the common `u + 1` universe.

Searches made:

- `msearch.py ... leanfinder "derived scalar extension etale proetale direct image comparison mate"`:
  unrelated scalar/direct-image results; no existing item theorem.
- `msearch.py ... loogle "CategoryTheory.mateEquiv, CategoryTheory.mateEquiv_vcomp"`:
  generic mate lemmas only.
- `msearch.py ... grep "scalar.*[Mm]ate|[Mm]ate.*scalar|mateEquiv_vcomp" CategoryTheory`:
  no site-specialized scalar mate.
- `rg` over the supplied pro-etale framework, upstream `WeilConjectures`, and
  `lean/Sheaf` for scalar pullback, comparison mates, `pbcFixedScalarExtension`,
  `pbcComparisonReduction`, and direct-image comparison names: only the published
  underlying constructions were found; the item equality is new.
- Exact-item grep over upstream and the shared DAG found no existing declaration.

No statement correction, new definition node, or `STATEMENT-DISPUTED` issue applies.

## Second reading by Q13

After consolidating the helpers, I reread the source statement, every hypothesis and
composition order, the item-local helper signatures, and the four dependency records
against the return entry. The second pass confirmed that the only postponed data are
named theorem proofs, that all helper maps are canonical mates or inverses of those
maps, that `directImageComparisonAmbientIso` is used only under `hJ`, and that the
unused `DerivedChangeOfRingsIndependentCoefficients` and `LowerStarProjection`
imports are absent. The item module compiles independently through `scompile.py`.
