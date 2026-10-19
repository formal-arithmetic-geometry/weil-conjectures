## Worker report

The module `Sheaf.AlgebraicGeometry.SurfacePointBlowupGeometry` states
`AlgebraicGeometry.Scheme.IdealSheafData.surface_point_blowup_geometry`.
Its only theorem has proof `sorry`. No definition is introduced and no theorem is proved.
The theorem docstring contains all ten source-based proof steps and their DAG dependencies.
The node's natural-language statement is unchanged. Its statement dependencies gain the
already landed `def-pc-dimension`, whose `Scheme.dim` is used for both scheme dimensions.
No new definition nodes or dependency replacement modules are needed.

### Hypotheses, matched individually

- The scheme is `(X : Scheme.{u})`; the arbitrary universe `u` is explicit.
- Integral is `[IsIntegral X]`, the recorded Mathlib class (nonempty and domain sections).
- Regular is `hRegular : IsRegularScheme X`, using the landed scheme definition, which
  includes local Noetherianity and regularity of every stalk.
- Excellent is `hExcellent : ∀ U : X.affineOpens, IsExcellent Γ(X, U)`. This is the usual
  affine-local scheme convention using the recorded excellent-ring predicate; it does
  not replace excellence by stalkwise excellence or by an arbitrary chosen affine cover.
- Noetherian is `[IsNoetherian X]`, the standard scheme class, including quasi-compactness.
- Dimension two is `hDimension : X.dim = 2`, using the supremum-of-local-dimensions definition.
- Existence of an ample invertible sheaf is `hAmple : ∃ (L : X.Modules)
  (hL : L.IsInvertible), @Scheme.Modules.IsAmple X L hL`. Both existence and invertibility
  are explicit, and the absolute ampleness definition includes quasi-compactness.
- The point is `(p : X)` and closedness is `hp : IsClosed ({p} : Set X)`.
- Its local dimension is `hpDimension : ringKrullDim (X.presheaf.stalk p) = 2`.
- The reduced closed centre is named by `(I : X.IdealSheafData)` and
  `hI : I = (X.fromSpecResidueField p).ker`. This equality fixes the ideal completely:
  the residue field is the local ring modulo its maximal ideal, and the canonical point
  map is a closed immersion when `p` is closed (Mathlib
  `isClosed_singleton_iff_isClosedImmersion`). Its kernel is the ideal of that reduced
  closed subscheme. Thus `I` is a name for the specified centre, not an extra restriction
  on admissible centres, an arbitrary map, or a chosen scheme structure on `{p}`.
- The node's `X'` and `b` are the recorded global constructions `I.blowup` and `I.blowupMap`.

### Conclusions, matched individually and in order

1. `IsIntegral I.blowup` is integrality of the blowup.
2. `IsRegularScheme I.blowup` is regularity, with local Noetherianity included.
3. `∀ U : I.blowup.affineOpens, IsExcellent Γ(I.blowup, U)` is excellence of the blowup.
4. `IsNoetherian I.blowup` is global Noetherianity.
5. `I.blowup.dim = 2` is its dimension, using the same definition as the hypothesis.
6. The existential `L : I.blowup.Modules`, `hL : L.IsInvertible`,
   `@Scheme.Modules.IsAmple I.blowup L hL` says it admits an ample invertible module.
7. `LocallyOfFiniteType I.blowupMap ∧ QuasiCompact I.blowupMap` is finite type, exactly
   the conjunction recorded by `def-weil-finite-type-morphism`.
8. `IsHProjective I.blowupMap` is finite-projective-space projectivity, not the
   weaker projective-bundle convention. Its index type is finite; replacing it by a
   finite standard set gives the node's integer-dimensional projective-space convention.
9. The exceptional divisor is the scheme
   `pullback I.blowupMap (X.fromSpecResidueField p)`. Its existential isomorphism `e`
   has target `ProjectiveLine (Spec (X.residueField p))`; the equation
   `e.hom ≫ (ProjectiveLine (Spec (X.residueField p)) ↘ Spec (X.residueField p)) =
   pullback.snd I.blowupMap (X.fromSpecResidueField p)` makes this an isomorphism
   over the residue field. `ProjectiveLine` abbreviates projective space with
   two homogeneous coordinates, namely `ULift.{u} (Fin 2)`.
10. `IsRegularScheme (pullback I.blowupMap (X.fromSpecResidueField p))` says the
    exceptional divisor itself is regular.
11. The support formula quantifies over every `W : X.IdealSheafData` with
    `p ∈ W.support`. The left side is `(W.comap I.blowupMap).support`, the support
    of the scheme-theoretic inverse image. Mathlib's `comapIso` identifies its closed
    subscheme with the fibre product over `X`. On the right, the range of
    `pullback.fst I.blowupMap (X.fromSpecResidueField p)` is the support of the
    exceptional fibre, and the range of the recorded `strictTransformMap` is the support
    of the strict transform in the blowup. The equality is of subsets of `I.blowup`.
12. The last clause quantifies over every `Y : X.IdealSheafData` with
    `[IsIntegral Y.subscheme]`. It gives an isomorphism from `I.strictTransform Y.subschemeι`
    to `(I.comap Y.subschemeι).blowup`, and the displayed equation identifies its map
    to `Y.subscheme` with `strictTransformToSource`. Thus the strict transform is the
    blowup of `Y` in the scheme-theoretic intersection with the reduced centre, as a
    scheme over `Y`. The ideal `I.comap Y.subschemeι` is precisely the pulled-back centre.

Closed subschemes are represented by quasi-coherent ideal sheaf data, not arbitrary
monomorphisms. Mathlib's closed immersion/kernel equivalence identifies every closed
subscheme with this representation, so these universal clauses cover all closed subschemes,
including nonreduced `W`. No irreducibility or reducedness hypothesis is imposed on `W`.

### Dependency declarations read and used

- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`.
- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`,
  `AlgebraicGeometry.IsRegularScheme`; its body is `IsLocallyNoetherian X ∧ IsRegular X`.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`, whose body
  is `IsQuasiExcellent R ∧ IsUniversallyCatenary R`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; scheme Noetherianity is `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsNoetherian`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim : (R : Type u) → [CommSemiring R] → WithBot ℕ∞`.
- `def-weil-pbc-ample-invertible-module`: `WeilConjectures.AlgebraicGeometry.Ample`,
  `AlgebraicGeometry.Scheme.Modules.IsAmple` with its invertibility instance argument.
- `def-nagata-global-blowup`: `WeilConjectures.Blowup.Gluing`,
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and `blowupMap`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; subscheme inclusions supplied by ideal sheaf
  data and strict transform are closed immersions. The canonical residue-field point
  map is a closed immersion exactly when the singleton is closed.
- `def-nagata-strict-transform`: `WeilConjectures.Compactification.StrictTransform`,
  `AlgebraicGeometry.Scheme.IdealSheafData.strictTransform`,
  `AlgebraicGeometry.strictTransformMap`, `AlgebraicGeometry.strictTransformToSource`.
  This is the scheme-theoretic image of the complementary open locus, not topological closure.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-nagata-projective-space-base-change`:
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`, `AlgebraicGeometry.ProjectiveSpace`
  and its `ProjectiveLine` abbreviation and canonical structural morphism.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`, `Scheme.fromSpecResidueField`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- Added landed dependency `def-pc-dimension`: `Sheaf.AlgebraicGeometry.Dimension`,
  `AlgebraicGeometry.Scheme.dim`.

Recorded proof dependency modules are imported nonpublicly. The three proof nodes
`lem-per-integral-blowup-projective-geometry`, `lem-per-projective-bundle-relative-ample`,
and `lem-per-relative-ample-absolute-twist` have no recorded declaration yet and therefore
supply no import. They are not needed to type this statement. No statement prerequisite
is missing. Mathlib proof leaves are imported in their defining modules too.

The two missing local source modules `WeilConjectures.AlgebraicGeometry.Ample` and
`WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, and the current projective-space
source, were read with the prescribed `scompile.py --source` resolver. The live signatures
are exactly those used here; no duplicate interface was introduced.

### Edge cases and source checks

- The empty scheme is excluded by integrality and also by the specified point. There is
  no tacit extra nonemptiness or dimension purity assumption.
- No restriction on characteristic, residue field perfection, or algebraic closedness
  occurs. The exceptional line is over the actual residue field, not over an algebraic closure.
- The point's local dimension is explicitly required even with global dimension two.
- `W = p`: the strict transform is empty and the total support is exactly the exceptional
  fibre; the union equation allows this case.
- `W = X`: its strict transform is the whole blowup; the same union equation holds.
- Nonreduced `W` containing `p` is allowed; the formula concerns support, not equality
  of total and reduced closed subscheme structures.
- `Y = p`: its pulled-back centre ideal is zero, its blowup is empty, and its strict
  transform is empty. No nonzero-ideal or dominant-immersion assumption is added.
- `Y` disjoint from `p`: the pulled-back centre is the unit ideal, so its blowup and
  strict transform both identify with `Y`.
- `Y = X` and arbitrary integral curves through `p` are included.
- The ample conclusion asserts existence of an ample module after twisting a relatively
  ample module; it does not incorrectly assert that the pullback of an ample module is ample.
- Read the source at `resolve.tex` Lemmas `lemma-blowup` and `lemma-blowup-regular`
  (Tags 0AGQ, 0AGR), and the opening proof of `lemma-embedded-resolution` (0BIC).
  The exceptional fibre in 0AGQ is scheme-theoretic and the regularity argument in 0AGR
  uses the regular quotient by its local equation. These match the theorem and proof plan.

No statement fault or `STATEMENT-DISPUTED` issue was found.

### Searches

All search wrapper calls used group `NV` and this item id.

- `msearch.py leanfinder`, query: "The blowup of a regular excellent Noetherian surface
  at a closed point is regular, with exceptional divisor the projective line". Eight
  hits concerned smoothness or Weierstrass curves; no matching theorem.
- `msearch.py leansearch`, query: "A blowup of a regular Noetherian surface at a closed
  point is regular and its exceptional divisor is a projective line". Eight hits
  concerned local closed points, residue maps, elliptic curves and normalization; no match.
- `msearch.py loogle`, query: `"blowup"`. Zero hits.
- `msearch.py grep`, query: `blowup|BlowUp|BlowingUp`, directory `AlgebraicGeometry`.
  Zero Mathlib hits.
- `rg -n 'lem-per-surface-point-blowup-geometry|surface.*[Bb]lowup|[Bb]lowup.*surface'`
  in `WeilConjectures` and `lean/Sheaf`: existing results concern principalization,
  rational-surface resolution, intersection decrease and embedded resolution. None
  states this preservation theorem with its exceptional fibre and both transform clauses.
- `rg` for the proposed declaration name in Mathlib/upstream-name records and both
  project source trees: no existing declaration with that name.
- Searches and inspection located the canonical global blowup, strict transform,
  residue-field point map, ideal pullback and projective line. All are reused.

### Validation

The delivered module was checked by `scompile.py` in both its sandbox and library-module
contexts. The first run compiled without errors or warnings (10.2 s and 3.5 s respectively).
A final wrapper run also checks the explicit defining-module imports added for all recorded
statement and proof dependencies. Only this module is compiled; no library build is run.
Delivery dry run and final push are performed with `deliver2.py` after this report is written.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
