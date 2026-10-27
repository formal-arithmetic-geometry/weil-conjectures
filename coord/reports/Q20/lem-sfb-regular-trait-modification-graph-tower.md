## Worker report

The module `Sheaf.AlgebraicGeometry.RegularTraitModificationGraphTower` states
`AlgebraicGeometry.exists_regular_trait_modification_graph_tower`. Its only theorem
has the whole proof `by sorry`; there are no new definitions, new nodes, dependency
repairs or statement changes. The node copy changes only `lean`.

I read the node, all nine statement dependency records, the recorded declarations
and their docstrings, the proof plan, and Stacks `resolve.tex` at
`lemma-extend-rational-map-blowing-up` (0C5H) and `lemma-blowup-regular` (0AGR).
The theorem is the node's trait application of 0C5H over C, with the node's additional
projectivity and local dimension bookkeeping; it does not assume excellence,
flatness, semistability or regularity of Γ. The eight proof steps are included in
the theorem docstring with their DAG citations.

Hypotheses, in the order of the mathematical statement:

- A DVR A: `(A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]`.
  This is the recorded Mathlib class, including the nonfield condition.
- Its fraction field F: `(F : Type u) [Field F] [Algebra A F] [IsFractionRing A F]`.
  The trait is literally `Spec (.of A)`, and its generic map is
  `Spec.map (CommRingCat.ofHom (algebraMap A F))`.
- The residue field k is canonically the residue field at
  `IsLocalRing.closedPoint A`. No independently specified residue field or
  arbitrary map is introduced. The scheme-theoretic special fibre is
  `(r ≫ c).fiber (IsLocalRing.closedPoint A)`.
- Integral H-projective C over the trait: `[IsIntegral C]` and
  `(c : C ⟶ Spec (.of A)) [IsHProjective c]`.
- Nonempty integral generic fibre of C: `hgeneric : IsIntegral (pullback c
  (Spec.map (CommRingCat.ofHom (algebraMap A F))))`. `IsIntegral` includes
  nonemptiness, so a separate redundant hypothesis is unnecessary.
- H-projective r: `(r : Z ⟶ C) [IsHProjective r]`.
- r is an isomorphism over Spec F: `hr` is `IsIso` of the underlying morphism
  obtained by applying `Over.pullback` along the specified generic map to
  `Over.homMk r rfl : Over.mk (r ≫ c) ⟶ Over.mk c`.
  This functor uses the actual pullback objects and their universal lift.
- Z integral, regular and Noetherian: `[IsIntegral Z]`, `hZ : IsRegularScheme Z`,
  `[IsNoetherian Z]`. The first regular predicate includes local Noetherianity;
  `IsNoetherian` includes local Noetherianity and quasi-compactness (CompactSpace).
- Every local ring of Z has dimension at most two: `hdim : ∀ z : Z,
  ringKrullDim (Z.presheaf.stalk z) ≤ 2`.
- Every closed point of Z_k has local dimension two: `hspecial` quantifies over
  the actual scheme-theoretic fibre, assumes its singleton closed in that fibre,
  and evaluates the ambient Z stalk at its image under `fiberι`. It does not
  incorrectly use the local dimension of the fibre itself.
- Γ integral and p H-projective: `[IsIntegral Γ]`, `(p : Γ ⟶ C) [IsHProjective p]`.
- p is an isomorphism over Spec F: `hp` is the same canonical base-change
  construction as `hr`, applied to p, with source structure map `p ≫ c`.

Conclusion, clause by clause:

- The tower is `B : OrdinaryBlowupTower Z`, using the published definition in
  `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule` (recorded on
  `def-trf-ordinary-resolution-rule`). It has `length : ℕ`, levels indexed by
  `Fin (length + 1)`, an initial isomorphism with Z, composable transition maps,
  actual ideals, and `blowupIso`/`blowup_fac` specifying each blowup over its
  predecessor. This interface is also exactly the tower used by the recorded
  proof dependency `exists_surface_rational_map_point_resolution`.
- For each `i : Fin B.length`, the first conjunct chooses a point z of
  `B.level i.castSucc` and `hz : IsClosed {z}`. Its ideal is required to equal
  `Scheme.IdealSheafData.vanishingIdeal ⟨{z}, hz⟩`, the canonical reduced point
  ideal, rather than a thickening or unspecified ideal.
- The same point lies in the special fibre: `(B.toBase i.castSucc ≫ r ≫ c) z =
  IsLocalRing.closedPoint A`. Since the special fibre is closed in the total
  space, a closed point there is closed in the total space and conversely;
  this is exactly the node's reduced closed special-fibre centre condition.
- Its local ring is regular and has dimension two:
  `IsRegularLocalRing ((B.level i.castSucc).presheaf.stalk z)` and
  `ringKrullDim ((B.level i.castSucc).presheaf.stalk z) = 2`.
- Every level, including 0 and the last, is integral, regular, Noetherian and
  H-projective over the trait: the second conjunct quantifies over all
  `i : Fin (B.length + 1)` and asserts `IsIntegral`, `IsRegularScheme`,
  `IsNoetherian`, and `IsHProjective (B.toBase i ≫ r ≫ c)`.
- Y is the last level; a is explicitly a morphism from this level to Γ.
- The map h is the actual composite `B.toBase (Fin.last B.length) ≫ r`.
  `OrdinaryBlowupTower.toBase` is defined from the transition to level 0 and
  the initial isomorphism, not chosen as an unrelated map.
- The commutative triangle is `a ≫ p = B.toBase (Fin.last B.length) ≫ r`.
- h is H-projective: the next conjunct is `IsHProjective` of this composite.
- h is an isomorphism over F: the final `IsIso` is the canonical `Over.pullback`
  of h along Spec F -> Spec A, precisely as for the two hypotheses.
- Length zero is allowed: no positive-length or nonempty-centre hypothesis;
  `Fin 0` has no centre and `Fin (0 + 1)` still has its initial/last level.

Dependencies used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective`, the finite homogeneous-coordinate embedding
  convention from the dependency record, not a weaker notion of projectivity.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`, with the
  canonical residue-field morphism used internally by the fibre definition.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  defined as locally Noetherian and the upstream stalkwise `IsRegular`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` in `WithBot ℕ∞`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `blowupMap`,
  reused through the existing tower's `blowupIso` and `blowup_fac` fields.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `IdealSheafData.vanishingIdeal`.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `Over.pullback`, and
  `Over.homMk` from `Over.Basic`. The recorded base-change conventions module,
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, is publicly imported
  and uses exactly these chosen pullbacks and morphisms in
  `baseChange_morphism_projections`.
- `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`: `OrdinaryBlowupTower`, `toBase`.

All recorded proof dependencies with usable modules are imported, including
HProjectiveComposition, ProjectiveImpliesProper, SurfaceRationalMapPointResolution,
RegularPointBlowupGeometry and ProjectiveAffineBaseBlowup. The Mathlib proof leaves
use their recorded source modules (DVR.Basic, OpenImmersion, Properties, Noetherian,
Topology.NoetherianSpace, Topology.Sober and Topology.KrullDimension). No proof
import was omitted for a cycle.

Edge cases checked: length zero; empty schemes excluded only by the explicit
integrality assumptions; generic nonemptiness built into `IsIntegral`; no
assumption that the residue field is perfect, algebraically closed or of a fixed
characteristic; no bound on the genus or smoothness of C_F; Γ need not be regular;
points may have arbitrary residue-field extensions. A, its fraction field and the
schemes use a common arbitrary universe u, as in the recorded scheme and blowup
interfaces; this imposes no field-extension or dimension restriction. There are
no independent small universes for test objects and no auto-bound variables.

Searches (2026-10-24):

- `msearch.py ... leanfinder` with query “A projective modification of a regular
  surface over a discrete valuation ring is dominated by a finite tower of
  blowups of closed special fibre points”: eight hits about Proj properness,
  valuative criteria and minimal Weierstrass models, none giving this theorem.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.IsHProjective, AlgebraicGeometry.Scheme.IdealSheafData.blowup`:
  zero hits; search service reports unknown identifier IsHProjective.
- `msearch.py ... grep 'blow.?up|PointBlowup|modification' AlgebraicGeometry`:
  two unrelated elliptic-curve comments, no matching theorem or blowup tower.
- `msearch.py ... leansearch` with query “A projective modification over a regular
  surface over a discrete valuation ring is dominated by finitely many blowups
  of closed points in the special fibre”: eight dominance, normalization, Proj
  and elliptic minimal-model hits; no match.
- `rg -n 'PointBlowup|pointBlowup|BlowupTower|blowupTower|modificationGraphTower|regularTrait'
  lean/Sheaf lean/WeilConjectures` found the reusable ordinary tower, point ideals,
  the general surface resolution theorem, and related surface factorization
  results, but not this trait application.
- `rg -n 'regular.?trait|modification.*tower|graph.*tower'` in the two Lean roots
  and `dag/lean_names_upstream.json` found only related docstring text.
- Searching the exact item id under `lean/WeilConjectures` found no declaration.

No statement dispute or node fault was found. An initial compile diagnosed the
abbreviated `.ofHom`; it was corrected to `CommRingCat.ofHom`. The final complete
module compiled in both sandbox and module-path modes using the prescribed
`scompile.py`, about 1.9 seconds each, with no errors or warnings.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
