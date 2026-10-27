## Worker report

The new module `Sheaf.AlgebraicGeometry.SpaceLimitRepresentableIsomorphism` states
`AlgebraicGeometry.AlgebraicSpace.exists_isIso_representable_stage_of_fppf_limit`,
with its sole proof `sorry`. No construction or definition is duplicated.
Source checked: `literature/stacks-project/spaces-limits.tex`, Situation 084R
(lines 1033 onward) and Tag 084S, lemma-descend-equality (lines 1096 onward).
The source has precisely assumptions (a)--(d) rendered below. No statement correction.

Clause-by-clause correspondence:

- Base scheme: `{S : Scheme.{u}}`; algebraic spaces over it: `AlgebraicSpace S`.
  These are the recorded full subcategory of fppf sheaves. Their structure sheaves
  are part of that existing framework and play no role in this statement.
- Small directed indexing set: `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]`.
  The fixed index `(i₀ : I)` supplies nonemptiness, so empty indexing is excluded
  exactly as in the node without a redundant `Nonempty` binder.
- Inverse system: `D : Iᵒᵖ ⥤ AlgebraicSpace S`. Opposite preorder arrows encode
  transitions from later to earlier stages.
- Every stage quasi-compact: `hqc` supplies an `Over S` scheme `U`, a map from
  `yoneda.obj U`, and `CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a`.
  This is exactly the node's quasi-compact atlas criterion.
- Every stage quasi-separated: `hqs` uses `IsAbsolutelyQuasiSeparated`.
  The recorded definition is Stacks 0AHR(3), equivalent to quasi-compactness of the
  absolute diagonal over Spec Z; it imposes no separation on the ambient S.
- Affine transitions: `haff` uses `IsRepresentableWith` and the recorded scheme
  predicate `IsAffineHom p.left`. Testing on all schemes for affine projection is
  equivalent to representability plus affine sources over affine scheme tests:
  restrict a test scheme to its affine opens and use target locality of affineness.
- Limit and specified projections: `c : Cone D` and
  `hc : IsLimit ((ObjectProperty.ι _).mapCone c)` say that the underlying fppf sheaf
  of `c.pt` with those projections is the sheaf limit. The inclusion here is from
  algebraic spaces to fppf sheaves, not merely an assumed space-category limit.
- Fixed stage: `(i₀ : I)`.
- Spaces and structure maps: `Y₀ T₀ : Over (D.obj (op i₀))`.
  Their structural maps are `Y₀.hom` and `T₀.hom`; the two `hYrep`/`hTrep`
  hypotheses apply the recorded scheme-test `IsRepresentable` to those maps.
- Quasi-compactness of Y₀ and T₀: `hYqc` and `hTqc` repeat precisely the existing
  atlas condition, with no restriction to affine or finite-presentation atlases.
- Absolute quasi-separatedness of Y₀ and T₀: `hYqs` and `hTqs`.
- Map over the fixed stage: `g₀ : Y₀ ⟶ T₀` in the over category includes exactly
  the commutation with their two structure maps.
- Local finite presentation: `hlfp : MapIsLocallyOfFinitePresentation g₀.left`,
  the recorded extension of scheme `LocallyOfFinitePresentation` to etale charts.
- Limit base change is an isomorphism: `hX` applies `IsIso` to
  `((Over.pullback (c.π.app (op i₀)).hom).map
  ((Over.post (ObjectProperty.ι _)).map g₀)).left`. Here `Over.post` sends the
  over-space map to the over-sheaf map using the inclusion into fppf sheaves, and
  `Over.pullback` is the canonical base-change functor in fppf sheaves.
  Invertibility is thus invertibility of exactly the specified sheaf/space map.
- Conclusion: `∃ (i : I) (hi : i₀ ≤ i), IsIso (...)` uses the same canonical
  base-change functor with transition `D.map (homOfLE hi).op`. Thus it asserts
  invertibility of the given g₀ after that base change, not a bare isomorphism of
  the two resulting objects.

Recorded declarations reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentable`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`; signatures/docstrings read.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated` (landed definition added to stmt_deps).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocallyOfFinitePresentation`, using `MapIsLocally`
  (landed definition added to stmt_deps).
- `Mathlib.CategoryTheory.Comma.Over.Basic` and `.Pullback`: `Over.post` and
  `Over.pullback`, with their signatures and definitions read.
- Size convention: explicit universe `u`, with schemes and index sets at the
  recorded sizes. This is a metatheoretic convention, with no declaration to import.

The stated proof dependencies are imported as plain imports: fibre products and
etale covers; affine-transition scheme limits; affine schemes' quasi-separatedness;
chart property test; scheme isomorphism descent; representable etale fppf lifting.
`lem-trf-space-qc-finite-affine-atlas-refinement` and
`lem-sfb-space-qcqs-source-products` have no recorded Lean declaration in the read
DAG, so no speculative imports were added for these proof-only inputs.

Edge cases checked before writing: constant/singleton directed systems give the
original isomorphism; non-antisymmetric preorders remain allowed; i=i₀ is allowed;
empty spaces and empty atlas schemes are allowed (no Nonempty scheme hypothesis);
S need not be quasi-separated, because all quasi-separatedness predicates are
absolute. Neither Y₀ nor T₀ is assumed finitely presented over Xᵢ₀. Only g₀ is
locally finitely presented. No transition surjectivity or separatedness is imposed.
Without the lfp assumption Spec Q -> Spec Z over the increasing localizations of
Z gives a limiting isomorphism without finite-stage isomorphism, confirming the
need for the retained hypothesis. No disputed statement or node fault found.

Searches for existing statements:

- msearch.py leanfinder: "A locally finitely presented morphism between qcqs
  algebraic spaces representable over a stage of an inverse system becomes an
  isomorphism at a finite stage if it is an isomorphism at the limit". Eight hits,
  including Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType and
  Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType; none states this space result.
- msearch.py loogle: "AlgebraicGeometry.AlgebraicSpace,
  CategoryTheory.IsIso". Zero hits; AlgebraicSpace unknown in the Mathlib index.
- msearch.py grep: "(algebraicSpace|AlgebraicSpace|descend.*[Ii]so)" in
  AlgebraicGeometry. Seven hits, all scheme isomorphism-descent infrastructure,
  no algebraic-space theorem.
- rg of lean/WeilConjectures and lean/Sheaf for the node id and algebraic-space
  isomorphism/limit statements: no exact existing theorem. Targeted definition
  searches located the existing absolute quasi-separatedness, chartwise morphism
  properties, which are reused. The canonical base-change helper belongs to a
  downstream theorem node: its reuse would close a DAG cycle, detected by an
  explicit dependency traversal and the first preflight. The final statement
  directly applies Mathlib Over.post and Over.pullback, without any new helper.
- DAG searches for these declaration names located their owning nodes and verified
  that each newly cited node is already recorded; no new definition node is needed.

## Second reading by Q45

The dispatcher requests one worker and explicitly forbids starting other agents;
this section records a self-review, not an independent review. The maintainer's
independent delivery review remains required. Re-read the node, Tag 084S and the
finished signature: checked the two representability hypotheses, all three qcqs
pairs, the direction of opposite-index transition maps, and canonical-map IsIso
rather than object isomorphism. Checked in particular that `hc` is a limit in fppf
sheaves by the full-subcategory inclusion and that no quasi-separatedness of S or
finite presentation of either structure map was introduced. No mismatch found.

Validation: the initial module compiled cleanly, but preflight detected the cycle
item -> eventually-surjective-map -> affine-limits-schematic-stages -> item.
Removed that owning-node dependency and helper import entirely; the final statement
uses the canonical sheaf pullback directly. No existing definition was copied.
