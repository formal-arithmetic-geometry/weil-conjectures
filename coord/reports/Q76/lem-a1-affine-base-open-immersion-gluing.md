## Worker report

The module `Sheaf.AlgebraicGeometry.AffineBaseOpenImmersionGluing` states
`AlgebraicGeometry.exists_unique_quasiCompact_isOpenImmersion_of_affine_base_cover`.
It introduces no definitions and leaves exactly that theorem's proof as `sorry`.
The node is unchanged except for its `lean` field. No statement correction,
new nodes, dependency repairs, or statement dispute was needed.

Source read: `literature/stacks-project/morphisms.tex`,
`lemma-characterize-quasi-affine` (Tag 01SM), especially the last assertion of
(2) implies (4). The node expands that local-to-global assertion into compatible
chart gluing; its five proof steps are reproduced in the theorem docstring.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The schemes are `{Z Y S : Scheme.{u}}`, and the named morphisms are
  `(h : Z ⟶ S)` and `(π : Y ⟶ S)`.
- The affineness of π is exactly `[IsAffineHom π]`.
- The affine open family is `(U : A → S.Opens)` with `{A : Type v}`;
  `hU : iSup U = ⊤` states that it covers S, and
  `hUa : ∀ a : A, IsAffineOpen (U a)` states that every member is affine.
- The node's Z_a and Y_a are `(h ⁻¹ᵁ U a).toScheme` and
  `(π ⁻¹ᵁ U a).toScheme`. These are Mathlib's actual open subschemes,
  and `(π ⁻¹ᵁ U a).ι` is the node's inclusion ι_a.
- Quasi-compactness of each Z_a is
  `hZ : ∀ a : A, CompactSpace (h ⁻¹ᵁ U a).toScheme`.
  CompactSpace includes no Hausdorff condition.
- The chart maps are the dependent family `e`. The hypothesis
  `he : ∀ a : A, IsOpenImmersion (e a)` says each is an open immersion.
- The over-S_a requirement is `heS : ∀ a : A, e a ≫ (π ∣_ U a) = h ∣_ U a`.
  Both sides have target `(U a).toScheme`, so this is exactly the stated
  equality over the base open, not merely an equation of underlying functions.
- Compatibility on Z_a ∩ Z_b is `heq`. Its common source is the open
  `(h ⁻¹ᵁ U a ⊓ h ⁻¹ᵁ U b).toScheme`; `Z.homOfLE inf_le_left` and
  `Z.homOfLE inf_le_right` are its two inclusions. The equality is between
  the resulting scheme morphisms into Y after `e a` and `e b` and the ι_a.
- The conclusion supplies `∃ c : Z ⟶ Y`. Its first conjunct gives every
  restriction `(h ⁻¹ᵁ U a).ι ≫ c = e a ≫ (π ⁻¹ᵁ U a).ι`.
- Its next conjuncts are `c ≫ π = h`, `QuasiCompact c`, and
  `IsOpenImmersion c`, respectively the over-base equation and both properties.
- Its last conjunct quantifies over every `c' : Z ⟶ Y` and states that the
  same restriction equations imply `c' = c`. Uniqueness is therefore among
  all extending morphisms, without requiring c' to have the extra properties.

Dependency declarations read and used (all statement dependencies are public imports):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `pqf-def-affine-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `AlgebraicGeometry.IsAffineHom`.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-finite-type-morphism`: the recorded module
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; its recorded quasi-compact
  clause is `AlgebraicGeometry.QuasiCompact`, defined in the imported
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`. Local finite type is
  not assumed or concluded, since the item only uses the quasi-compact clause.

The Mathlib matches of proof dependencies are imported as proof imports:
`Scheme.Cover.glueMorphisms`, `Scheme.Cover.ι_glueMorphisms`, and
`Scheme.Cover.hom_ext` from `Mathlib.AlgebraicGeometry.Gluing`;
`IsOpenImmersion.of_forall_source_exists` from
`Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion`;
`Scheme.compactSpace_of_isAffine` from `Mathlib.AlgebraicGeometry.AffineScheme`
(available through the affine imports), `quasiSeparatedSpace_of_isAffine` and
`quasiCompact_of_compactSpace` from
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`; and
`IsZariskiLocalAtTarget.of_iSup_eq_top` from
`Mathlib.AlgebraicGeometry.Morphisms.Basic`.
All names above are in the AlgebraicGeometry namespace except CompactSpace.
Restriction and inclusion operations are the existing Mathlib
`morphismRestrict`, `Scheme.homOfLE`, and `Scheme.Opens.ι`.

Edge cases checked before writing: A may be empty (the covering equation then
forces S empty, and the existence of h and π forces Z and Y empty); the
restriction and uniqueness conditions still make sense. Infinite covers and
independently large index universes are allowed by `A : Type v`. Empty members,
repeated members and non-affine intersections cause no typing issue. There is
no finite-cover, nonempty-index, global injectivity, quasi-separatedness of h,
or compactness/separation hypothesis on S. The proof only uses the
quasi-separatedness of each affine target chart. Empty Z with nonempty Y is
also permitted. For the identity one-chart cover, this specializes to the
usual compact-source open immersion into an affine target.

Searches made using the prescribed msearch.py wrapper with group Q76 and this item:

- LeanFinder query: "Compatible open immersions over inverse images of an affine
  open cover with quasi compact sources glue to a unique quasi compact open immersion".
  Result: eight hits, including Scheme.Cover.instIsOpenImmersionFromGlued and
  Scheme.exists_isOpenCover_and_isAffine. None is this compatible-chart theorem.
- Loogle query: `AlgebraicGeometry.IsOpenImmersion, AlgebraicGeometry.QuasiCompact`.
  Result: twelve hits, including IsImmersion.isImmersion_iff_exists_of_quasiCompact
  and instQuasiCompactOfIsLocallyNoetherianOfIsOpenImmersion. None matches.
- Mathlib grep query: `glueMorphisms|of_openCover_source|quasiCompact_iff_forall_affine`
  in AlgebraicGeometry. Result: ordinary gluing, source locality and
  quasi-compactness criteria, but no theorem with this combined statement.
- rg in lean/WeilConjectures and lean/Sheaf for the item id, the proposed name,
  `affineBaseOpenImmersion`, `affine_base_open_immersion`, `glueMorphisms`,
  `of_openCover_source`, and combinations of gluing/open immersion/affine-cover
  terminology. The prescribed `grep -rn` of the item id in WeilConjectures
  returned no match. The other searches found generic scheme morphism gluing,
  including WeilConjectures.Mathlib.AlgebraicGeometry.Gluing, and unrelated
  specific constructions; none supplies this theorem. No existing definition
  is duplicated.

Validation: scompile.py compiled this file separately in sandbox and library
module mode successfully, with no errors or warnings. All variables and
universes are explicit, and the file starts with `module`.

## Second reading by Q76

I reopened the node and the completed module for a separate reading in this
worker session; the dispatcher's explicit instruction forbids spawning another
agent. The maintainer provides the independent review on delivery.

The original and Lean statements have the same three schemes and two morphisms,
affine π, arbitrary affine open cover, compact source charts, open immersion
chart maps, equality over each base chart, and equality on intersections into Y.
In particular, `heS` is an equality with target the open base subscheme, and
`heq` uses the intersection of the source preimages, not an affine replacement
of that intersection. The conclusion has existence, all restrictions, the
base equation, quasi-compactness, open immersion and uniqueness among every
morphism satisfying the restrictions. A remains arbitrary, including empty;
there is no hidden global injection or quasi-separatedness assumption. No
mismatch was found, and no change to the node statement was made. The proof
plan's five steps and empty-cover argument were checked against the node.
