## Worker report

Statement-only delivery for `lem-sfb-space-ample-fibre-section-lifting` in
`Sheaf.AlgebraicGeometry.SpaceAmpleFibreSectionLifting`, declaration
`AlgebraicGeometry.AlgebraicSpace.exists_lift_section_of_schematic_fiber_isAmple`.
The sole theorem has proof `sorry`. No definition or helper theorem is introduced.
The source was read at spaces-divisors.tex, lines 3140–3267: Stacks 0D39,
lemma-ample-on-fibre, final assertion with the coherent module equal to O_X.

Hypotheses and clauses, in the order of the node:

- Noetherian scheme T: `(T : Scheme.{u}) [IsNoetherian T]`. Mathlib's
  `isNoetherian_iff_of_finite_iSup_eq_top` identifies this with the node's finite
  affine cover by spectra of Noetherian rings; this includes the quasi-compactness
  requirement, rather than merely local Noetherianity.
- Proper algebraic space over T: `(X : AlgebraicSpace T)` and
  `(f : X ⟶ schemeSpace (Over.mk (𝟙 T))) (hf : MapIsProper f)`.
  The target is the actual representable sheaf of T over itself. Its structural
  morphism is unique, so a scheme test W has composite to T equal to W.left.hom.
  `MapIsProper` is exactly separated, finite type and universally closed.
- The line module is `(L : X.Modules) (hL : X.IsLineModule L)`, using the recorded
  small-etale module category and local triviality predicate, without a copied notion.
- Pullback and its tensor-power identification: the existing
  `lineTestFamily X L hL` is the canonical cartesian realization selected from
  `exists_linePresentation`, which fixes it up to the unique isomorphism inducing
  the identity on the given small-etale module. It is not an arbitrary family of
  invertible modules. Its `module W` is the ordinary tensor pullback to W, and
  `powerMap j d` is the actual tensor section 1 tensor s followed by the recorded
  `boundaryPullbackPowIso` and `boundaryTensorPowIso`. Its naturality includes the
  canonical unit in degree zero. This is a coordinate presentation of the node's
  canonical ringed-topos pullback, not a replacement map or extra assumption.
- The point is `(t : T)`; the schematic fibre is `F : SchemeTests X.obj.obj`
  with `p : F.left ⟶ Over.mk (T.fromSpecResidueField t)` and the displayed
  `hF : IsPullback ...`. Thus the representing scheme is exactly the fibre of X
  over Spec kappa(t), with both projections. No scheme representation for X is
  assumed. Spec kappa(t) and its canonical map are Mathlib's actual constructions.
  Quantification over a representing scheme is the usual presentation of the
  hypothesis that this fibre is a scheme; every such representation is allowed.
- The pulled-back ordinary line is `(lineTestFamily X L hL).module F`.
  Its `IsInvertible` instance is already `TestLineFamily.invertible F` and is
  not an additional hypothesis. `hample` uses the recorded absolute `IsAmple`
  on this actual fibre scheme and line.
- The uniform nonnegative bound and every larger degree are
  `∃ d₀ : ℕ, ∀ (d : ℕ), d₀ ≤ d → ...`. This is precisely nonnegative integer
  degrees, including d = 0 whenever the chosen bound is zero.
- Every prescribed section is
  `v : Γ(((lineTestFamily X L hL).module F).tensorPow d, ⊤)`.
- The neighbourhood is `∃ (U : T.Opens) (_ : t ∈ U) ...`, inside the quantifiers
  for d and v, so it may depend on both.
- A section of L^d on X_U is written out as its compatible family `s W hW` on
  ALL scheme tests W whose structural map lands in U. The condition
  `Set.range W.left.hom ⊆ (U : Set T)` says precisely that W factors through X_U.
  The equation for every triangle j is the ordinary tensor-pullback compatibility
  via `powerMap j d`. The existing cartesian descent of this line identifies these
  families with module-sheaf sections: restriction to etale charts gives the
  small-etale section; any section pulls back to all tests; descent and
  cartesianness give uniqueness. One can also read precisely this limit
  description in `SpaceSectionAlgebra.sections` (not used as an extra hypothesis).
  Thus the compatible-family condition is the definition of the type of sections,
  not a strengthening of the lifting conclusion.
- `hFU` places the fibre among those tests. It is only the typing witness that
  the fibre lies over U: `p` is over T and `T.fromSpecResidueField_apply` makes
  its image the fixed point t, which belongs to U. The equality `s F hFU = v`
  is the pullback equality under the canonical tensor-power comparison.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`,
  `isNoetherianRing_iff_ideal_fg`; scheme Noetherianity is the existing Mathlib
  `AlgebraicGeometry.IsNoetherian`, not a new predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `Modules`,
  `IsLineModule` (publicly supplied by the imports).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`: the recorded canonical ringed
  site interface, retaining `EnlargedEtaleRingedSite.schemeSpace` by public import.
  This is the latest recorded dependency, read with its small-site structural map.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the existing
  tensor interface; the scheme powers used here are
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible.tensorPow`.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `Scheme.Modules.scheme_zariski_etale_quasiCoherent_equivalence`, including its
  open-section normalization and identification of invertible and line modules.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `tensorPow`.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`.
- Added already-landed statement dependency `def-trf-space-line-module-proj-input`:
  module `Sheaf.TraceFormula.SpaceLineModuleProjInput`, `lineTestFamily`,
  `linePresentation`, `exists_linePresentation`, publicly reexporting
  `SchemeTests`, `TestLineFamily.module`, `invertible`, and `powerMap` from
  `SpaceLinePresentationDefs`. Its full normalization and uniqueness were read.
  This adds the declaration needed for canonical pullback to arbitrary scheme tests;
  it neither repairs nor redefines any dependency.

All recorded proof-dependency modules are imported with plain import except where
also statement dependencies (then public import). The three unstated proof nodes
`lem-sfb-space-proper-base-change`, `lem-sfb-space-conormal-uniform-vanishing`, and
`lem-sfb-space-closed-immersion-quasi-coherent-modules` have no Lean module on the
current base and therefore no import to add. The Mathlib leaf for localization
Noetherianity is already reached through the scheme Noetherianity import; the
Mathlib enough-injectives module is imported explicitly. The proof docstring carries
all six accepted proof steps and their dependencies.

Edge cases checked against the source and the types:

- Empty T: no t exists, so the pointed assertion is vacuous, as in the node.
- Empty fibre: its only section is zero and is lifted by the zero compatible family;
  no nonemptiness is imposed on F, X, or their scheme tests.
- d = 0 is the existing zeroth tensor power, the structure module. The theorem
  only requires it if d₀ = 0; it does not force all degree-zero fibre functions to lift.
- A field base, nilpotent local base, nonflat proper X, arbitrary characteristic,
  and disconnected fibres are not excluded. No completeness, flatness or
  projectivity hypothesis has been inserted.
- All schemes and test schemes have the same geometric universe u, as the existing
  space and size-convention interface requires. The collection of tests lives in
  u+1; the displayed dependent family is allowed to live there. No equality of
  independent site and coefficient universes is imposed.

Searches actually run:

- msearch.py leanfinder: “Sections of high tensor powers of an ample line bundle on
  a schematic fibre of a proper algebraic space lift over an open neighbourhood”.
  Eight hits, all ordinary scheme localization/Proj/spreading-out results; none is
  the algebraic-space lifting theorem.
- msearch.py loogle: `IsAmple, sections`. No hits; service reported unknown
  identifier IsAmple. This query is inconclusive, not evidence of absence.
- msearch.py grep, Mathlib/AlgebraicGeometry:
  `ample.*fibre|ample.*fiber|fibre.*section|fiber.*section`.
  One unrelated ProjectiveSpectrum.StructureSheaf hit.
- msearch.py leansearch: “For a proper algebraic space over a Noetherian scheme
  sections of high powers of an ample invertible sheaf on a schematic fibre lift
  locally”. Eight hits, including IsNoetherian and ordinary localization results,
  none the item.
- rg in lean/WeilConjectures/AlgebraicGeometry for the same keywords: only unrelated
  affine fibre sections, formal functions and other scheme results. The exact item
  id has no hit in lean/WeilConjectures.
- rg in lean/Sheaf and lean/WeilConjectures for ample-fibre/section keywords found
  `Sheaf.AlgebraicGeometry.AmpleFibreSectionLifting`: its full signature was read;
  it assumes X is a scheme, so does not state this item. Further reading found the
  reusable canonical cartesian realization and its power maps; none is this lemma.
- rg for the new full declaration name across Mathlib, WeilConjectures and Sheaf
  found no existing declaration.

No statement correction, disputed statement, missing definition node, or dependency
repair is needed. Only the item's lean record and its additional already-landed
statement dependency change.

Validation: scompile.py Q09 lem-sfb-space-ample-fibre-section-lifting compiled the
file in both sandbox and library modes (5.3 s and 2.2 s); no errors or non-sorry
warnings. All variables and universes are explicitly bound; autoImplicit and
relaxedAutoImplicit are disabled.

## Second reading by Q09

Independent second reading by the maintainer's review service (NT-cc-Q09-7f040a5c8). The
delivered section with this heading was a self-check by the same worker. This section
replaces it. The worker report above is unchanged.

Node clauses and their Lean (source: spaces-divisors.tex, Tag 0D39, final surjectivity
with F = O_X):

1. T Noetherian scheme (finite affine cover by Noetherian spectra): `(T : Scheme.{u})
   [IsNoetherian T]`. Mathlib's global Noetherian notion (quasi-compact + locally
   Noetherian) is exactly this. OK.
2. f : X → T proper morphism of algebraic spaces: `X : AlgebraicSpace T`,
   `f : X ⟶ schemeSpace (Over.mk (𝟙 T))`, `hf : MapIsProper f`. MapIsProper =
   MapIsSeparated ∧ MapIsFiniteType ∧ MapIsUniversallyClosed (def-sfb-space-morphism-properties).
   schemeSpace (Over.mk (𝟙 T)) is the terminal representable sheaf, so f is the structure map. OK.
3. L a line module on the small étale site: `(L : X.Modules) (hL : X.IsLineModule L)`. OK.
4. Pullback/tensor powers: `lineTestFamily X L hL` (def-trf-space-line-module-proj-input,
   landed 2026-10-17, before the base; it is a definition node, so it may be added to stmt_deps).
   It is `.choose` of `exists_linePresentation`, which pins the realization up to the unique
   étale-compatible cartesian isomorphism, so the statement does not depend on the choice.
   `powerMap j d` uses the tensor-pullback unit pinned on values (1 ⊗ η) by
   `exists_tensorPullbackAdjunction`, followed by `boundaryPullbackPowIso` and `boundaryTensorPowIso`.
   It is the canonical comparison (L^{⊗d})_W ≅ (L_W)^{⊗d}, not an arbitrary map. `tensorPow 0 = 𝟙_`
   (= O), as the node requires. OK.
5. t ∈ T, X_t = X ×_T Spec κ(t) a scheme: `F : SchemeTests X.obj.obj`,
   `p : F.left ⟶ Over.mk (T.fromSpecResidueField t)`, `hF : IsPullback F.hom (yoneda.map p)
   f.hom.hom (yoneda.map (Over.homMk …))`. This is a presheaf pullback square, i.e. F.left
   represents the fibre product, with both projections. Limits of sheaves are computed in
   presheaves, so this is the sheaf fibre product. Every representing scheme is allowed and none is
   assumed for X. OK.
6. L_t ample on X_t: `hample : Scheme.Modules.IsAmple F.left.left ((lineTestFamily X L hL).module F)`.
   This is the absolute ampleness of the actual pulled-back ordinary invertible module. The
   IsInvertible instance comes from the family and is not an extra hypothesis. OK.
7. ∃ d₀ ≥ 0, ∀ d ≥ d₀, ∀ v ∈ Γ(X_t, L_t^{⊗d}): `∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ v : Γ(… .tensorPow d, ⊤)`.
   The order of the quantifiers is the node's. OK.
8. ∃ open U ∋ t (depending on d, v) and ṽ ∈ Γ(X_U, L^{⊗d}|_{X_U}) pulling back to v: `∃ U, t ∈ U`,
   `hFU`, and a family `s W hW` on all scheme tests W with range ⊆ U, compatible under
   `powerMap j d`, with `s F hFU = v`. A test W → X factors through X_U = X ×_T U iff
   W → T lands in U. A section of the quasi-coherent line module L^{⊗d} on X_U is the same as such
   a compatible family on all scheme tests. Restriction to étale charts gives the étale section.
   Injectivity and surjectivity hold by étale descent along W ×_X U_i → W, which is a scheme because
   the diagonal of X is representable. So the conclusion is neither weaker nor stronger. `hFU` is
   a Prop witness that always holds, since F.left.hom = p.left ≫ fromSpecResidueField t has
   image {t} ⊆ U. Evaluation at F is the pullback to the fibre under the canonical
   tensor-power identification. OK.

Edge cases: empty T (vacuous); empty fibre (v = 0, zero family); d = 0 (O, only forced if d₀ = 0);
nilpotent or field local rings, non-flat X, any characteristic: none excluded. Universes:
a single geometric universe u, as the space interface fixes. No extra assumption.

Records: the statement text is unchanged from the base. The only node change is the added landed
definition stmt_dep def-trf-space-line-module-proj-input, which the Lean uses. The base theorem
stmt_deps (lem-trf-space-enlarged-etale-ringed-site-model for schemeSpace,
lem-trf-scheme-zariski-etale-quasi-coherent-equivalence) predate the delivery. `lean.statement`
is verbatim the signature in the file. No definitions, so nothing is hollow. The proof is `sorry`.
The module and theorem docstrings carry Tag 0D39 and `(blueprint: …)`, and the theorem docstring
gives the six proof steps. No pro-étale substitute is used.

Searches: `exists_lift_section_of_schematic_fiber_isAmple` occurs nowhere else in lean/Sheaf or
lean/WeilConjectures. The scheme-case `Sheaf.AlgebraicGeometry.AmpleFibreSectionLifting`
(`exists_lift_section_of_fiber_isAmple`) assumes X is a scheme, so it is not this item.

Mismatches found: none in the Lean or the records. Changed: only this section (H11).
