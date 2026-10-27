## Worker report

The module `Sheaf.AlgebraicGeometry.SpacePushoutCompatibleEtaleCharts` states
`AlgebraicGeometry.AlgebraicSpace.exists_pushout_compatible_etale_charts` and
`AlgebraicGeometry.AlgebraicSpace.compatible_etale_charts_pushout`. Both proofs are
`sorry`. There are no new definitions or additional postponed obligations.

Sources read: Stacks `spaces-pushouts.tex`, `lemma-pushout-along-thickening-schemes`
(07SY), `lemma-pushout-along-thickening` (07VX), and the proof of
`lemma-equivalence-categories-spaces-over-pushout` (07W0), including
`equation-cube-over` (07W2); `spaces-more-morphisms.tex`,
`lemma-thickening-equivalence` (05ZS). The compatible charts in this node are the
charts of the *arbitrary compatible pair* of spaces, rather than only an atlas
of the base pushout. The proof docstrings reproduce all four node proof steps.

Hypothesis and clause correspondence:

- The scheme B and the size convention are `{B : Scheme.{u}}` and explicit
  `universe u`; all schemes over B are `Over B`, and spaces are the existing
  `AlgebraicSpace B`. Nothing assumes that B or any chart is nonempty.
- `T T' S : Over B`, `i : T ⟶ T'`, and `a : T ⟶ S` are precisely the given
  base span. `[IsClosedImmersion i.left]` and `hi : IsHomeomorph i.left.base`
  express an arbitrary thickening, with no global nilpotence exponent.
  `[IsAffineHom a.left]` says exactly that the scheme morphism is affine.
- `X Y : AlgebraicSpace B`, `x : X ⟶ schemeSpace S`, and
  `y : Y ⟶ schemeSpace T'` are the two arbitrary relative algebraic spaces.
  `φ` is the isomorphism of their actual sheaf fibre products. `hφ` states that
  it is over T (equality of the second sheaf projections).
- The node's P does not occur in the assertions about charts. Its existence and
  role in the proof are provided by the recorded pushout dependency; it is not
  introduced as an extra assumption. The second theorem quantifies over the
  specified Z, its two inclusions `j`, `k`, and `hz : IsPushout ... j k`.
  Its span is exactly `U → X` and `U → Y`, the latter composed with `φ.hom`.
- In the first theorem, `X₁ : Over B` and `c : schemeSpace X₁ ⟶ X` are the
  arbitrary scheme chart. `hc` and `hcs` use the existing representable etale
  and representable surjective predicates. Every B-structure on X₁ is retained.
- The existential gives schemes `Y₁`, `U₁`, the map `d` to Y, scheme maps
  `r : U₁ ⟶ X₁`, `s : U₁ ⟶ Y₁`, and `t : schemeSpace U₁ ⟶ U`.
  `IsEtale d.hom.hom ∧ IsSurjective d.hom.hom` gives the required cover of Y.
  The first `IsPullback` identifies U₁ with X₁ ×_X U, hence X₁ ×_S T.
  The second identifies the same U₁ with Y₁ ×_Y (Y ×_T' T), hence Y₁ ×_T' T.
  Its projection is `t ≫ φ.hom`, so the induced overlap isomorphism is over U
  and compatible with the given φ, not merely an abstract isomorphism.
- In the second theorem, `X₁ Y₁ U₁`, `c d`, the four chart properties, `r s t`,
  and the two pullback witnesses `hr hs` quantify over *every* such compatible
  pair. This is an equivalent universal-property presentation of the specified
  overlap isomorphism: both fibre products are represented by the same U₁,
  with their projections to the overlap related by φ.
- The first conjunct asserts existence of a scheme pushout using
  `IsPushout r.left s.left j₁.left k₁.left`. The second conjunct quantifies
  over every scheme pushout with those inclusions; no choice of pushout data
  is made in a definition.
- The map `e : schemeSpace Z₁ ⟶ Z` satisfies the two equations on the pieces,
  characterizing the induced pushout map. Its representable etaleness and
  surjectivity are the next two conjuncts. The final two `IsPullback` clauses
  are exactly the chart squares with horizontal maps `j₁,j` and `k₁,k`.
- There are no flatness or local finite presentation hypotheses on x, y or
  other arbitrary structural maps. Etale chart maps retain, of course, their
  intrinsic etale properties. There is no separation or finite-order assumption.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective` (full signatures and docs).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`, with their docstrings. The actual fibre product
  used in the statement bundles the first theorem's algebraic-space property.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `schemeSheaf_isAlgebraicSpace`, `enlargedFibreProduct`,
  `enlargedFibreProductFst`. The existing owning nodes
  `def-trf-scheme-algebraic-space` and `def-sfb-space-sheaf-fibre-product` are
  added to stmt_deps; their definitions are reused without any copies.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; `Mathlib.AlgebraicGeometry.Morphisms.Affine`:
  `IsAffineHom`. `Mathlib.Topology.Homeomorph.Defs`: `IsHomeomorph`.
- `Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout`:
  `exists_affineThickeningPushout`, `scheme_affineThickeningPushout`, and
  `affineThickeningPushout_recovery`, read in full. The first is the existence
  interface; the second upgrades scheme pushouts to algebraic spaces; the last
  supplies the recovery squares used in proof step 3. Its existing imports also
  supply the established point topology and point map; neither is redefined.
- Proof-only Mathlib imports `Mathlib.AlgebraicGeometry.Morphisms.Separated`
  and `Mathlib.AlgebraicGeometry.Limits` cover the already stated Mathlib leaf
  `lem-weil-pbc-affine-morphism-permanence`. Its recorded affine base-change,
  affine-source, quasi-compactness, separatedness and finite-coproduct declarations
  were read. The remaining three proof-only space nodes (thickening base change,
  thickening etale scheme equivalence, pushout etale base change) have no Lean
  record yet in this checkout and are not needed to *state* these theorems.
  Their proof steps remain explicitly cited in the docstrings; no replacement
  hypothesis for any of their conclusions is introduced.

Edge cases checked before writing: empty X forces any surjective chart X₁ to
be empty; the compatible overlap and thickening then give the corresponding
empty restrictions, without a nonempty assumption. Empty T gives empty T' and
empty Y, so the pushout reduces to X and the second chart is empty. If i is an
identity, the claims reduce to transporting charts through φ. If a is an
identity, the pushout is the thickened Y-side and the chart lifting is exactly
05ZS. Nil ideals need only be locally nilpotent; neither the hypotheses nor the
proof plans introduce a finite nilpotence exponent. Nonflat x and y are retained.
The universal quantifier over all scheme pushouts avoids dependence on a chosen
presentation or on any particular lifted chart.

Searches actually run with msearch.py, group NV and this item:

- LeanFinder, `Compatible etale scheme covers of algebraic spaces and their
  pushout along a thickening`: eight hits, concerning scheme etale categories,
  scheme gluing, and etale composition; no compatible algebraic-space pushout
  chart statement.
- LeanSearch, `Compatible etale scheme charts for pushouts of algebraic spaces
  along a thickening`: eight hits, concerning IsEtale, sites, formally etale
  rings, and subscheme charts; no matching statement.
- Loogle, `IsPushout, IsEtale`, then
  `CategoryTheory.Limits.IsPushout, AlgebraicGeometry.IsEtale`: the service did
  not recognize the IsPushout identifier; these are unsuccessful searches,
  not evidence of absence.
- Mathlib grep, `etale.*pushout|pushout.*etale|Etale.*pushout|pushout.*Etale`
  in AlgebraicGeometry: zero hits.
- Local rg in both `lean/WeilConjectures` and `lean/Sheaf` for this node id,
  compatible-chart/pushout terms, and `exists_compatible` chart/cover names:
  no existing exact theorem. The AlgebraicStackRimSchlessinger proof cites this
  node, but does not state its result. The existing SpaceAffineThickeningPushout
  module is used for the base result, not duplicated.
- The upstream name index has no entry for this node id. Searches for
  `schemeSpace` and `enlargedFibreProduct` located their already-owned definitions.

No statement correction or disputed statement is needed. Only lean and the
addition of the two already-landed definition owners to stmt_deps are changed.

## Second reading by NV

This is the worker's final rereading; the maintainer independently reviews the
delivery. I rechecked the signatures against the node and the cited Stacks cube.
The potentially significant mismatch was whether the two chart overlap
representations remember φ: the right-hand square has `t ≫ φ.hom`, while the
left-hand square has `t`. Together with `hφ`, this preserves both the U-map and
the T-map. I also checked the direction of both final squares: their common
rightward vertical map is e, and their bottom inclusions are j and k. The
scheme-pushout quantifier uses the underlying schemes, so it is a pushout
against arbitrary scheme targets, rather than only targets over B. No mathematical
mismatch was found. Compilation required explicit source annotations on the
Yoneda maps of i and a; these do not change any hypotheses.
