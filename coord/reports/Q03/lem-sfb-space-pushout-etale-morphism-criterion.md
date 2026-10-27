## Worker report

States `AlgebraicGeometry.AlgebraicSpace.existsUnique_chartwiseEtale_affineThickeningPushout`
in `Sheaf.AlgebraicGeometry.SpacePushoutEtaleMorphismCriterion`. Its sole theorem has
proof `sorry`; there are no new definitions or helper axioms. The mathematical statement is unchanged. The repair below repoints its chartwise-etale
citation and dependency to the owning definition node; Lean and its record are unchanged.

Read the local Stacks source `spaces-pushouts.tex`,
`lemma-equivalence-categories-spaces-pushout-flat` (Tag 07W3), especially (5) and its
proof of (1)--(5), together with `lemma-pushout-along-thickening` and
`lemma-equivalence-categories-spaces-over-pushout`. This is the forward construction
assertion, not the final flat counit assertion. The theorem docstring reproduces the
four accepted proof steps and their dependency nodes.

Clause-by-clause correspondence:

- Base scheme and algebraic spaces over it: `{B : Scheme.{u}}` and
  `A A' C Q X Y Z : AlgebraicSpace B`. All morphisms are in that category and hence
  over B. The explicit universe `u` follows the recorded size convention; there is
  no independent smaller universe of test schemes.
- Thickening A into A+: `i : A ⟶ A'`,
  `hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`,
  and `hiTop : IsHomeomorph (mapPoint i.hom.hom)`. These say representable closed
  immersion on every scheme base change and homeomorphism on point spaces.
  The existing `pointTopologicalSpace` is the final topology for representable
  etale scheme charts, equivalently the quotient topology from an atlas.
- Affine A to C: `a : A ⟶ C` and
  `ha : IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) a.hom.hom`.
  This quantifies over all scheme tests, not only one chosen atlas.
- Base pushout: `j : C ⟶ Q`, `b : A' ⟶ Q`, and `hQ : IsPushout a i j b`.
  This is a pushout in algebraic spaces, with all algebraic spaces as targets.
- Etale component maps: `x : X ⟶ C`, `y : Y ⟶ A'`,
  `hx : IsChartwiseEtale x`, `hy : IsChartwiseEtale y`. The definition tests every
  representable etale scheme-source chart, exactly as the node requests.
- Specified isomorphism over A: `φ : enlargedFibreProduct x a ≅
  enlargedFibreProduct y i`; `hφ` says its underlying sheaf morphism commutes with
  the second projections to A. Thus it is the specified relative isomorphism,
  not merely an isomorphism of underlying spaces.
- U and its maps: `enlargedFibreProduct x a` is U = X times_C A;
  `enlargedFibreProductFst x a` is U to X, and
  `φ.hom ≫ enlargedFibreProductFst y i` is its specified map to Y.
- Source pushout: `Z`, inclusions `u : X ⟶ Z`, `v : Y ⟶ Z`, and `hZ` assert the
  pushout of exactly these overlap maps. This is the pushout formed in the node;
  existence is the already recorded affine-thickening pushout theorem, since
  the two overlap legs are respectively affine and a thickening by base change.
- Conclusion: `∃! p : Z ⟶ Q, u ≫ p = x ≫ j ∧ v ≫ p = y ≫ b ∧ IsChartwiseEtale p`.
  The equations characterize the induced morphism and retain both restrictions.
  Its existence follows from the overlap compatibility, and its uniqueness among
  all maps with those restrictions is already the universal property `hZ`.
  The additional conclusion is precisely chartwise etaleness.
- No separatedness, quasi-compactness, Noetherian, finite-order nilpotence, or
  finite-presentation assumptions occur. In particular there is no candidate
  space over Q recovering X and Y, nor recovery or cartesian hypotheses on p.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, and `IsAlgebraicSpace` (full fppf-sheaf
  subcategory, scheme-test representability, and atlas condition).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, which supplies the actual sheaf fibre product
  underlying the bundled overlap. Its other two statements give covering base
  change and the scheme-source special case.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, closed embedding plus surjective stalk
  maps; `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`, affine
  inverse images of affine opens.
- `Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout`:
  `exists_affineThickeningPushout`, `scheme_affineThickeningPushout`, and
  `affineThickeningPushout_recovery`. The same scheme-test and point-topology
  thickening interface is used here, without adding its recovery conclusion
  as a hypothesis. These public dependencies also expose `mapPoint` from
  `ProperCurveModuli` and `pointTopologicalSpace` from `AlgebraicSpacePointTopology`.
- `def-sfb-space-chartwise-etale-morphism` owns
  `AlgebraicGeometry.AlgebraicSpace.IsChartwiseEtale` in
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` (existing definition, line 47).
  It renders `hx`, `hy`, and the conclusion exactly.
- Proof dependency `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`:
  `chartwise_etale_permanence`, using the existing `IsChartwiseEtale`,
  `enlargedFibreProduct`, and `enlargedFibreProductFst` from its public dependency
  `EnlargedEtaleRingedSite`. These definitions are reused without any copies.
- `def-weil-size-convention` has no declaration by design; explicit universe
  polymorphism renders the metatheoretic convention.
- Proof-only imports for the already recorded proof nodes:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`
  (`representable_etale_scheme_tests`) and
  `Sheaf.AlgebraicGeometry.SpaceEtaleSourceAtlasDetection`
  (`etale_source_atlas_detection`). The other four proof-only nodes
  `lem-sfb-space-thickening-etale-scheme-equivalence`,
  `lem-sfb-space-thickening-base-change`, `lem-sfb-space-pushout-lifted-atlas`,
  and `lem-sfb-scheme-infinitesimal-etale-patching` have no recorded Lean module;
  no import is invented for them. They are proof inputs only, not missing
  notions needed to type this statement.

Edge cases checked before writing: the identity thickening makes the base pushout
C and the induced map the given etale X to C. Taking a to be the identity makes
the pushout A+ and gives the other component map. Empty overlaps give coproduct
pushouts and etale maps on both pieces; X and Y may both be empty. No nonempty
binder excludes these cases. Arbitrary non-separated spaces are admitted.
The homeomorphism condition allows arbitrary locally nilpotent thickenings,
without a uniform nilpotence exponent. A nontrivial overlap automorphism is
retained by φ and hZ; no identity gluing is silently selected.

Searches actually run on 2026-10-24 (logged by msearch.py):

- LeanFinder: "The map induced by compatible etale components between
  infinitesimal pushouts of algebraic spaces is etale". Eight hits, including
  scheme etale composition/cancellation and base change; no algebraic-space
  infinitesimal-pushout criterion.
- Loogle: `"pushout", "Etale"`. Zero hits.
- Mathlib grep in AlgebraicGeometry:
  `pushout.*[Ee]tale|[Ee]tale.*[Pp]ushout|thickening.*pushout`. Zero hits.
- LeanSearch: "An etale triple over a thickening and an affine morphism induces
  an etale morphism between pushouts of algebraic spaces". Eight hits, consisting
  of scheme/ring etaleness and permanence, not this statement.
- Local rg in WeilConjectures and Sheaf:
  `pushout.*etale|etale.*pushout|affineThickeningPushout|pushout_etale`
  (case insensitive). Ring pushouts, torsors, and the recorded base-pushout
  theorem occur; no induced etale morphism criterion. Exact node-id grep in
  WeilConjectures returned no hits; exact proposed declaration-name rg across
  Mathlib, WeilConjectures and Sheaf returned no hits.

Initial validation: prescribed scompile.py server compile passed for the new module,
with no errors or warnings. No new node, dependency module, or statement dispute
was necessary. The returned delivery requires the citation-only correction below.


## Return repair: H2

Compared the retained delivered node against current main: only `lean` differed
before repair, and its Lean file is the retained returned version. Read the landed
`def-sfb-space-chartwise-etale-morphism` record and its actual definition at
`EnlargedEtaleRingedSite.lean:47`. This is exactly the predicate in `hx`, `hy`, and
the conclusion. Replaced `lem-trf-space-chartwise-etale-permanence` in `stmt_deps`
with that definition node, and repointed the statement's chartwise-etale citation.
Kept permanence in proof step 4, its `uses`, and `proof_deps`. The complete Lean
module and `lean` record are unchanged, as requested. No second copy of a notion
is introduced. This repairs the sole returned point on immutable head 5a228a53d35d.

## Statement corrected

This is a citation and dependency ownership correction only. The old statement is
recorded verbatim in `statement_change.old_statement`; its sole text change is
`[lem-trf-space-chartwise-etale-permanence]` to
`[def-sfb-space-chartwise-etale-morphism]`. No mathematical text changes. The source
is Stacks Tag 03FR, the same chartwise-etale predicate used by Tag 07W3 (5).
The previous `stmt_deps` are recorded in `statement_change.old_stmt_deps`; the proof
and proof dependencies are unchanged.

Citer audit: searched every node's `stmt_deps` and `proof_deps`; exactly one cites
this item: `lem-sfb-space-pushout-etale-base-change`, holds true, because its proof
uses the same unchanged etaleness criterion. The occurrence in
`lem-sfb-space-pushout-lifted-atlas` is not a dependency edge. No citer is edited.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
