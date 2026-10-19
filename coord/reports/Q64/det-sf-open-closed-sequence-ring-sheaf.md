## Worker report

The supplied sandbox contained brief markers but no worker module, node copy or report.
The initial statement draft made during this reading was superseded by the repairs below.
The delivery states the unchanged blueprint node in
`Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf`.
Its main declaration is
`AlgebraicGeometry.ProEtale.proEtale_openClosed_sequence_ring_sheaf`.
There is one postponed theorem and eight construction helpers, all with real data.
No target statement, natural-language node statement, dependency statement or proof was changed.

Ring sheaves are encoded by the existing `MonObj` structure on abelian sheaves, and
module sheaves by the existing `CategoryTheory.Mod` category. This is the same arbitrary,
possibly noncommutative encoding already published in
`Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits`,
`AlgebraicGeometry.Scheme.closed_inverseImage_preserves_limits`.
It is not a new category or a new definition of a ring. The transparent specializations
`ringSheafInverseImage`, `ringSheafDirectImage` and `ringSheafOpenExtension` retain the
existing underlying sheaves, actions and adjunctions. The two square helpers merely fix
coefficient transport along the chosen cartesian square. Their multiplicativity is a
conclusion, not an additional assumption.

The dependency interfaces read include Mathlib's `Scheme`, `IsOpenImmersion`,
`IsClosedImmersion`, `QuasiCompact`, `pullback`, `pullback.fst`, `pullback.snd` and
`ComposableArrows.Exact`; `CategoryTheory.ringedSiteModules` in
`Sheaf.CategoryTheory.RingedSiteModules`; and the original arbitrary-site inverse-image
functors reexported by the current inverse-image record. In particular, the finite,
commutative intrinsic adjunction recorded as that node's primary declaration is not
applied to arbitrary coefficients here. The original public module
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage` supplies the same `ProEtale.upperStar`,
`lowerStar` and `upperStarLowerStarAdjunction` used by the published module-object API.
The current pro-etale-site record supplies additional derived constant-coefficient
constructions; the small site itself remains `Scheme.ProEt.topology`.

Construction APIs read in the published framework:
`Functor.mapMod`, `Mod.comap`, `Adjunction.mapModAdjunction`,
`Adjunction.mapModLeft`, `Adjunction.mapModLeftAdjunction`,
`ProEtale.openImmersionLowerShriekUpperStarAdjunction`, and
`ProEtale.upperStarCompIso`. The projection-formula instance for the open immersion
has no coefficient-ring binder or commutativity hypothesis despite its enclosing
`CondensedRing` namespace. These specialize to arbitrary `MonObj B`.

The statement and hypotheses are matched individually in the second reading below.
The docstring gives all nine proof steps of the node, naming their dependency nodes.
The proof dependencies' statement modules are imported for stage 3; the three
base-change facts already belong to the imported Mathlib morphism-property modules.

## Second reading by Q64

Sources opened: the full node JSON, the blueprint statement and proof at
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/` followed by
`sk-prop-sf-closed-unit/det-sf-open-closed-sequence-ring-sheaf.md` and `.proof.md`;
Stacks `proetale.tex`, especially labels
`lemma-closed-immersion-complement-retrocompact-exact`, `definition-extension-zero`,
`lemma-open-immersion`, and `lemma-ses-associated-to-open`; and `sites-modules.tex`,
labels `lemma-adjoint-push-pull-modules` and `lemma-extension-by-zero-exact`.
The Stacks open-closed sequence assumes a quasi-compact open immersion; its closed
pushforward exactness requires retrocompact complement. Those hypotheses hold here.
The module lifting in Stacks uses an arbitrary sheaf of rings, not just commutative
or constant coefficients. No Noetherian, characteristic or finiteness condition on
coefficients is assumed throughout these sources. The blueprint adds qcqs X and X'.

The following is the object/hypothesis/conclusion list extracted from the node before
matching it with the final Lean. All verdicts below concern the final file.

1. **Base scheme, qcqs.** `X : Scheme.{u}`, `[CompactSpace X]` and
   `[QuasiSeparatedSpace X]` render precisely the base scheme and its two hypotheses.
   Verdict: matches; no separatedness or Noetherian hypothesis.
2. **Closed complement and quasi-compact open.** `i : Z ⟶ X`, `j : U ⟶ X`,
   `[IsClosedImmersion i]`, `[IsOpenImmersion j]`, `[QuasiCompact j]`, and
   `_hU : Set.range j = (Set.range i)ᶜ` render the specified immersions and
   complement relation. There is no extra reducedness condition on Z.
   Verdict: matches.
3. **Coefficient ring and module categories.**
   `B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}` with `[MonObj B]` is an arbitrary
   unital ring sheaf: multiplication is additive in each variable because it is a
   morphism from the tensor product of abelian sheaves. No `[IsCommMonObj B]` occurs.
   `Mod` supplies the existing left-module objects and their linear morphisms.
   `ringSheafInverseImage f B` is `(upperStar Ab f).mapMod B`, with coefficient
   `(upperStar Ab f).obj B`, so both j and i use the actual inverse-image ring.
   Verdict: matches, including nonconstant and noncommutative coefficients.
4. **Clause (1), exact restriction and extension.** The first four conjuncts are
   `PreservesFiniteLimits` and `PreservesFiniteColimits` for restriction and extension
   by zero; in these abelian categories these express exactness. The extension
   helper is `mapModLeft` of the existing abelian extension-by-zero adjunction.
   The construction `ringSheafOpenAdjunction j B` itself supplies j_! adjoint to j^*;
   the next conjunct says its actual unit is invertible at every N.
   Verdict: matches; no arbitrary adjunction or unspecified isomorphism.
5. **Clause (2), closed direct image.** `ringSheafDirectImage i B` is existing
   `lowerStar.mapMod` followed by restriction of scalars through `unitAlgHom B`.
   Its two finite-preservation conjuncts give exactness. The counit of the fixed
   `ringSheafAdjunction i B` is invertible for every G; this is precisely the
   adjunction criterion for full faithfulness. The following `IsZero` conjunct
   renders j^*i_*G = 0 for every G. Verdict: every clause matches.
6. **Clause (3), every M and the actual arrows.** The universal M quantifier ranges
   over all B-module sheaves. `Mono` of the open counit, `Epi` of the closed unit,
   and `ComposableArrows.mk₂ ... .Exact` state exactly the short exact sequence.
   These are the counit/unit components of the constructions above, not freely
   chosen arrows. Verdict: matches, including the zero terms at the ends.
7. **Clause (4), arbitrary base change.** The quantifier is over every
   `X' : Scheme.{u}` with `[CompactSpace X'] [QuasiSeparatedSpace X']` and every
   `g : X' ⟶ X`. There is no flat, etale, proper or quasi-compact hypothesis on g.
   The actual base changes are `pullback g j`, `pullback g i`; j' and i' are
   `pullback.fst`, and g_U and g_Z are `pullback.snd`. Their immersion instances
   come from Mathlib base-change stability. Verdict: matches the objects and order.
8. **Clause (4), coefficient identifications.** `ringSheafSquareComparison` is the
   existing `upperStarCompIso` for `pullback.condition`, not an arbitrary choice.
   `ringSheafSquareCoefficient` explicitly fixes its component at B.
   The existential `hu` and `hz` conclude that these fixed maps respect ring
   multiplication. `ringSheafSquarePullback` then uses exactly those maps in
   `Mod.comap`, identifying g_U^*j^*B with j'^*g^*B, and similarly for Z.
   Verdict: canonical coefficient transport, with no additional hypothesis.
9. **Clause (4), restriction comparisons.** The module natural isomorphisms `delta`
   and `gamma` are normalized by equality of their underlying maps with the fixed
   square comparison at M.X. Since the module forgetful functor is faithful, this
   specifies their maps. Verdict: the inverse-image compositions are the actual
   canonical compositions; module actions have not been forgotten.
10. **Clause (4), open extension base change.** `alpha` has type
    `ringSheafOpenExtension j B ⋙ ringSheafInverseImage g B ≅
    ringSheafSquarePullback g j B ⋙ ringSheafOpenExtension j' (g^*B)`.
    Its inverse component is fixed by the open adjunction's `homEquiv`: its
    transpose is g_U^* of the original unit followed by `delta.inv`.
    Verdict: exactly the canonical open base-change map, not merely existence
    of an unrelated natural isomorphism.
11. **Clause (4), closed direct image base change.** `beta` has the corresponding
    type for `ringSheafDirectImage`. Its forward component is fixed by the closed
    adjunction's inverse `homEquiv`: its transpose is `gamma.hom` followed by
    g_Z^* of the original counit. Verdict: canonical closed base change for
    arbitrary g, without additional geometric hypotheses.
12. **Clause (4), the entire sequence.** The pulled-back M's actual sequence is
    explicitly short exact (`Mono`, `Epi`, `Exact`). The final two equations
    identify g^* of the original open counit with the new open counit through
    `alpha` and `delta`, and g^* of the original closed unit with the new closed
    unit through `beta` and `gamma`. Thus both terms AND arrows are identified.
    Verdict: all of clause (4), including exactness, is in the signature.

Edge cases: X, X', U and Z may be empty. Empty open and empty closed complements are
allowed by the range equality, with no `Nonempty` or nonzero-ring restriction. Every
zero module is included by the universal quantifiers. The zero ring is a monoid
object and is allowed. No coefficient finiteness, nontriviality, field hypothesis or
characteristic restriction was introduced. There is no n or index-set parameter in
this node. The identity base change and all arbitrary g are included. The sites
retain object universe u+1 and morphism universe u, with abelian coefficients and
modules at u+1, as in the published framework; no equality of these site universes
is imposed and u is arbitrary.

Searches actually run during this reading:

- LeanSearch via `msearch.py`: query
  `Open closed localization short exact sequence of modules over an arbitrary
  noncommutative sheaf of rings with base change`. The service returned eight
  module-localization results, no exact match.
- LeanFinder via `msearch.py`: query
  `extension by zero modules sheaf rings open closed base change`. The service
  returned eight unrelated tilde/unit results, no exact match.
- Grep via `msearch.py`: query `openClosed|open_closed|mapModLeft`. It returned
  twenty-one mostly topological open/closed results, no exact match.
- Direct `rg` across Mathlib, the upstream `WeilConjectures` tree and the side
  `lean/Sheaf`/framework trees using `openClosed`, `open_closed`, `extensionByZero`,
  `mapModLeft`, `mapModAdjunction`, `upperStarCompIso`, and the node/helper names.
  The existing `ProEtale.exact_openClosedSequence` has finite constant commutative
  coefficients. `Scheme.proEtale_ringed_open_closed` has commutative ring sheaves,
  a localized-site open category, and no complete module base-change clause.
  Neither is an exact match; the latter remains a proof dependency.
  The module-object transport and adjunction APIs above do exist and are reused.
  No existing declaration has the whole arbitrary-ring statement with clause (4).

Mismatches found and changes made:

- The supplied sandbox lacked the first worker's module and report. The statement
  and its full node binding were supplied rather than treating absence as a
  mathematical obstruction.
- The preliminary commutative-ring draft excluded the node's arbitrary rings.
  Replaced that coefficient restriction by the already published `MonObj`/`Mod`
  encoding, without requiring a commutativity instance.
- A preliminary underlying abelian closed comparison did not give both MODULE
  base-change isomorphisms or compatibility of sequence arrows. Added the actual
  transported coefficient rings, both module comparisons, their adjunction
  characterizations, and both sequence-map equations. Added explicit short
  exactness for the pulled-back M's sequence.
- Made the coefficient comparison's source and target explicit to preserve the
  successive inverse-image ring structures during elaboration. Corrected the
  direction of `homEquiv` in the closed-map characterization.
- The optional finite intrinsic reexport imports encountered an unrelated duplicate
  proof-name collision between the side and upstream constructibility modules.
  Imported the original public arbitrary inverse-image module instead; it is
  precisely the reexported construction required here, with no dependency edit.
- Preserved the natural-language statement and all node fields except `lean`.
  No new definition node or dependency module is needed: every helper specializes
  an existing canonical construction belonging to this item's notion.

All nine declarations have source/blueprint docstrings. There is no proof beyond
one theorem's `sorry`, no hollow data definition, no local notation or private copy.
`autoImplicit` is false. The file has no line longer than 100 characters, and every
universe and variable was checked in the final signature. `lean.statement` is copied
verbatim from that signature and `lean.declarations` lists all nine declarations.

Validation: final `scompile.py Q64 det-sf-open-closed-sequence-ring-sheaf`
compiled the sandbox probe and the delivered module cleanly (5.1 s and 5.6 s),
with no warning. No global build or live-library edit was performed.
