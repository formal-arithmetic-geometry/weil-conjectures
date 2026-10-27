## Worker report

The new module `Sheaf.AlgebraicGeometry.SpacePushoutLiftedAtlas` states
`AlgebraicGeometry.AlgebraicSpace.spacePushout_liftedAtlas`, with its proof wholly
`sorry`. It supplies the scheme representative of the prescribed overlap, its
scheme pushout, and the unique induced map to the given space pushout, and asserts
that this map is representable surjective etale. There are no definitions, additional
postponed lemmas, dependency replacements, or corrections to the mathematical statement.

Source read: `literature/stacks-project/spaces-pushouts.tex`, lines 842–966,
`lemma-pushout-along-thickening-schemes` and `lemma-pushout-along-thickening`
(Tags 07SY and 07VX), and lines 1077–1188,
`lemma-equivalence-categories-spaces-over-pushout` and `equation-cube-over`
(Tags 07W0 and 07W2). The supplied node's eight proof steps are rendered in the
statement docstring, including the composition-domain patching argument that the
Stacks proof omits. In particular the proof starts with the prescribed atlases;
it does not assume that an arbitrary map between two pushouts is etale.

Hypotheses and conclusions, clause by clause:

- The scheme base is `{B : Scheme.{u}}`, and `T T' S P : AlgebraicSpace B` are
  arbitrary spaces over it. The universe `u` is explicit; there are no implicit
  universe equalities beyond the existing algebraic-space interface. Its presheaf
  values are `Type u` on the big site of `Over B`, as in def-trf-algebraic-space.
- The thickening is `i : T ⟶ T'`, with `hi` the existing
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom` and `hiTop`
  the `IsHomeomorph (mapPoint i.hom.hom)` condition. Closed immersions are the
  Mathlib scheme predicate after every scheme base change. The point topology is
  the existing final topology for etale scheme charts, hence the atlas quotient
  topology for algebraic spaces. No nilpotence exponent is chosen.
- The affine arrow is `a : T ⟶ S`; `ha` is
  `IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) a.hom.hom`. This says exactly
  that the arrow is represented by affine scheme morphisms on scheme tests.
- The given pushout `P`, including both structure maps, is bound by `j : S ⟶ P`,
  `b : T' ⟶ P` and `hP : IsPushout a i j b`. This is the universal property against
  every algebraic space over B, not only scheme targets.
- The schemes in the atlases are `V W : Over B`. Their maps are
  `v : schemeSpace V ⟶ S`, `w : schemeSpace W ⟶ T'`. The four binders `hv`,
  `hvSurj`, `hw`, `hwSurj` are precisely the recorded representable scheme-test
  predicates `IsEtale` and `IsSurjective` for these maps. Representability is
  included in each predicate and is not replaced by a point-set condition.
- The specified overlap is `φ : Limits.pullback v.hom a.hom ≅
  Limits.pullback w.hom i.hom`, an isomorphism of actual fppf sheaf products.
  `hφ` says its second projection equals the second projection to T, so it is an
  isomorphism over T, with no required compatibility beyond that in the node.
- `D : Over B` and `e : (schemeSpace D).obj ≅ Limits.pullback v.hom a.hom`
  exhibit the actual overlap as a scheme. There is no extra representability
  hypothesis on the caller. The first equation identifies `dV : D ⟶ V` with the
  first projection via `e`. The next equation identifies `dW : D ⟶ W` with the
  other first projection via `e.hom ≫ φ.hom`. Thus the map to W uses this exact
  specified overlap isomorphism. The second projection of e gives its map to T.
- `IsAffineHom dV.left` expresses the stated affineness of D over V. The fact that
  dW is a thickening follows from its prescribed overlap, rather than being an
  additional assumption. The existential scheme `Q : Over B` with inclusions
  `jV`, `jW` has `IsPushout dV.left dW.left jV.left jW.left` in the category of
  schemes, exactly the scheme pushout named in the node. Representing schemes
  and scheme pushouts are supplied existentially because the node specifies
  them by their universal properties, up to unique compatible isomorphism.
- The extension is `q : schemeSpace Q ⟶ P`. Its two displayed sheaf-map equations
  give exactly the restrictions `V → S → P` and `W → T' → P`. The final universal
  quantifier asserts that every map `q'` with these same two restrictions equals
  q. This gives the full unique-extension clause, not merely some atlas map.
- `IsEtale q.hom.hom ∧ IsSurjective q.hom.hom` is the required representable
  surjective etale conclusion. These are the same predicates used for the two
  input atlases.
- There are no flatness, finite-presentation, separation, quasi-compactness,
  finite-order or nonemptiness hypotheses anywhere in the signature.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`, and `IsAlgebraicSpace`; the
  full signatures and docstrings specify scheme-test properties and the full
  subcategory of fppf sheaves.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` and `etale_fibreProduct_isScheme`; these give
  the sheaf fibre-product and scheme-test interpretation, read with
  `etaleCover_pullback`. The actual overlap in the signature is the sheaf
  category's `Limits.pullback`, as those statements specify.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (class at lines 45–46). Its closed
  embedding with surjective stalk maps is used in `hi`.
- `Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout`:
  `exists_affineThickeningPushout`, `scheme_affineThickeningPushout`, and
  `affineThickeningPushout_recovery`. The first supplies the meaning and
  existence of P; the second upgrades the scheme pushout to space targets.
  The third was read, including its specified-overlap equation; its stronger
  recovery conclusion is not assumed or added to the present statement.
- `Sheaf.AlgebraicGeometry.SchemeAffineThickeningPushout`:
  `AlgebraicGeometry.exists_scheme_affine_thickening_pushout`. Its `IsPushout`
  clause is the scheme universal property for Q; `IsThickening` in that
  theorem imposes no finite nilpotence order.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, the existing
  Yoneda fppf sheaf bundled as an algebraic space, owned by the landed node
  def-trf-scheme-algebraic-space. This node is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  the etale-chart final topology, owned by def-a1-space-point-topology. This
  landed node is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `mapPoint`, the actual quotient
  map on field-valued representatives, owned by def-sfb-proper-curve-moduli.
  This landed node is added to stmt_deps for the existing map only; no curve
  hypotheses or moduli data are used.
- def-weil-size-convention has the recorded metatheoretic convention rather
  than a Lean declaration. Explicit `universe u` and the recorded space/scheme
  interfaces implement it here.

`SpaceAffineThickeningPushout` publicly imports the statement interfaces above;
`SchemeAffineThickeningPushout` is also a direct public import. The stated proof
modules `AlgebraicSpaceRepresentableEtaleSchemeTests`, `EtaleRelationQuotient`,
and `EtaleAtlasPresentation` are plain imports. The proof-only nodes
lem-sfb-space-thickening-base-change, lem-sfb-scheme-infinitesimal-etale-patching,
and lem-sfb-unramified-geometric-equivalence-relation currently have no recorded
Lean declarations; no import is invented for them. Their exact roles are kept
in the eight-step proof docstring. They supply no missing notion required to
form this statement, so no extra dependency modules are needed.

Edge cases checked before writing: when S is empty, T and T' are empty, both
atlases and their pushout are empty, and the empty-to-empty map has the required
scheme-test properties. If T is empty while S is not, T' and W are empty and
Q is V, so the conclusion specializes to the given atlas of S. If i is an
isomorphism, the overlap is W and Q identifies with V; if a is an identity,
D identifies with V and Q with W. None of these cases restricts the supplied
φ beyond being over T. Infinite disjoint unions of charts and non-quasi-compact
atlases remain allowed. A nil ideal without a single global exponent is allowed
by `hi` and `hiTop`, so the node does not become a finite-order thickening
statement. These are semantic checks, not new asserted lemmas.

Searches actually run with the prescribed msearch.py wrapper:

1. LeanFinder: "Compatible scheme atlases of an algebraic space pushout along a
   thickening induce a representable surjective etale map from their scheme
   pushout". Eight hits, including `Scheme.GlueData.ι_jointly_surjective`,
   `Scheme.GlueData.gluedScheme`, `Scheme.Cover.fromGlued`,
   `Scheme.instHasPullbacksEtale`, and scheme Zariski gluing results. None states
   this algebraic-space infinitesimal atlas assertion.
2. Loogle: `"pushout", "Etale"`. Zero hits.
3. Mathlib grep: `pushout.*atlas|atlas.*pushout|thickening.*pushout`, restricted
   to AlgebraicGeometry. Zero hits.
4. LeanSearch: "Compatible etale scheme atlases give a surjective etale atlas
   for the algebraic space pushout along an affine map and a thickening".
   Eight hits: Scheme.Etale, stability of the scheme jointly-surjective precoverage,
   Scheme.smallEtaleTopology, IsEtale, the coproduct cover surjectivity instance,
   Algebra.Etale.formallyEtale, IsEtale.of_comp, and affineness of a scheme
   coproduct descent. None concerns an infinitesimal algebraic-space pushout.
5. Direct `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
   `pushout.*[Aa]tlas|[Aa]tlas.*[Pp]ushout|lem-sfb-space-pushout-lifted-atlas`
   found only two proof-docstring mentions in SpaceAffineThickeningPushout,
   no existing declaration of this statement. A separate exact-id search in
   WeilConjectures returned no hits. The proposed full name
   `spacePushout_liftedAtlas` has no existing source declaration, also checked
   across Mathlib's AlgebraicGeometry directory and both project roots.

Compilation: the prescribed scompile.py command compiled the module separately
in sandbox and library mode against the server's live published build; both
completed with exit 0 and no warnings (20.1 s and 29.5 s respectively).

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
