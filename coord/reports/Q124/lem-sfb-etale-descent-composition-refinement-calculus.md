## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.etale_descent_composition_refinement_calculus`
in `Sheaf.AlgebraicGeometry.EtaleDescentCompositionRefinement`, with its whole proof `sorry`.
Its new prerequisite `Sheaf.AlgebraicGeometry.FpEtaleSpaceDescent` contains real definitions
of the finite-presentation fibre category and its descent interface. No statement correction
or dependency-record repair is needed. There are no postponed theorems in that definition
module and no data chosen from an unproved existence assertion.

Clause-by-clause correspondence:

- Schemes and the size convention: explicit `universe u`, `S : Scheme.{u}`, and `Over S`.
  The ambient `S` just puts all spaces in the one existing category `AlgebraicSpace S`.
  An object over the representable space of `T → S` is exactly an algebraic space over T:
  its sheaf on Sch/S sends U to pairs of a map U→T and a section over that map. Conversely,
  its fibre over each U→T is the relative sheaf on Sch/T. These inverse constructions
  preserve natural transformations, atlas tests, and fibre products. Thus no object is
  required to be a scheme and no morphism over T is excluded. Taking the ambient S=T
  includes every configuration of the original statement. S itself need not be
  quasi-separated, an extra freedom of presentation which adds no hypothesis.
- Every scheme base is quasi-separated: the explicit `QuasiSeparatedSpace X.left`,
  `Y.left`, `T.left`, `V.left`, and `P.left` hypotheses. In the definitions of universal
  descent, the test V and its cartesian pullback P are also quasi-separated. For the
  quasi-separated source and target in the theorem every such fibre product is
  quasi-separated, so these tests omit no allowed base change.
- Objects and arrows of F(T): `FpEtaleSpace T` is the full subcategory of
  `Over (schemeSpace T)`. Its four conditions are `IsChartwiseEtale A.hom`,
  `MapIsLocallyOfFinitePresentation A.hom`,
  `IsQuasiCompactPresheafMap A.hom.hom.hom`, and the same quasi-compactness predicate
  on `pullback.diagonal A.hom.hom.hom`. These render respectively chartwise étaleness,
  local finite presentation on scheme charts, quasi-compactness on affine scheme
  tests, and quasi-compact relative diagonal. A full subcategory retains all maps
  over T; it does not require maps to be representable or separated.
- Desc_F(q): `FpEtaleDescentData q` has an object in F(X) and the existing
  `Over.DescentDatum (descentSchemeMap q) obj.obj`. Its `transport_homMk_comp`,
  `transport_self`, and `transport_transport` fields give naturality, the diagonal
  identity, and the triple cocycle. Reversing the two base points gives the inverse
  transport. Evaluating on the universal pair of projections recovers the ordinary
  isomorphism between the two sheaf pullbacks. Conversely, pulling that isomorphism
  back to any test object gives this transport. The Hom structure and its Category
  instance retain exactly the compatible arrows, including noninvertible ones.
  Tests by algebraic spaces here are equivalent to tests by their scheme atlases:
  equality of sheaf maps can be checked after the surjective étale atlas. This does
  not strengthen the descent condition.
- Canonical full faithfulness: `FpEtaleDescendsMorphisms q` is its Hom equalizer
  description. For A,B over T, its `IsPullback p r A.obj.hom (descentSchemeMap q)`
  specifies P=A×_T X. Giving a map P→B over T is equivalent, by the pullback
  universal property, to giving P→B×_T X over X. The displayed invariance under
  all s,t with s≫p=t≫p is precisely compatibility of that map with the two canonical
  descent data, because P×_A P=A×_T(X×_T X). `∃! f : A.obj ⟶ B.obj` is thus
  bijectivity on the canonical functor's Hom sets, including uniqueness. This is
  an equalizer encoding of full faithfulness, not an assumed arbitrary functor.
- Universal descent: `IsUniversalFpEtaleDescent q` applies this condition to every
  cartesian scheme square after every quasi-separated V→T. All representatives of
  the pullback are allowed; they are uniquely isomorphic and the condition is
  invariant under that isomorphism. The maps in the interface are constrained by
  actual cartesian universal properties, not unconstrained comparison arrows.
- Universal effective descent: `IsUniversalEffectiveFpEtaleDescent q` is universal
  descent together with `∀ D, Nonempty D.Realization` after each such base change.
  Full faithfulness plus these specified realizations is exactly equivalence of
  the canonical comparison; the `Nonempty` here existentially asserts the full
  realization data and never chooses a canonical object from a bare existence proof.
- Realizations and comparisons: `D.Realization` contains the descended F(T) object,
  the map from D's object to it, an `IsPullback` square, and its transport invariance.
  The universal property gives the actual isomorphism with the sheaf fibre product;
  invariance states that it identifies the original datum with the canonical datum.
  Thus the conclusion retains a compatible realization, not just an isomorphism
  class or a nonempty underlying space.
- (i): the first implication in the first conjunct takes universal effectiveness
  of a and b and concludes it for `a ≫ b`.
- (ii): the second implication takes only universal effectiveness of `a ≫ b` and
  concludes it for b. It imposes no descent or surjectivity assumption on a.
- (iii): the second main conjunct takes universal descent of q and universal
  effective descent of g. `square : IsPullback h r q g` specifies P=X×_T V.
  D is the original q-datum; E is the datum after that base change.
  `FpEtaleDatumPullback square D E` contains a map of the objects whose square over
  h is cartesian, with an explicit transport compatibility equation. Such a pair
  (E,map) is precisely a representative of the canonical pullback datum, uniquely
  determined up to compatible isomorphism. The two equality witnesses e,e' in that
  equation concern the same pair of points; e' exists from e and the base square,
  and proof irrelevance removes dependence on which proof is used. The hypothesis
  `Nonempty E.Realization` and conclusion `Nonempty D.Realization` give the required
  local-to-global effectivity, with actual compatible comparison maps in both.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsAlgebraicSpace`,
  `IsEtale`, representable fppf-sheaf model and full-subcategory morphisms.
- `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`:
  `AlgebraicSpace.chartwise_etale_permanence`; it publicly exposes the existing
  `IsChartwiseEtale` and `schemeSpace` from `EnlargedEtaleRingedSite`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocally`, `MapIsLocallyOfFinitePresentation` (existing chart test).
- `Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests`:
  `quasiCompact_iff_quasiCompact_scheme_tests`, `quasiCompact_presheafMap_baseChange`;
  this exposes the affine-atlas predicate `IsQuasiCompactPresheafMap` from
  `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`. Cartesian squares in the full subcategory specify
  these sheaf fibre products since their closure and universal property hold there.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`:
  generic `CategoryTheory.Over.DescentDatum`, its four structure fields, and the
  compatible-pullback-square characterization in `DescentDatum.IsEffective`.
  The latter is read for comparison; our realization retains the required F(T)
  membership and the square as data, so it does not weaken to arbitrary spaces.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `QuasiSeparated`, `quasiSeparated_iff_quasiSeparatedSpace`, and the qcqs
  permanence instances used by the proof plan.
- The metatheoretic size-convention node has no module or declaration, as recorded.

The theorem imports the stated proof prerequisites (étale scheme morphisms,
quasi-separated/locally-finitely-presented scheme permanence, space quasi-compactness,
chartwise permanence and sheaf pullbacks). The proof prerequisite
`lem-sfb-descent-data-refinement-hom` has no recorded Lean module yet, so there is
no proof-only import to add for it. It is referenced in the proof docstring for
stage 3. No import cycle is introduced. No dependency module is copied privately.

Edge cases checked before writing: identity q, identity g, empty schemes and empty
spaces, non-separated finitely presented étale spaces, arbitrary non-surjective a
in (ii), and non-quasi-compact base schemes. No nonempty, separatedness, flatness,
surjectivity, or quasi-compactness hypothesis is silently imposed on the base maps.
The full fibre category is never replaced by finite étale schemes. In the identity
case Hom descent is the ordinary Hom bijection and cartesian realizations recover
all data. In the empty case the same universal properties apply without a point
choice. Local finite presentation includes the zero-generator/relation cases.

Searches: `msearch.py` LeanFinder query “Universal effective descent for finitely
presented etale algebraic spaces is closed under composition and refinement and
effectivity is local on the base” returned scheme étale composition and ring/scheme
property descent, not this statement. Loogle `"DescentDatum", "IsEffective"` returned
zero hits. LeanSearch “finitely presented etale algebraic spaces category universal
effective descent cartesian realizations” and LeanFinder “category of finitely
presented etale algebraic spaces with transport descent data and compatible cartesian
realization” returned ring étaleness, Scheme.Etale, and scheme-site definitions,
not the fibre category of algebraic spaces. Mathlib grep for
`UniversalEffectiveDescent|universalEffectiveDescent|IsEffectiveDescent|DescentDatum`
and `FpEtaleSpace|UniversalEffective.*Descent|DescendsMorphisms` in CategoryTheory
returned no matches. The wrapper's exact query/result records are retained in the
new node's mathlib_searches. Direct rg searches of lean/WeilConjectures and lean/Sheaf
found the generic upstream Over.DescentDatum, which is reused, and the scheme-only
DescentDataCategory, whose type cannot carry non-schematic algebraic spaces. The
item-id search in WeilConjectures returned no declaration. DAG searches found
related theorem nodes, not a definition of this specialized interface.
`tools/blueprint_refs.py search 'etale descent'` returned two unrelated blueprint
statements; `ancestor` returns null for this inherited item. No exact existing
statement was found.

Source checked online: https://davidrydh.se/papers/submersion20100305.pdf, printed
pp.17--19, Notation (5.1), Remark (5.2), (5.5), Propositions (5.6)--(5.7). The latter
state composition, refinement and the precise local-effectivity implication. The
paper's quasi-separated convention is retained by finite presentation and by the
explicit scheme hypotheses. No mathematical dispute found.

Validation: both delivered files compile separately via scompile.py against the
live published server library in dependency order; no errors or unexpected warnings.

## New nodes

`def-sfb-fp-etale-space-descent` gives the finite-presentation étale fibre category,
its transport data category and cartesian realization/pullback interface, plus the
Hom-equalizer definitions of universal descent and universal effective descent.
Its source is Rydh (5.1)--(5.5), pp.17--19. The searches above and the exact records
in mathlib_searches distinguish it from the existing scheme-only category and from
the generic transport notion, which is imported directly. It adds no arbitrary
pullback choices, axioms, proof obligations or duplicate local-finite-presentation,
chartwise-étale, or quasi-compactness predicates. The item gains this new definition
node in stmt_deps; otherwise only its lean record changes.

## Second reading by Q124

I reopened the original node, the new node, and both complete Lean files for a
separate clause-by-clause pass. The four fibre conditions match the original finite
presentation convention, and the full-subcategory arrows include every map. The
upstream transport includes both identity and cocycle, and the compatible Hom
structure has exactly the stated arrow equation. The Hom equalizer includes unique
lifting, so the effectiveness predicate also includes full faithfulness, as required
by “equivalence”. I checked that cartesian squares specify the canonical pullbacks
up to unique compatible isomorphism, and that the local pulled datum condition
retains this comparison rather than taking an arbitrary object or map. Both (i)
and (ii) appear in the first conjunct with their distinct hypotheses; the second
conjunct includes both universal hypotheses of (iii) and realizes the original datum.
The explicit quasi-separated assumptions and universe parameters match the allowed
bases, and identity/empty cases are included. No mismatch or statement correction
was found. This is a second pass by the assigned worker; the maintainer's independent
review remains the external second reader, as specified by the dispatch brief.
