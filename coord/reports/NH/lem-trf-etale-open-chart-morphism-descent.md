## Worker report

The module Sheaf.AlgebraicGeometry.EtaleOpenChartMorphismDescent states
AlgebraicGeometry.AlgebraicSpace.etale_open_chart_morphism_descent, with sorry as its
only theorem proof. Two real helper constructions belonging to this node are
openChartObject V O = Over.mk (O.ι ≫ V.hom), and openChartInclusion V O =
Over.homMk O.ι. They give the actual open scheme with its inherited base map and
inclusion. They introduce no independent mathematical notion and choose no data
from an existence assertion. Both are listed in lean.declarations.

Hypothesis and clause correspondence:

- The base scheme is S : Scheme.{u}; X and Z are AlgebraicSpace S. All scheme tests,
  atlas schemes and representing schemes are Over S in the same universe u. This is
  the recorded algebraic-space framework, with values in Type u.
- V : Over S and p : yoneda.obj V ⟶ X.obj.obj are the atlas and its natural map.
  hp : IsEtale p and hsur : IsSurjective p are precisely representable etaleness and
  representable surjectivity on all scheme tests, using the recorded definitions.
- R : Over S, s t : R ⟶ V and hR : IsPullback (yoneda.map s) (yoneda.map t) p p
  specify the scheme representing V times_X V with its actual projections.
- O : V.left.Opens is the open subscheme. hinv equates s.left ⁻¹ᵁ O and
  t.left ⁻¹ᵁ O, so either is R_O. q has domain the Yoneda functor of the actual O.
- hq is the equality of q after the two restrictions to R_O, expressed without casts:
  for every test B and a,b : B → O and c : B → R whose projections are the inclusions
  of a and b, yoneda.map a ≫ q = yoneda.map b ≫ q. Maps with this data are exactly
  maps B → R_O, since the two inverse-image opens agree. Thus no compatibility
  assumption beyond the node is introduced. Yoneda or evaluation at identity makes
  equality of these composites equivalent to equality on their sections.
- U : OpenSubspace X uses the recorded subfunctor definition. U.val.preimage p =
  Subfunctor.range (yoneda.map (openChartInclusion V O)) means h_V times_X U=h_O
  as subfunctors of h_V. Open inclusions are mono, so their Yoneda range is precisely
  their represented open subfunctor. The next universal clause proves uniqueness
  among all open subspaces with this pullback, independently of q.
- pO factors the actual atlas map on O through U: pO ≫ U.val.ι equals the original
  map to X. The existential r is a natural transformation U → Z; pO ≫ r=q is the
  required descent equality. Every other r' satisfying it equals r.
- For every B,a and every representing pullback E,e,v, the square IsPullback
  (yoneda.map v) (yoneda.map e) p a is the actual scheme test E=B times_X V.
  It is a surjective etale cover by hp and hsur. The theorem supplies W : B.left.Opens
  with e.left ⁻¹ᵁ W=v.left ⁻¹ᵁ O; every other open with this equation equals W.
  U.val.preimage a equals the Yoneda range of W's inclusion, giving the required
  scheme representation of h_B times_X U. There is no choice of a particular
  representative E, and the formula holds for all of them.
- For every f:C → B, the next clause identifies the representing open on C with
  f.left ⁻¹ᵁ W. This is compatibility of these descriptions with maps of tests.
- For b:h_B → U and every representing atlas pullback, the next clause gives
  w:E → O lifting v and equates yoneda.map e ≫ b ≫ r with yoneda.map w ≫ q.
  This is exactly the asserted coverwise description of r on a factored test.
  Since r itself is a natural transformation, these descriptions are natural;
  uniqueness of r says they characterize that natural transformation.
- For every algebraic space Z', equality of r₁,r₂:U → Z' is detected after pO.
  This includes the requested target Z and permits the representable target h_T.
- For every scheme T over S and x:X → h_T,z:Z → h_T, the equality expressing
  that q is over T implies r ≫ z=U.val.ι ≫ x, so r is over T.
- There is no hypothesis of quasi-compactness, separatedness, affineness, nonemptiness,
  or existence of extra lifts. The supplied relation and scheme squares encode their
  representing properties, rather than replacing them by arbitrary unrelated maps.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom,
  including the locally affine locally ringed space structure and category.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace and
  AlgebraicSpace.IsRepresentableWith, IsRepresentable, IsEtale, IsSurjective.
  These quantify over actual scheme-valued cartesian squares over S.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace: AlgebraicSpace.OpenSubspace,
  a subfunctor with inclusion representable by open immersions.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: Limits.pullback,
  pullback.fst and pullback.snd; their cartesian-square formulation is IsPullback
  from the algebraic-space dependency. Mathlib.AlgebraicGeometry.Pullbacks supplies
  the scheme pullback infrastructure. No duplicate fibre-product construction.
- Mathlib's Scheme.Opens, Opens.ι, Over.mk, Over.homMk, yoneda, Subfunctor.preimage
  and Subfunctor.range implement the actual open scheme and its subfunctor pullback.

Public imports expose statement dependencies, including Scheme and AlgebraicSpace
through OpenSubspace. Plain proof imports include EnlargedEtaleRingedSite for the
recorded schemeSpace construction (def-trf-scheme-algebraic-space), and
SiteCoveringAxioms for def-weil-pbc-sites-and-cohomology. Fpqc, Etale and OpenImmersion
are already exposed transitively by the statement imports. The proof dependency
lem-trf-fppf-local-open-subfunctor-descent has no recorded Lean declaration locally,
so it has no module to import; this does not obstruct the statement. Its exact role
is retained in the theorem's eight-step proof docstring.

Edge cases checked before writing: O empty descends to the empty open; O=V gives X
and ordinary morphism descent; an identity atlas gives restriction to O; an empty
atlas forces X empty by surjectivity. Z empty imposes exactly the existence of q,
which forces O empty. The relative clause allows any T and identity structure maps.
R may be nonaffine, nonseparated and non-quasi-compact. W uniqueness is explicitly
among all opens satisfying the inverse-image equation, not only among those already
supplied with a representation. Universes are explicitly bound and autoImplicit=false.

Searches made (the raw wrapper results are retained in searches.jsonl):

- msearch.py leanfinder: "An invariant open subscheme of an etale atlas of an
  algebraic space and a compatible morphism descend uniquely to an open subspace
  and a morphism". Eight hits: Scheme.Etale, Scheme.GlueData.f_open,
  LocallyRingedSpace.GlueData.f_open, Scheme.Etale.forget, Scheme.instCategoryEtale,
  IsOpenImmersion.lift_uniq, IsEtale, LocallyRingedSpace.IsOpenImmersion.lift_uniq.
  None states algebraic-space open-and-morphism descent.
- msearch.py loogle: "AlgebraicSpace, OpenSubspace". Zero hits; Loogle does not know
  the project's AlgebraicSpace identifier.
- msearch.py grep: "OpenSubspace|invariant.*open|open.*descent", AlgebraicGeometry.
  Three Mathlib hits: Morphisms.FlatDescent for fpqc descent of universally open
  maps and open immersions, and Morphisms.FlatMono. All concern schemes, not this
  algebraic-space theorem.
- rg in lean/WeilConjectures and lean/Sheaf for invariant opens and etale open
  morphism descent found AlgebraicSpaceEtaleOpenImage, EtaleRelationFindingOpens,
  EtaleAtlasPresentation and scheme effective-descent modules. Open images and
  quotient-open representability omit the compatible morphism, scheme-test formula,
  detection and relative clauses, so none is an exact existing declaration.
- Exact item-id and proposed-name searches in those two source trees found no
  existing declaration of this node.

Sources opened: literature/stacks-project/spaces.tex at lemma-finding-opens (02WU),
spaces-properties.tex at lemma-open-subspaces (03BZ), and spaces-divisors.tex at
lemma-invertible-map-into-relative-proj (0D2Z). The live node's eight-step proof has
been included as a full natural-language proof in the theorem docstring.

No statement correction, new node, dependency interface repair or disputed statement.
The previous worker's stage-1 live-wins refusal is inapplicable to a stage-2 statement
on the already split node; the node has no lean record and no released repair note.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
