## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceFpModuleHomColimit` states
`AlgebraicGeometry.AlgebraicSpace.finitePresentation_hom_directed_colimit`, with
one `sorry` and no new definitions. The source is Stacks, Cohomology of Spaces,
Tag 07U7, whose statement and proof were read in spaces-cohomology.tex lines
518ff, together with the recorded stage-1 proof. No statement correction or
dispute is needed. The node changes only in lean and the addition of the landed
definition owner `def-sfb-space-absolute-quasi-separated` to stmt_deps.

Hypotheses, objects and clauses:

- `{S : Scheme.{u}}` and `(X : AlgebraicSpace S)` give the scheme base and the
  specified algebraic space. This is the dependency's actual fppf-sheaf model,
  not a scheme substituted for the space.
- The explicit universe `u` is the small scheme/coefficient universe; the small
  étale site has objects in `u+1` and morphisms in `u`. The index preorder
  `I : Type (u+1)` and Hom-set colimit are in the larger universe of the size
  convention. There are no auto-bound universes or variables.
- `[CompactSpace (Point X.obj.obj)]` is quasi-compactness of the existing point
  topology: open covers have finite subcovers; Hausdorffness is not required.
- `hqs : IsAbsolutelyQuasiSeparated X` uses the landed definition for
  quasi-compactness of the absolute diagonal, equivalently quasi-compactness of
  the fibre products of two affine S-scheme tests. This is Stacks 0AHR(3), not
  relative quasi-separatedness of X over a possibly non-quasi-separated S.
- `[Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]` is precisely a nonempty
  directed preorder, without antisymmetry. Mathlib supplies its thin category.
- `D : I ⥤ X.Modules` is the given diagram in ALL structure-module sheaves on
  the small étale site. Neither the terms nor the apex carry a quasi-coherence
  assumption.
- `c : Cocone D` specifies the module M as `c.pt` and coprojections as
  `c.ι.app i`, including transition compatibility. `hc : IsColimit c` supplies
  exactly the module-sheaf colimit universal property, with no chosen-colimit
  restriction on M.
- `G : X.Modules` with `[G.IsFinitePresentation]` is Mathlib's local finite
  cokernel-presentation predicate, read in Quasicoherent.lean:202-284. The
  landed quasi-coherent-module module supplies its slice sheafification
  instances. It means étale locally O^m -> O^n -> G -> 0, with finite m,n.
- `D ⋙ coyoneda.obj (op G)` is the diagram of Hom sets with postcomposition
  transitions. `(coyoneda.obj (op G)).mapCocone c` has apex Hom(G,M) and legs
  g |-> g ≫ c.ι.app i. Its `colimit.desc` is therefore the exact canonical map
  specified in the node. `Function.Bijective` is its stated bijectivity.
- The second conjunct says every `f : G ⟶ c.pt` is `g ≫ c.ι.app i` for an
  actual stage i and actual module morphism g.
- The third conjunct quantifies over arbitrary i,j,g,h with equal composites
  into M, and produces k together with hik : i ≤ k and hjk : j ≤ k and equality
  `g ≫ D.map (homOfLE hik) = h ≫ D.map (homOfLE hjk)`. Thus both original
  stages are bounded, and the equality is at a common later stage.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`, actual locally ringed spaces locally affine.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleTopology`, `structureSheaf` and `Modules`; in particular Modules is
  `ringedSiteModules.{u} X.structureSheaf`, the existing SheafOfModules category.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace`, the supremum of the
  coinduced topologies of étale scheme-source tests on the existing Point type.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and
  `etaleModuleOverHasWeakSheafify`, `etaleModuleOverWEqualsLocallyBijective`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsFinitePresentation` (the actual predicate used), with
  `QuasicoherentData.IsFinitePresentation` and finite local presentations.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`, owned by the added landed definition dependency.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`,
  `colimit.desc`, with Types.Colimits providing colimits of Hom-set diagrams.
- `def-weil-size-convention` is a metatheoretic convention, with no declaration;
  implemented by the explicit universe choices described above.

Available proof-dependency modules are imported privately: InternalHom
(`SheafOfModules.homObj`), Presheaf.Sheafification (the sieve-module
sheafificationAdjunction), Sites.LocallyBijective (W_iff_isLocallyBijective),
SiteFinitePresentationInternalHomColimit
(`internalHom_preserves_filteredColimit_of_isFinitePresentation`),
ModuleSheavesColimitsForgetful (`moduleSheaves_colimits_forgetful`),
Abelian.RightDerived (the degree-zero comparison instance), Grp.FilteredColimits
(the AddCommGrpCat forgetful preservation instance), and Types.Filtered
(`isColimit_eq_iff`, `isColimit_eq_iff'`). The existing DAG node
`lem-sfb-space-cohomology-filtered-colimit` has no Lean record or Mathlib match
in the read repository, so it is named in the proof docstring but has no module
import. It supplies no object needed to state this item.

Edge cases checked before writing: X empty; G zero; finite-free G including
rank zero; singleton I; non-antisymmetric directed preorders; zero diagrams;
arbitrary non-quasi-coherent diagram terms; arbitrary specified colimit apex;
base S not quasi-separated. The conclusion specializes correctly in every
case. Empty I is explicitly excluded by the node. The comparison's legs are
postcomposition with the given c, not an arbitrarily selected bijection.

Searches performed with msearch.py (group Q36 and this item):

- leanfinder: "Hom from a finitely presented module sheaf on a quasi compact
  quasi separated algebraic space commutes with directed colimits" returned
  eight local-presentation declarations, including
  QuasicoherentData.IsFinitePresentation.isFinite_presentation,
  quasicoherentDataOfIsFinitePresentation, and Presentation.isColimit. None is
  the global Hom-continuity theorem on an algebraic space.
- loogle: "SheafOfModules.IsFinitePresentation, PreservesFilteredColimits"
  returned zero hits and reports PreservesFilteredColimits unknown in that
  service's namespace. No existing theorem can be inferred from that query.
- grep: "finitePresentation.*[Cc]olimit|[Cc]olimit.*finitePresentation|IsFinitePresentation"
  in Algebra/Category/ModuleCat/Sheaf returned five finite-presentation
  definition/instance occurrences in Quasicoherent.lean, no continuity theorem.
- leansearch: "Hom from a finitely presented sheaf of modules on a qcqs
  algebraic space commutes with filtered colimits" returned general
  categorical presentability, finite-presentation results for rings,
  SheafOfModules.Hom and module-colimit existence. No exact match: local finite
  presentation must first imply the categorical continuity at issue here.
- rg searches in lean/WeilConjectures and lean/Sheaf for Hom/colimit and local
  finite-presentation patterns found no exact algebraic-space theorem; the
  precise node id has no upstream source hit. The new declaration name was
  searched in both trees and dag/lean_names_upstream.json with no match.
  Searches for quasi-compactness/diagonal conventions found the landed absolute
  quasi-separatedness definition, which is reused and cited, not copied.

Validation: prescribed scompile.py compiled the file in sandbox mode and its
library module mode, both clean (1.6 seconds each). No theorem was proved.

## Second reading by Q36

I reread the node, Stacks 07U7 and the complete module after compilation. This
is a worker self-check; no other agent was started, as the dispatcher brief
forbids delegation. The maintainer's independent delivery review remains the
independent reading. The clause correspondence is listed explicitly above.
In particular I checked that the target modules are unconstrained, the
quasi-separatedness is absolute, arbitrary colimit cocones are allowed,
non-antisymmetric preorders are allowed, and both order bounds occur in the
last clause. The desc map's cocone is coyoneda applied to the supplied c,
which fixes its canonical normalization. No semantic mismatch was found and
no statement was corrected. No new nodes or dependency modules were needed;
the existing absolute-quasi-separatedness owner was added to stmt_deps.
