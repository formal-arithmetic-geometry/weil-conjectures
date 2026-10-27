## Worker report

Module: `Sheaf.AlgebraicGeometry.CurveDescentIsomSpaces`.
Main declaration: `AlgebraicGeometry.ProperCurveModuli.fppf_stack_and_isom_spaces`.
The only postponed theorem is this declaration; its proof is `sorry`, with all six
DAG proof steps explained in the docstring. Two concrete helpers express isomorphisms
on slice sites and their restriction under base change. Their data contain no sorry.

Read the complete item statement, proof, statement dependencies and their records;
read the recorded signatures and documentation in the source modules. Also read
Stacks `quot.tex`, situation-curves and lemmas-curves-fibred-in-groupoids,
-curves-stack and -curves-diagonal (0D4Z, 0D51, 0D52, 0D53).

Clause-by-clause rendering:

- Schemes over Spec Z: the first three conjuncts use `ProperCurveModuli` with
  `S = Spec (.of (ULift.{u} ℤ))`, projected by `ProperCurveModuli.forget` to
  `Over S`. The integer-ring lift puts the same initial ring in the site's universe.
  The last conjunct quantifies over every `T : Scheme.{u}`; the unique map to Spec Z
  is unnecessary data for the relative Isom functor.
- A family has an algebraic-space source, not necessarily a scheme:
  `ProperCurveFamily` has `space : AlgebraicSpace S` and a projection to `yoneda.obj T`.
  The total category is the published `ProperCurveModuli`; no second definition.
- Flatness is the first conjunct of `AlgebraicSpace.IsProperCurveFamily`, using
  `MapToSchemeIsLocally (@Flat)` on every representable etale scheme chart.
- Properness is its separatedness, quasi-compactness, chartwise local finite type,
  and universal-closedness conjuncts. Separatedness is a closed-immersion relative
  diagonal; quasi-compactness tests affine scheme base changes on point spaces.
  Universal closedness tests scheme base changes, equivalently arbitrary
  algebraic-space base changes by the etale-local scheme-chart criterion for
  closed subsets. This is the recorded proper-curve definition, unchanged.
- Finite presentation is local finite presentation on etale charts together with
  quasi-compactness and quasi-compact diagonal, the latter being quasi-separatedness.
- Every geometric fibre has dimension at most one: the final conjunct of that same
  predicate quantifies over every algebraically closed field in universe u and
  every geometric point, and applies `topologicalKrullDim` to the `Point` space of
  the actual presheaf fibre product. Properness ensures quasi-separatedness, so this
  topological dimension agrees with relative dimension computed on etale charts.
- Arrows are base arrows and cartesian squares, in `ProperCurveModuli.Hom`.
  Over an identity these are exactly isomorphisms; over `T' → T` they identify the
  source with the actual sheaf fibre product. Composition pastes these squares.
- Cartesian pullbacks and fibres in groupoids: the first conjunct is
  `(forget S).IsFibered`; the second says every arrow is strongly cartesian over
  its actual `a.base`. This is the usual total-category formulation, including
  cartesian lifting and the uniqueness clause, not merely existence of pullbacks.
- Fppf topology: the third conjunct uses `Scheme.fppfTopology.over S` exactly.
  No etale-only descent assertion is substituted for fppf descent.
- All compatible descent data are effective: `D` is a diagram on all arrows of a
  covering sieve with `hD` its specified base diagram. In a category in which every
  arrow is cartesian this is precisely a cartesian descent section. The cocone `c`
  has its vertex over `T` by `hc`; the displayed equation fixes each leg over the
  canonical map of the covering sieve. `Nonempty (IsColimit c)` says that gluing
  gives all and uniquely the compatible arrows out of the datum, so this includes
  descent of isomorphisms as well as effective descent of families. Passing between
  covering families with cocycles and cartesian sections on covering sieves is the
  standard total-category stack criterion; there is no index countability bound.
- For any scheme T and two objects X,Y of its curve fibre, the last conjunct uses
  `ProperCurveFamily (Over.mk (𝟙 T))`. Representable terminal presheaves have unique
  structure maps, so these are exactly algebraic-space families over T.
- Isom over each U → T: `ProperCurveFamily.isomorphisms X Y U` is the type of natural
  isomorphisms of the two presheaves restricted along `Over.forget U`. A scheme
  over U has the prescribed composite map to T, so this restriction is exactly
  the functor of points of X ×_T U, respectively Y ×_T U, on schemes over U.
  Natural isomorphisms on this slice are exactly U-isomorphisms of these products.
  In particular it imposes preservation of the projection to U.
- Algebraic-space representation and the sheaf assertion: `I : AlgebraicSpace T`
  gives the representing fppf sheaf with representable diagonal and etale atlas.
  `θ U` identifies every section of I with precisely these isomorphisms. The last
  equation is naturality for EVERY map `a : U ⟶ V`, with restriction defined by
  `Functor.isoWhiskerLeft (Over.map a).op`. Hence the represented functor is a
  sheaf, not just objectwise equinumerous with one.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `ProperCurveFamily`,
  `ProperCurveModuli`, `ProperCurveModuli.Hom`, `ProperCurveModuli.forget`,
  `AlgebraicSpace.IsProperCurveFamily`, `MapToSchemeIsLocally`,
  `MapToSchemeIsSeparated`, `MapIsQuasiCompact`, `MapToSchemeIsUniversallyClosed`.
  Added its already landed node `def-sfb-proper-curve-moduli` to stmt_deps under
  the permission to cite existing landed definitions. Its full statement and
  module were read; no dependency node is changed.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `AlgebraicSpace.IsRepresentableWith`,
  `AlgebraicSpace.IsEtale`, used through the imported curve definition.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Spec`, `Spec.map`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`,
  with its projections and cartesian universal property in the family interface.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, in the family predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, `IsSeparated`,
  `UniversallyClosed`, giving the scheme chart conventions used by the family predicate.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over`: topology `.over`.
- `Mathlib.CategoryTheory.FiberedCategory.Fibered`: `Functor.IsFibered`;
  its Cartesian dependency gives `Functor.IsStronglyCartesian`.
- `Mathlib.CategoryTheory.Whiskering`: `Functor.isoWhiskerLeft`;
  `Over.map`, `Over.forget` express restriction.
- Proof-only import: `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`. The other four proof-input nodes
  (locality, relative dimension, Hom representability and finite-type effectivity)
  have no Lean record or Mathlib match yet, so there is no module to import.
  They are proof dependencies only; their notions are not prerequisites to writing
  this statement and they remain named explicitly in its natural-language proof.
- The size-convention node is metatheoretic; `universe u` is explicit throughout.

Searches performed:

1. `msearch.py leanfinder`: "Proper flat finitely presented algebraic space curve
   families form an fppf stack with algebraic space Isom sheaves". Eight results,
   all scheme morphism properties (flat base change, scheme isomorphism descent,
   universally open); no matching curve-stack or Isom-space statement.
2. `msearch.py loogle`: `"IsStack", "IsRepresentable"`. Zero results.
3. `msearch.py grep`: `CurveModuli|CurveFamily|IsModuliStack|HasRepresentableModuliDiagonal`
   in Mathlib/AlgebraicGeometry. Zero results.
4. `msearch.py leansearch`: "Isomorphism functor of two objects over a base represented
   by algebraic space". Eight generic Yoneda/Over/Grothendieck results; no match.
5. `rg` in WeilConjectures and Sheaf found `ProperCurveModuli` (reused), generic
   `IsModuliStack` (etale topology, not used for this fppf statement), and the existing
   proper-curve automorphism functor, whose slice-restriction convention is followed.
   Searching the item id in upstream Lean found no declaration. Searching all three
   source trees and `dag/lean_names_upstream.json` for the proposed declaration names
   found no duplicate. Mathlib `presheafHom` supplies Hom restrictions, but does not
   state the Isom representation assertion. No private copy of that Hom functor is made.
6. `blueprint_refs.py search 'families of curves'`: zero blueprint-node matches;
   DAG search for `ProperCurveModuli` found the existing definition node cited above.

Edge cases checked before writing: empty base and empty curve (dimension minus infinity),
zero-dimensional fibres, disconnected or nonreduced curves, arbitrary characteristic,
nonreduced test schemes, arbitrary geometric field extensions in the big site's size,
empty covering sieve on the empty base, and covers with arbitrary index set. No genus,
connectedness, reducedness, nonemptiness, nodality, or stability hypothesis is added.
The actual integer ring is lifted only in universe, not replaced by a coefficient ring.
All variables and universes are explicit; there are no file-local instances or notation.

Validation: scompile.py compiled the file in sandbox and actual module modes, both
clean (3.6 s and 2.1 s). No statement correction or disputed statement was needed.

## Second reading by Q127

Reopened the item and the complete file after the successful compile. This is a
worker self-check; the dispatched workflow supplies the independent maintainer review.
Checked the flat/proper/fp clauses against the imported definition, the geometric fibre
formula and point topology, the category's actual cartesian arrows, the fppf (rather
than etale) topology, effectiveness plus arrow descent, the quantified arbitrary base
scheme in the Isom clause, and the naturality equation with its direction U → V.
The generic existing IsModuliStack definition was deliberately not used because its
topology is etale; the exact fppf total-category criterion is written out instead.
No mismatch, extra hypothesis, weakened conclusion, or node correction was found.
