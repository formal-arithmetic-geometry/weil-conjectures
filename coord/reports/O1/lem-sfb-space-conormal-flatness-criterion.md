## Worker report

The module Sheaf.AlgebraicGeometry.SpaceConormalFlatnessCriterion states Stacks
Tag 06BH (spaces-more-morphisms.tex, lemma-deform). It adds the definition
`AlgebraicGeometry.AlgebraicSpace.firstOrderConormalMap` and the theorem
`AlgebraicGeometry.AlgebraicSpace.space_conormal_flatness_criterion`.
The latter has `sorry` as its entire proof; nothing is proved in this delivery.
The map is selected from the existing UNIQUE existence theorem
`space_conormal_map`, whose normalization determines it as an actual morphism.
It is not chosen from a bare nonempty set of maps. No new mathematical notion,
new node, dependency repair or statement correction is needed.

Hypotheses and clauses, individually:

- A scheme S: `{S : Scheme.{u}}`, with explicit universe u.
- The four algebraic spaces over S: `{X Y X' Y' : AlgebraicSpace S}`.
  These are the existing full subcategory of fppf sheaves with representable
  diagonal and an etale surjective scheme atlas. Morphisms are its actual
  sheaf morphisms, not morphisms of schemes or arbitrary ringed spaces.
- The two horizontal arrows and the two vertical arrows:
  `(f : X ⟶ Y) (f' : X' ⟶ Y') (i : X ⟶ X') (j : Y ⟶ Y')`.
- A commutative square: `(h : i ≫ f' = f ≫ j)`.
- Both closed immersions are first-order thickenings:
  `(hi : IsSpaceFirstOrderThickening i)` and the corresponding `hj`.
  This existing predicate tests the representable morphism on every scheme
  base change, using the existing scheme predicate
  `IsFirstOrderThickening p.left = (IsClosedImmersion p.left ∧ p.left.ker ^ 2 = ⊥)`.
  A square-zero defining ideal implies surjectivity on underlying points, so
  the requirement that the underlying spaces agree is included, not omitted.
- Flatness of f: `(hf : MapIsFlat f)`, the existing all-compatible-etale-charts
  predicate applied to Mathlib's scheme `Flat`.
- The two conormal sheaves: `spaceConormal i` and `spaceConormal j`.
  By definition each is tensor pullback of the actual structural kernel:
  `(moduleTensorPullback i).obj (kernel (moduleStructureMap i))`.
  This is I/I² on the reduced small etale site; square zero identifies it
  with I. No arbitrary ideal, ideal-module identification, or substitute
  coefficient sheaf is supplied as a hypothesis.
- The source of the map: `(moduleTensorPullback f).obj (spaceConormal j)`.
  This is the previously recorded tensor pullback, namely
  O_X tensor over f^{-1}O_Y with f^{-1}C_{Y/Y'}, normalized by its adjunction
  unit and the chart tensors `moduleTensorSection`.
- The canonical map: `firstOrderConormalMap f f' i j hi hj h`.
  Its body selects the map whose UNIQUE existence is the existing theorem
  `space_conormal_map f f' i j hi hj h`. Its property
  `IsSpaceConormalMap` sends the iterated local tensor 1 tensor (1 tensor s)
  to 1 tensor the actual ring-map image of s, on every compatible chart square.
  Module linearity gives the formula for arbitrary a. Under I/I² = I, this
  is exactly a-lift times f'-sharp(s). Different lifts differ by I_X, and
  f'-sharp(s) lies in I_X, so the square-zero product vanishes.
- Flatness of f': `MapIsFlat f'`, with the same chart predicate as for f.
- The canonical morphism X to X' times over Y' with Y: the actual sheaf map
  `Limits.pullback.lift i.hom f.hom (congrArg (fun k ↦ k.hom) h)`.
  The pullback is the sheaf pullback of f'.hom and j.hom in this order;
  `fibreProduct_isAlgebraicSpace` guarantees that it is an algebraic space.
  `IsIso` is exactly that this canonical morphism is an isomorphism.
- The conjunction of these last two assertions is equivalent (`↔`) to
  `IsIso (firstOrderConormalMap f f' i j hi hj h)`.
- No finite-presentation, finite-type, representability of f or f',
  Noetherian, nonempty-space, or characteristic hypothesis is imposed.

Dependency declarations read and used (full signatures and docstrings read):

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `AlgebraicGeometry.Flat`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  `AlgebraicGeometry.IsClosedImmersion`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicGeometry.AlgebraicSpace`,
  its `EtaleSite`, `structureSheaf`, and `Modules`.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses:
  the recorded independent-universe tensor interface, publicly imported.
- Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData:
  `IsSpaceFirstOrderThickening`, using the upstream scheme predicate in
  WeilConjectures.AlgebraicGeometry.Thickening. Its existing definition owner
  def-sfb-space-square-zero-extension-data is added to stmt_deps.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: `MapIsFlat` and
  `MapIsLocally`. Owner def-sfb-space-morphism-properties added to stmt_deps.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations:
  `moduleTensorPullback`, `moduleTensorAdjunction`, `moduleTensorSection`.
  Owner def-trf-space-etale-module-functors added to stmt_deps; these are
  publicly available through SpaceUniversalConormal.
- Sheaf.AlgebraicGeometry.SpaceUniversalConormal: `spaceKernel`,
  `spaceConormal`, `IsSpaceConormalMap`, `space_conormal_map`.
  Existing landed owner lem-sfb-space-universal-conormal added to stmt_deps.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  `fibreProduct_isAlgebraicSpace`. Its owner added to stmt_deps.

The mathematical proof dependency lem-sfb-space-square-zero-flatness-criterion
has no Lean record or Mathlib match in the read repository, so there is no
module to import for it. It is not needed to type this statement; its existing
DAG proof remains unchanged and is copied step by step into the docstring.

Edge cases checked against the node and source:

- Zero ideals / identity thickenings: conormal modules are zero and their
  canonical map is invertible; the conclusion reduces to the given flatness.
- Empty spaces and charts: no nonempty hypothesis or point selection is used;
  the zero module and canonical pullback conditions retain their meaning.
- X = Y = Spec k, X' = Y' = Spec k[e]/e², with f and f' identities:
  the map on the one-dimensional ideal is the identity and both sides hold.
- X = X' = Spec k, Y = Spec k, Y' = Spec k[e]/e²:
  the conormal map k -> 0 is not invertible and f' is not flat.
- X' = Spec k[e,d]/(e,d)² mapping to Y' = Spec k[e]/e²,
  with both reductions Spec k: the conormal map k -> k² is not invertible;
  the thickened map is not flat. Thus the statement does not silently keep
  only the surjectivity or the Cartesian part of the criterion.
- No restriction on u beyond the existing scheme/algebraic-space size
  convention; every site, coefficient and index universe comes from those
  recorded notions, with no newly imposed universe equality.

Searches made on 2026-10-24:

- msearch.py leanfinder, query "Flatness and cartesianness of square zero
  thickenings of algebraic spaces detected by the conormal map": 8 hits,
  including scheme `AlgebraicGeometry.Flat`, formally unramified and smooth
  predicates; no conormal flatness criterion for algebraic spaces.
- msearch.py loogle, query `Module.Flat, "TensorProduct"`: 12 hits,
  including flat tensor instances and tensor injectivity lemmas; no match.
- msearch.py grep, query `conormal|Conormal|[Ff]lat.*[Nn]ilpotent`, subdirectory
  AlgebraicGeometry: 0 hits.
- msearch.py leansearch, query "Flatness criterion for first order thickenings
  by isomorphism of conormal modules": 8 hits, general module flatness,
  localization and smoothness-flatness results; no match.
- rg on lean/WeilConjectures and lean/Sheaf for conormal, Conormal,
  FirstOrderThickening, SquareZeroThickening, MapIsFlat and related criterion
  names found the existing notion owners above; scheme conormal base change
  and formal-unramifiedness results do not state the present equivalence.
- rg for the exact item id in lean/WeilConjectures: no hit. The proposed
  declaration names do not occur in Mathlib, the source library, the project
  or dag/lean_names_upstream.json.

No STATEMENT-DISPUTED flag or mathematical node fault was found. The withdrawn
CompactObject example was followed through its current node record to the
upstream WeilConjectures.CategoryTheory.CompactObject example.

Validation: scompile.py compiled the module in sandbox and library module
positions cleanly (32.6 s and 5.7 s, respectively); no compiler errors or
unexpected warnings. All binders and the universe are explicit, autoImplicit
is disabled, and every line is at most 100 characters. The required dry run
and delivery checks follow this compilation.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
