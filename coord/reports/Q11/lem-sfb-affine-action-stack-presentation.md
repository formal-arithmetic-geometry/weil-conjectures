## Worker report

The module Sheaf.AlgebraicGeometry.AffineActionStackPresentation states the full
node in six concluding theorems and supplies concrete helpers. Every theorem has
proof `sorry`; no mathematical result is proved. No statement correction, disputed
claim or dependency interface replacement was needed. Two definition nodes supply
missing generic predicates; neither reconstructs the quotient stack.

Hypotheses, one by one:

- Field k: `(k : Type u) [Field k]`.
- Affine U = Spec E: `affineActionScheme k E`, the recorded definition, with
  `(E : Type u) [CommRing E] [Algebra k E]` and `[Algebra.FiniteType k E]`.
- Group scheme over k: `G : Over (Spec (.of k))` with `[GrpObj G]`.
- Smooth, affine, finite type G: `[Smooth G.hom] [IsAffineHom G.hom]`
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
- Specified left action: `[ModObj G (affineActionScheme k E)]`; the actual action
  arrow is `ModObj.smul`, including the unit and associativity identities.
- Quotient and canonical atlas: the recorded `affineActionQuotientStack k E G`
  and `SchemeAction.quotientAtlas G (affineActionScheme k E)`. No alternative
  stackification or unrelated functor is substituted.

Clauses, one by one:

- `affine_action_stack_presentation` gives `IsAlgebraicModuliStack` and
  `IsSmoothModuliAtlas` of this exact atlas. Finite type is an existential smooth
  scheme atlas with `LocallyOfFiniteType W.hom` and `QuasiCompact W.hom`.
  It does not assume that U is smooth over k.
- Its affine diagonal is `HasSchemeStackDiagonalWith (@IsAffineHom)`.
  Scheme-valued tests of all pairs retain both projections of the equivalence.
  This is the scheme-test version of an affine diagonal: on affine targets the
  representing source is affine, and arbitrary tests follow by affine localization.
- Its displayed pullback is `IsSchemeStackDiagonalPresentation` with R = G tensor U,
  first projection `ModObj.smul` and second projection `snd G U`. Thus the arrow
  to U tensor U is exactly `affineRelation`, not just an abstractly isomorphic
  relation with unspecified projections.
- `affine_action_stack_diagonal_quasiFinite` assumes for every algebraically closed
  extension `[Algebra k Ω]` and every actual point v that the topological Krull
  dimension of `affineStabilizer ... v` equals zero. That stabilizer is the entire
  scheme fibre of `(a,pr₂)` at `(v,v)`; it represents g v = v, including nilpotents.
  The conclusion tests the diagonal by `LocallyOfFiniteType`, `QuasiCompact`,
  `Finite ↥(Limits.pullback f y)` for every algebraically closed geometric y, and
  `IsClosedImmersion (pullback.diagonal f)`. This is the node's explicit
  quasi-finite/separated convention, with the relative diagonal of the diagonal.
- `affine_action_stack_space_maps` covers every `Z : AlgebraicSpace (Spec (.of k))`.
  Every based functor restricts, by a vertical comparison, to a presheaf map b
  with `yoneda.map a ≫ b = yoneda.map pr₂ ≫ b`. Every such invariant b extends,
  and any other extension is vertically naturally isomorphic. This gives exactly
  the stated identification of maps modulo natural isomorphism; no separatedness
  assumption is imposed on Z.
- `affine_action_stack_geometric_orbits` states bijectivity of the canonical
  `affineOrbitToClasses`. Its domain is Mathlib's `MulAction.orbitRel` quotient
  for the actual group of Ω-points; the codomain is the skeleton of the actual
  torsor fibre category (not a replacement set of presumed trivial torsors).
  `affineAtlasPoint` is precisely the recorded trivial torsor attached to x.
- `affineInvariants` is `RingHom.eqLocus` of the action pullback after swapping
  factors and the first projection pullback. The canonical
  `affineProductCoordinates` identifies this ring of functions with E tensor k[G].
  It is selected from UNIQUE existence characterized on both tensor factors, not
  from an unconstrained existence theorem. `affineTensorCoaction` and
  `affineInvariants_mem_iff` display exactly rho(e) = e tensor 1 in the required
  tensor-factor order. k[G] is global sections of the actual group scheme with
  the actual pullback coefficient map, without a chosen coordinate presentation.
- `affineInvariantSpectrum` is Spec of this actual equalizer, using restriction of
  the specified k-coefficient map. `affineInvariantProjection` is Spec of its
  literal subring inclusion. `affine_action_stack_invariant_spectrum` gives the
  map from the specified quotient whose atlas composite is exactly this map,
  with vertical uniqueness. No finite-generation claim on E^G is introduced.
- `affine_action_stack_pgl` covers every r with `1 ≤ r` over every field. It gives
  a group object representing the scalar quotient and its smooth/affine/finite-type
  structure. These are precisely the hypotheses of the preceding general
  theorems for any of its actions. There is no characteristic restriction and no
  restriction that r be invertible. `IsProjectiveLinearQuotient` retains local
  rather than global matrix lifts, as the fppf quotient requires.

Dependency declarations read and used:

- Sheaf.AlgebraicGeometry.AffineActionQuotientStack: `affineActionScheme`,
  `affineActionQuotientStack`, `SchemeAction.quotientAtlas`, `torsorFiber`,
  `torsorGroupoid`, `trivialObject`, and the actual pullback and map conventions.
- Sheaf.AlgebraicGeometry.AlgebraicModuliStack: `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas` and `SpaceMapIsSmooth`; the predicates choose no atlas.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids: `discreteModuli`,
  `discreteModuliMap`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `ModuliTwoIso`.
- Sheaf.AlgebraicGeometry.SchemeActionTorsorGroupoids: `TorsorObject`,
  `trivialObject`, group action and equivariant arrows; reused transitively.
- Mathlib.Algebra.Field.Defs: `Field`; Mathlib.FieldTheory.IsAlgClosed.Basic:
  `IsAlgClosed` (arbitrary algebraically closed extensions, not necessarily algebraic).
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`;
  Morphisms.QuasiCompact: `QuasiCompact`; their conjunction means finite type.
- Mathlib.Topology.KrullDimension: `topologicalKrullDim` in WithBot N-infinity.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`;
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: actual `pullback`.
- Mathlib.CategoryTheory.Skeletal: `Skeleton`, `toSkeleton`;
  Mathlib.GroupTheory.GroupAction.Defs: `MulAction.orbitRel`.
- Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective:
  `Matrix.ProjGenLinGroup`, `ProjGenLinGroup.map`, `mk_eq_mk_iff` and
  `GeneralLinearGroup.center_eq_range_scalar` give the matrix scalar quotient.
  This matrix group is reused; it is not itself a scheme or an fppf sheaf.

Proof-plan imports are GroupoidScheme, ActionGroupoidTorsorComparison,
StackChartwiseSmoothEtaleCalculus, AlgebraicSpaceFibreProductsEtaleCovers,
ZeroDimensionalNoetherianFiniteDiscrete, the upstream Nullstellensatz module,
Mathlib Noetherian and Spectral.Basic. The smooth-groupoid quotient, fppf locality,
and PGL reductive-structure proof dependencies currently have no Lean module,
so no nonexistent import was fabricated. No import cycle is introduced.

Sources read: local Stacks algebraic.tex lines 2340–2458, spaces-groupoids.tex
lines 2580–2645 and 2710–2755, examples-stacks.tex lines 1300–1400. They supply
exactly the relation projections, smooth atlas, algebraicity, coequalizer and
inverse-right-translation torsor conventions used here. Milne Example 5.49,
printed p.111 (PDF page 122), was read from the primary PDF at
https://www.jmilne.org/math/Books/iAG2017.pdf, confirming the scalar quotient.
The current blueprint contains no duplicate item statement for this supporting
node; the source route remains the node's existing inherited route.

Edge cases checked before writing and again against the final file:

- E may be the zero k-algebra, so U is empty. No Nontrivial E, nonempty scheme,
  geometric point, or positive dimension assumption excludes this case.
- The trivial group and r = 1 are included. Its quotient is U, and stabilizer
  dimension is zero. Positive-characteristic nonreduced finite stabilizers are
  tested as schemes, not by their finite group of geometric points alone.
- A positive-dimensional stabilizer (e.g. G acting trivially on a point) does not
  satisfy the conditional diagonal hypothesis; algebraicity/affineness remain.
- Non-algebraically-closed fields are not claimed to trivialize torsors. Every
  orbit-bijection claim explicitly assumes `IsAlgClosed Ω`.
- The space target may be nonseparated, and the invariant ring need not be finite
  type. Both cases remain in the statement.
- All rings, field extensions and test schemes use a common universe u, as the
  recorded big site does. No independent smaller test universe makes a universal
  condition vacuous. The entire construction is polymorphic in u.
- PGL matrices need only lift locally; global lifts were deliberately not made
  an assumption or conclusion of the quotient characterization.

Searches (actual calls recorded in searches.jsonl): LeanFinder query
“A quotient stack of an affine scheme by a smooth affine group has a smooth atlas
and affine diagonal” returned only scheme smoothness/affine-space results;
Loogle “GrpObj, ModObj” returned unknown identifier GrpObj, hence no usable hit;
Mathlib grep “quotientStack|PGL|ProjectiveGeneralLinear” in AlgebraicGeometry
returned three irrelevant Gluing hits. LeanSearch for the fppf projective-linear
scalar quotient returned PSL and projectivization declarations, not a group scheme.
The broader grep “PGL|HasSchemeDiagonalWith|IsSchemeDiagonalPresentation” located
Mathlib's matrix PGL, which was read and reused. LeanFinder/LeanSearch for a scheme
presentation of the diagonal returned scheme diagonal morphisms and their
properties, not the required stack predicate. Direct rg in lean/WeilConjectures,
lean/Sheaf and dag/lean_names_upstream.json found no requested generic predicate
or theorem; related AffinePGLAction and ModuliStackProperties were read.
`tools/blueprint_refs.py search 'diagonal presentation'` returned no match;
'projective general linear' returned no match; 'diagonal' returned existing
unrelated blueprint assertions. Ancestor command reports from.node = null for
this supporting node, so the two new records retain null and its inherited via.

All three modules compiled cleanly through scompile.py on 2026-10-24; main module
compiled in about 5.6 seconds. The final dry run also compiles every delivered file.

## New nodes

`def-sfb-scheme-stack-diagonal-presentation`: `IsSchemeStackDiagonalPresentation`
and `HasSchemeStackDiagonalWith` define a scheme-valued diagonal presentation
retaining both projections and a property of its map to the scheme product.
Source: Stacks Tags 04M9/04WZ. StablePointedModuliGroupoids supplies the two-fibre
product; ModuliStackProperties.HasProperModuliDiagonal only handles the proper
property and so cannot render affine or quasi-finite diagonal assertions. The
new predicate generalizes that existing projection convention without redefining
the two-fibre product. Its node records three logged searches; no prior generic
DAG definition or declaration was found.

`def-sfb-projective-linear-quotient`: `IsProjectiveLinearQuotient` specifies the
representability of the fppf scalar-quotient sheaf by a group scheme using the
existing Mathlib matrix quotient, natural injective maps, and local surjectivity.
Source: Milne Example 5.49. Existing PGL-related nodes are action data or theorems
asserting representability/geometry, and none gives this reusable predicate.
The new node records three logged searches. It makes no representability or
smoothness assertion; existence is a conclusion of the item's PGL theorem.
The definition makes sense in rank zero as well; the item's theorem and source
application concern every positive rank.

## Second reading by Q11

I reread the node and all three final files, without delegating (the dispatcher
explicitly prohibits other agents). This is a worker self-check; the maintainer's
independent review remains the independent reading promised in the dispatch.
The mapping above was checked against every hypothesis and clause. In particular:
the diagonal equivalence retains BOTH projections, the finite-type atlas does not
assume U smooth over k, geometric stabilizers are full scheme fibres, the orbit
map lands in the actual torsor fibre skeleton, the equalizer is transported into
E tensor k[G] in the specified order, and the invariant map's composite is the
literal Spec of inclusion. No statement change was made. The compile repairs
were namespace/scope and explicit scheme coercion repairs only. The matrix PGL
quotient was found in the broader grep and reused, rather than copied.
