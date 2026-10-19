## Worker report

This is the stage-2 statement of `lem-per-uniformization-nodal-quotient-reduction`,
not another stage-1 split. Q74's reviewed split is retained unchanged. In particular,
its nine new proof nodes are neither duplicated nor re-split. The item had no `lean`
record when this work began. The previous worker's stale-dispatch diagnosis confused
stage-1 completion with existence of a stage-2 declaration.

The main module is `Sheaf.AlgebraicGeometry.UniformizationNodalQuotientReduction`.
It states `AlgebraicGeometry.uniformization_of_marked_nodal_quotient_resolution`.
Its sole postponed theorem has proof exactly `by sorry`; its docstring gives the
node's nine-step proof. The additional definition has real predicate data, no sorry.
No original statement, proof, proof-dependency or review field is changed.

Source checked directly: ILO, Expose IX, Theorem 1.2 and 1.3--1.4, printed
pp. 131--133 (PDF pages 137--139). The marked nodal quotient hypothesis is situation
(*) at the end of 1.4; the theorem is the conditional reduction, rather than the
unconditional regular-cover theorem. The source records admissibility, replacement
by the Sylow subgroup and normalization of dominating base-change components.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The fixed prime is `(ell : ℕ) [Fact ell.Prime]`.
- The assertion for every model is the argument `hresolve`, universally quantified
  over `Y Y' C X : Scheme.{u}`, all the morphisms, actions and markings below.
- `Y` affine, integral, Noetherian: `[IsAffine Y] [IsIntegral Y] [IsNoetherian Y]`.
  Excellence is `∀ U : Y.affineOpens, IsExcellent Γ(Y, U)`; regularity is
  `IsRegularScheme Y`; finite Krull dimension is
  `∃ d : ℕ, topologicalKrullDim Y ≤ d`. The latter does not choose a fixed bound.
- Invertibility on Y is `∀ y : Y, IsUnit (ell : Y.presheaf.stalk y)`.
- The closed boundary T is represented by its ideal `T : Y.IdealSheafData` with
  `IsStrictNormalCrossingsBoundary T`. All later appearances use `T.support`, so
  the assertion depends on its support as required.
- A finite ell-group is `G : Type u`, `[Group G] [Finite G]` and
  `∃ n : ℕ, Nat.card G = ell ^ n`. This includes the trivial group at n = 0.
  Finite groups may be represented in the scheme universe without a size restriction
  on their isomorphism classes.
- `b : Y' ⟶ Y` is finite by `[IsFinite b]`. `Y'` is integral by its instance,
  excellent by the affine-coordinate-ring condition, and normal by the dependency's
  `IsNormalScheme Y'`. The action is `aY' : G →* Aut Y'`; the equation
  `(aY' g).hom ≫ b = b` says it is over Y.
- V is `T.support.compl`; V' is `(b ⁻¹ᵁ T.support.compl).toScheme`. The dependency
  `Scheme.GaloisCoverAction G (Scheme.Opens.toScheme T.support.compl)` supplies the
  finite etale surjective torsor A, with `[ConnectedSpace A.Z]`. The isomorphism
  `e : A.Z ≅ V'` commutes with the structure maps. The following equation on every
  g identifies A's action with the restriction of aY', not an unrelated action.
  Thus this is precisely the connected finite etale G-torsor of the statement.
- The normalization field is `Y'.functionField`, canonically isomorphic to κ(V'):
  V' is a nonempty dense open of the integral Y', since the torsor is over the
  nonempty complement of an effective Cartier boundary on integral Y. The algebra
  `Y.functionField → Y'.functionField` is constrained by the equality of the
  corresponding generic-point morphisms with `Y'.fromSpecFunctionField ≫ b`.
  Hence it is the extension induced by b. The isomorphism
  `en : Y' ≅ Y.normalizationIn Y'.functionField` is over Y, by
  `en.hom ≫ Y.fromNormalizationIn Y'.functionField = b`. This uses the actual
  normalization in the extension field, not normalization in Y's own function field.
- `f : C ⟶ Y'` is projective, flat and locally finitely presented by
  `[IsHProjective f] [Flat f] [LocallyOfFinitePresentation f]`. Projectivity implies
  properness, hence quasi-compactness and quasi-separatedness; thus the stated
  finite-presentation clause is fully present, not just its local part.
- C is integral, Noetherian and separated by `[IsIntegral C] [IsNoetherian C]
  [C.IsSeparated]`; the latter is separation over the terminal scheme, equivalently
  the diagonal over Spec Z is closed. Excellence uses the same affine-ring predicate.
- Equivariance is `(aC g).hom ≫ f = f ≫ (aY' g).hom`, for `aC : G →* Aut C`.
- `HasNodalGeometricFibres f` states every geometric fibre is nonempty connected,
  of dimension one and smooth except for points with completed local ring
  `Ω[[u,v]]/(uv)`. Its recorded definition is imported and reused verbatim.
- Smoothness over V' is `∀ c : C, b (f c) ∉ T.support → c ∈ f.smoothLocus`.
- The marking is `D : C.IdealSheafData` with `D.IsInvertible` (effective Cartier),
  `D.comap (aC g).hom = D` (G-stability as a divisor),
  `IsFinite (D.subschemeι ≫ f)` and `Etale (D.subschemeι ≫ f)`, and
  `∀ c, c ∈ D.support → c ∈ f.smoothLocus`. All these concern the divisor scheme,
  not just its underlying set.
- `π : C ⟶ X` and `IsAdmissibleFiniteSchemeQuotient aC π` state admissibility,
  finiteness, invariance, the actual orbit-space topology and invariant structure
  sheaf. X is integral and Noetherian by its instances, excellent affine-locally.
- E is `E : X.IdealSheafData`, `E.IsInvertible`; the set inclusion is exactly
  `π ⁻¹' E.support ⊆ D.support ∪ (f ≫ b) ⁻¹' T.support`, rendering the defined B
  without introducing an independent or unconstrained boundary object.
- The marked assertion's conclusion gives `R`, `r : R ⟶ X`, `IsIntegral R`,
  `IsRegularScheme R`, `IsNoetherian R` and `IsProper r`. Dense U and dense
  `r ⁻¹' U` with `IsIso (r ∣_ U)` express isomorphism on dense open subschemes.
  This does not substitute arbitrary abstract function-field isomorphisms.
- There is an ideal H on R with `IsStrictNormalCrossingsBoundary H` and the exact
  support equality `H.support = r ⁻¹' E.support`.
- The consequence ranges over arbitrary reduced Noetherian `S`, with
  `∀ U : S.affineOpens, IsQuasiExcellent Γ(S, U)` and invertible ell on its stalks.
  The prescribed `Z : Set S` has `IsClosed Z` and `IsNowhereDense Z`. No finite
  dimension, integrality or excellence assumption is imposed on S.
- The target object `base : PrimeToEllAlteration.Alt S` satisfies
  `base.obj = Over.mk (𝟙 S)`. This only bundles the identity target in alt/S.
- The finite family is `n : ℕ`, `T : Fin n → PrimeToEllAlteration.Alt S`, with
  arrows `q : ∀ i, T i ⟶ base` and the exact dependency predicate
  `PrimeToEllAlteration.IsCoveringFamily ell T q`. Each source is regular and
  Noetherian. Its ideal H is an snc boundary with support exactly the preimage
  of Z under `(T i).obj.hom`. The equations for morphisms of alt/S and the
  identity target identify this with the covering arrow's map to S.
- Membership in alt/S already includes finite type (locally finite type plus
  quasi-compactness), reducedness, maximal dominance and generic finiteness.
  Thus the final finite-type clause is supplied by the objects, not omitted.

Dependency declarations used (their full signatures/docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  `Scheme.Hom.app`, `appLE` and the open-subscheme API.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; scheme Noetherianity
  is `Mathlib.AlgebraicGeometry.Noetherian.IsNoetherian`.
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, `IsQuasiExcellent`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`, `IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  the alteration objects also include `QuasiCompact`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `Scheme.IdealSheafData.IsInvertible` (not abstract line bundles).
- `Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology`:
  `PrimeToEllAlteration.Alt`, `topology`, `IsCoveringFamily`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`;
  its current source was obtained with `scompile.py --source`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `Scheme.Hom.smoothLocus`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, as used
  in the imported geometric-fibre predicate; no private fibre construction.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `Scheme.normalization`, `normalizationIn`, `fromNormalizationIn`.
- `Sheaf.AlgebraicGeometry.NormalScheme`: `IsNormalScheme`, `Scheme.GaloisCoverAction`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`,
  as used by the recorded projective, Cartier and boundary notions.
- Added existing recorded dependencies: `def-trf-nodal-geometric-fibres`
  (`Sheaf.AlgebraicGeometry.NodalGeometricFibres.HasNodalGeometricFibres`) and
  `def-fin-normalization-extension` (the upstream `Scheme.normalizationIn` and
  `Scheme.fromNormalizationIn`). Their declarations are reused, not rewritten.
- Available proof modules `Sheaf.AlgebraicGeometry.ClosedDominantDimension` and
  `Sheaf.RingTheory.IsExcellentFiniteTypeLocalization` are imported privately.
  `WeilConjectures.AlgebraicGeometry.Regular` is reached through the regular-scheme
  dependency; the unstated proof nodes remain the existing nine-step DAG plan.

Edge cases checked before finalization: empty boundary T and empty marking D are
permitted (unit ideal); E may also be empty. The trivial group is allowed. Integral
Y, Y', C and X are nonempty, as required. No smoothness of C or X is assumed, and
Y' is normal rather than regular. A nodal fibre with several components remains
allowed. `ConnectedSpace` includes nonemptiness, so empty fibres cannot enter.
The consequence allows empty S, empty Z and an empty covering index (n = 0).
It does not impose a finite-dimensional bound on S. All universes/variables are
explicit, `autoImplicit` is false, and there are no let binders in the statement.

Searches for an existing statement and missing quotient notion:

- `msearch.py leanfinder`: “Reduction of prime to ell alteration regular coverings
  to resolution of marked nodal curve quotients”: 8 unrelated hits (Weierstrass
  reduction and smooth/etale definitions), no reduction theorem.
- `msearch.py loogle`: `AlgebraicGeometry.IsIntegral, AlgebraicGeometry.IsRegularScheme`:
  no hits; Mathlib does not know the project's regular-scheme declaration.
- `msearch.py grep`: `nodal|Nodal|IsSchemeQuotient` in AlgebraicGeometry: 0 hits.
- `msearch.py leansearch`: “A finite group acts admissibly on a scheme and the
  quotient has invariant sections and orbit quotient topology”: 8 set-theoretic
  orbit quotient/proper group-action hits, none about scheme invariant sheaves.
- `msearch.py leanfinder`: “finite admissible scheme quotient invariant structure
  sheaf and orbit space”: 8 hits about finite scheme morphisms, affine quotients
  by ideals and gluing; no finite-group scheme quotient definition.
- `msearch.py loogle`: `"quotient", AlgebraicGeometry.Scheme`: 5 hits, all
  `Scheme.Hom.liftQuotient`, its equations, the topology of a flat surjection or
  quotient rings in PointsPi; none says the required notion.
- `msearch.py grep`: `IsAdmissibleFiniteSchemeQuotient|admissible|invariant.*sheaf`
  in AlgebraicGeometry: 5 hits about admissible Weierstrass variable changes only.
- `rg` on Mathlib, upstream WeilConjectures and side `lean/Sheaf` for nodal,
  quotient/action and normalization names located the imported nodal predicate,
  GaloisCoverAction, alteration topology and normalizationIn. No declaration says
  this conditional reduction, and no invariant-sheaf orbit quotient predicate exists.
  `rg` for the item id in upstream source found no declaration.
- Definition-node search for quotient/admissible/orbit in `dag/nodes` found
  no definition for admissible finite scheme quotients. The existing statement
  nodes about quotient existence are different assertions, not definitions.
  `tools/blueprint_refs.py search 'marked nodal quotient'` and
  `... search 'finite scheme quotient'` both returned zero matching blueprint nodes.

No STATEMENT-DISPUTED issue or node-statement correction is needed. The new predicate
only supplies the explicitly described missing quotient notion. Original dependencies
are retained; the new definition and two existing recorded notions are added.

Validation: `scompile.py` compiled both delivered files individually, in dependency
order, against the private overlay/live library, without errors or warnings.

## New nodes

`def-per-admissible-finite-scheme-quotient` defines exactly the finite quotient of an
admissible finite scheme action required by IX 1.4, pp. 132--133. Its module is
`Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient`, declaration
`AlgebraicGeometry.IsAdmissibleFiniteSchemeQuotient`. Admissibility is affine-open
containment of every orbit. The finite invariant map is a topological quotient
with fibres equal to orbits. Its map on sections of every open is injective with
image the invariant sections. The invariance formula uses actual pullback/restriction
maps into every common subopen; these subopens cover the domain, and quotient
invariance makes the full inverse-image open itself stable. This is precisely
`O_X = (π_* O_C)^G`, not merely a categorical quotient universal property.
The node records the raw LeanSearch, LeanFinder, Loogle and Mathlib-grep results,
plus DAG/upstream/side source searches above. The existing torsor notion forces
free action and cannot replace a possibly ramified finite quotient. No quotient
scheme is fabricated by choice; this is a property of the supplied action and map.

## Second reading by Q112

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
