## Worker report

The module Sheaf.AlgebraicGeometry.AlgebraicSpaceUCSurjectionSeparation states
AlgebraicGeometry.AlgebraicSpace.separation_of_surjective_universallyClosed, with
one postponed theorem and no definitions or proofs. Its proof is `sorry`.
The item statement, dependencies and accepted split are unchanged; only `lean`
is recorded. The previous stage-1 refusal is inapplicable to this stage-2 record
(coord/brief-stage2.md section 0). The current queue explicitly assigns stage 2.

Clause-by-clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`; `universe u` and
  `set_option autoImplicit false` bind all universes and variables explicitly.
- Algebraic spaces over that base and their arbitrary morphism are
  `(X Y : AlgebraicSpace S) (f : X ⟶ Y)`. Their objects are fppf sheaves with
  representable diagonal and a representable surjective etale scheme atlas.
- Surjectivity on field-valued point classes is exactly
  `hsurj : Function.Surjective (mapPoint f.hom.hom)`. This does not require f
  to be representable or surjective on sections over each scheme.
- Universal closedness against every algebraic-space base change is exactly
  `hclosed : MapIsUniversallyClosed f`. That definition tests the closedness of
  `mapPoint` on the second projection of the existing sheaf pullback, for every
  algebraic space Y' and map Y' -> Y. No tests or finiteness cases are dropped.
- The first implication renders absolute quasi-separatedness: for every pair of
  affine schemes U,V over S and maps a,b into the space,
  `CompactSpace (Point (Limits.pullback a b))`. This is exactly the equivalence
  (1) iff (3) of Stacks 0AHR, read in spaces-properties.tex. CompactSpace on Point
  uses the recorded final atlas topology, so it says every open cover has a
  finite subcover. This matches the already landed spelling of absolute
  quasi-separatedness in AlgebraicSpaceCoherentFilteredUnion.
- The second, separate implication renders the absolute diagonal being a closed
  immersion. For every such affine pair it asserts a representing scheme W,
  projections p,q, the square
  `IsPullback (yoneda.map p) (yoneda.map q) a b`, and
  `IsClosedImmersion (prod.lift p.left q.left)`. Thus W represents U x_X V and
  its canonical map to U x_Z V is a closed immersion. Here `prod.lift` is in
  Scheme, since p.left and q.left are scheme morphisms. It is NOT the product
  in Over S. Scheme products are over Spec Z (the universe-lifted terminal
  scheme), even for a nonseparated S. This is the closed-immersion form of
  Stacks 0AHS(2), equivalently the surjective ring homomorphism from the tensor
  product over Z in that clause. Since U x_Z V is affine, a closed immersion
  is precisely an affine W with that surjective coordinate homomorphism.
  The representability witness is canonical up to unique isomorphism by its
  pullback square; no arbitrary map substitutes for the diagonal.
- The conclusions apply the identical predicates to Y. The outer conjunction
  is `(QS X -> QS Y) ∧ (Sep X -> Sep Y)`: neither hypothesis is required for
  the other conclusion. There is no finite type, Noetherian, flatness,
  nonemptiness, representability-of-f or base-separation assumption.

Sources read: spaces-morphisms.tex, Tag 05Z2 statement and full proof;
spaces-properties.tex, Tag 03BS (absolute separation definition), Tag 0AHR
(statement and proof), and Tag 0AHS (statement and proof). In particular the
source itself reduces the affine-pair characterizations to Spec Z, justifying
the use of these exact equivalent formulations rather than relative diagonals.
No statement correction or new notion is needed.

Dependency interfaces read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  IsRepresentableWith, IsRepresentable, IsEtale and IsAlgebraicSpace. The
  closed-immersion tests use the same scheme-representing pullback squares as
  IsRepresentableWith; there is no replacement definition of algebraic spaces.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace, etaleCover_pullback and etale_fibreProduct_isScheme.
  Limits.pullback is the same sheaf/presheaf fibre product in these interfaces.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: PointRepresentative.map,
  pointImage and pointTopologicalSpace; Point and schemePointMap are imported
  from AlgebraicSpacePointClasses.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties:
  MapIsUniversallyClosed, with mapPoint from its public import ProperCurveModuli.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion.
- The size-convention node is metatheoretic; explicit universe u is used
  consistently for schemes and coefficient sets, Point lives in u+1, and the
  full category of spaces lives in the corresponding larger universe.

The available proof dependencies are imported privately:
Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed,
Mathlib.AlgebraicGeometry.Morphisms.Separated,
Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
Mathlib.AlgebraicGeometry.Morphisms.Proper, and
Mathlib.AlgebraicGeometry.ZariskisMainTheorem. They supply
instQuasiCompactOfUniversallyClosed, IsSeparated.isSeparated_of_mono,
LocallyOfFiniteType, IsProper and IsClosedImmersion.iff_isProper_and_mono.
The statement dependencies also appearing in proof_deps are public imports.
These proof nodes have no Lean record and thus no import yet:
lem-sfb-space-change-base-to-integers, lem-a1-space-point-open-calculus,
lem-sfb-space-universally-closed-quasicompact, lem-sfb-qc-space-affine-etale-atlas,
lem-sfb-space-closed-subspace-proper, lem-sfb-space-diagonal-scheme-tests.
They are named in the complete six-step proof docstring for subsequent stage 3.
None is needed merely to type this statement.

Edge cases checked mathematically:

- Empty X forces the point set of Y empty by hsurj. Empty affine tests and
  empty pullbacks remain allowed; they are compact and the empty scheme gives
  the closed-immersion witness. No nonemptiness binder occurs.
- Identity/isomorphism f gives each implication with exactly the same predicate.
- An infinite disjoint union is not assumed compact; the assertion concerns its
  diagonal, not CompactSpace of X itself. No accidental quasi-compactness
  hypothesis on X or Y has been inserted.
- For nonseparated S, take X=Y=S with f the identity. The relative diagonal
  over S is trivially closed, while the absolute diagonal need not be. The
  present affine-pair closed-immersion test detects the absolute diagonal via
  U x_Z V, so it does not confuse these conditions.
- Independent implications allow quasi-separated X which is not separated.
  Arbitrary characteristic and non-Noetherian bases are retained.

Searches for existing declarations (all actual runs through msearch.py and rg):

- LeanFinder query: "A universally closed surjective morphism of algebraic spaces
  descends absolute quasi-separatedness and separatedness"; eight hits, including
  UniversallyClosed.of_comp_surjective and flat-descent scheme results. All
  returned algebraic-geometry interfaces quantify over Scheme, not AlgebraicSpace.
- Loogle query: `"UniversallyClosed", "IsSeparated"`; two scheme results,
  instHasOfPostcompPropertySchemeUniversallyClosedIsSeparated and
  UniversallyClosed.of_comp_of_isSeparated; neither states this node.
- Mathlib grep: `AlgebraicSpace|[Uu]niversallyClosed.*[Ss]eparated` in
  AlgebraicGeometry; three lines in Morphisms/Proper.lean concerning schemes.
- LeanSearch query: "The absolute diagonal of an algebraic space over a scheme S
  is the diagonal after forgetting the base scheme to Spec Z"; eight hits,
  including Scheme.isSeparated_iff_isClosedImmersion_prod_lift and scheme
  diagonal results; no algebraic-space statement.
- rg of lean/WeilConjectures and lean/Sheaf for surjective universally closed
  separation and absolute diagonals; read
  WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed in
  full. Its `isSeparated_of_surjective_universallyClosed` is for scheme maps to
  a scheme base, so it is not the present arbitrary algebraic-space statement.
- `grep -rn` of this node id in lean/WeilConjectures: no hit. rg of
  dag/lean_names_upstream.json finds only the scheme analogue's distinct node.
  `blueprint_refs.py search 'absolute diagonal'` returned zero blueprint nodes.
  No matching declaration named separation_of_surjective_universallyClosed
  exists in either library. The report adds no duplicate definition.

Validation: scompile.py compiled the delivered module in isolation both as its
sandbox module and at its intended library module path, with no errors or warnings.
The unchanged theorem has a single expected sorry. The delivery's dry run and
final delivery are run with deliver2.py; their results are reported by that tool.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
