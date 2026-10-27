## Worker report

The module `Sheaf.AlgebraicGeometry.ExceptionalCurveCount` states
`AlgebraicGeometry.exceptional_curve_count_of_proper_birational`, with its only
proof `sorry`. Its two real helper definitions spell out U_f and B(f), which
are introduced explicitly by this very node; these are not new independent
notions or unstated prerequisites. All three declarations are recorded in
`lean.declarations`. There are no other postponed theorems, new nodes,
dependency repairs, or statement corrections. The original node is changed
only in `lean`.

Source read: `literature/stacks-project/resolve.tex`,
`lemma-proper-birational-regular-surfaces` (Tag 0C5R), especially the first
proof paragraph at lines 4898--4910. That paragraph introduces the maximal
isomorphism open and induction on curves in fibres after a target point
blowup. The accepted node expands its omitted finite-measure details. The
module docstring carries all nine proof steps, including the closed-image
argument that produces a curve mapping onto the exceptional projective line;
it does not assert the source's stronger isomorphism-on-a-component remark.

Hypothesis and clause correspondence:

- Schemes and the actual morphism are `(X Y : Scheme.{u})` and `(f : X ⟶ Y)`.
  Every universe and variable is explicitly bound; `autoImplicit` is false.
- Integral X and Y are `[IsIntegral X] [IsIntegral Y]`, the recorded Mathlib
  predicates. In particular they are nonempty; the empty scheme is correctly
  outside the node's hypotheses.
- Noetherian X and Y are `[IsNoetherian X] [IsNoetherian Y]`. The Mathlib
  class extends `IsLocallyNoetherian` and `CompactSpace`, exactly the node's
  locally Noetherian plus quasi-compact convention.
- Regularity is `hX : IsRegularScheme X`, `hY : IsRegularScheme Y`, using the
  dependency's recorded locally-Noetherian and stalkwise-regular predicate.
- The dimension-two assumptions are `hdimX : topologicalKrullDim X = 2` and
  `hdimY : topologicalKrullDim Y = 2`; they are topological Krull dimensions,
  not a pure-dimensionality or finite-type-over-a-field assumption.
- Properness is `[IsProper f]`, the recorded Mathlib class.
- Birationality is `hbirational`: dense opens V in X and U in Y, an actual
  scheme isomorphism `e : V.toScheme ≅ U.toScheme`, and
  `V.ι ≫ f = e.hom ≫ U.ι`. The last equality makes the isomorphism the
  restriction of this f, not an arbitrary abstract common-open isomorphism.
- `f.isomorphismOpen` is literally `sSup {U : Y.Opens | IsIso (f ∣_ U)}`.
  The supremum of opens is their union; this tests the entire inverse image
  of U, not a selected open in the source. No maximality/existence premise
  is added to the theorem.
- `f.exceptionalCurves : Set (Set X)` is the comprehension of C satisfying
  `IsClosed C ∧ IsIrreducible C ∧ topologicalKrullDim C = 1 ∧
  ∃ y : Y, f '' C = {y}`. Here C coerces to the subtype with its subspace
  topology. Irreducibility includes nonemptiness. The singleton image is
  an equality, not just a containment, and imposes no condition on the
  residue field of y. This is exactly the node's B(f).
- The first conclusion `((f.isomorphismOpen : Set Y)ᶜ).Finite` states
  finiteness of the bad-point set.
- The second conclusion quantifies over every y outside that open and
  gives `IsClosed ({y} : Set Y)` and
  `ringKrullDim (Y.presheaf.stalk y) = 2`, separately retaining both the
  closed-point and local-dimension clauses.
- The third conclusion `f.exceptionalCurves.Finite` states finiteness of
  B(f), even if it is empty.
- The fourth conclusion `f.exceptionalCurves = ∅ ↔ IsIso f` is the full
  equivalence, in both directions.
- The final conclusion quantifies over every bad y and every proof hy of
  its closedness. Such a proof is supplied by the second conclusion; this
  binder is needed only to form the canonical reduced-point ideal and
  does not add an unproved closedness hypothesis or lose any bad point.
  Proof irrelevance makes the resulting construction independent of hy.
- Y' and b are the canonical
  `(Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).blowup` and its
  `.blowupMap`. Mathlib's vanishing ideal supplies the reduced induced
  point structure. Using the named canonical blowup fixes the same
  representative as the dependency, rather than adding an arbitrary
  blowup candidate or arbitrary morphism b.
- Every `g : X ⟶ Y'` is quantified. Its `IsProper` assumption, integral,
  regular, Noetherian and dimension-two target assumptions, and its
  dense-open birationality assumption all appear explicitly. This is
  exactly the list in the node's factorization clause, even where known
  geometric facts could derive some of these properties.
- `g ≫ ...blowupMap = f` is the specified equality f = b composed with g.
  The conclusion `g.exceptionalCurves ⊂ f.exceptionalCurves` is proper
  set containment, not only non-strict inclusion or a cardinal inequality.
  Both sets inhabit `Set (Set X)`, as required.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`
  and the bundled `AlgebraicGeometry.IsNoetherian`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  and the open-subscheme inclusions/restrictions used for birationality and U_f.
- `WeilConjectures.Blowup.Gluing`:
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and `.blowupMap`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.Topology.Irreducible`: `IsIrreducible`; this is the subset predicate
  identified explicitly by `def-weil-irreducible-components.mathlib_match`.
- The reduced centre also uses Mathlib's existing
  `Scheme.IdealSheafData.vanishingIdeal`, from
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`; its docstring explicitly
  identifies the quotient with the reduced induced closed subscheme.

Every already-stated proof dependency module is imported with a plain import.
The declarations read are `normal_modification_isomorphism_open_contains`,
`IsRegularLocalRing.isDiscreteValuationRing`,
`regular_normal_and_normal_decomposition`, `ringKrullDim_stalk_eq_coheight`,
`finite_of_isClosed_of_closed_points`,
`TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`,
`Scheme.fromSpecStalk_local_properties`,
`Scheme.IdealSheafData.blowupFlatBaseChange` and `.blowupFlatBaseChangeIso`,
`localSurfaceMaximalBlowupGeometry`, `Scheme.Hom.fiber`,
`ProjectiveLine.TwistData`, and `Scheme.regular_point_blowup_geometry`.
Scheme sobriety uses the `T0Space` and `QuasiSober` instances from Properties
and `IsGenericPoint.eq` from `Mathlib.Topology.Sober`. The two flat-base-change
nodes lack lean records but have closed upstream audit records; their recorded
upstream declarations were read and their module imported, without duplicating
them. The regular-surface geometry and projective-line modules are proof
imports only; the theorem does not replace its own hypotheses by their
conclusions.

Edge cases checked before drafting: if f is an isomorphism, U_f is all Y and
B(f) is empty, while the final bad-point clause has no instance. For a single
point blowup and g the identity on X, B(g) is empty and B(f) contains the
exceptional curve, giving the intended direction of strict containment.
Several bad points do not require selecting one in advance: every bad y
occurs in the final quantifier. Empty subsets cannot be exceptional curves,
and zero-dimensional fibre components are not counted. All images are taken
on the entire irreducible closed subset. Finite and imperfect residue fields
are permitted. No excellence, algebraic closedness, catenarity or base field
has been introduced. Dimension-zero or dimension-one schemes are excluded
by the node's dimension-two assumptions, not by an extra API restriction.

Searches made through the required launcher wrapper:

- LeanFinder: "A proper birational morphism of regular Noetherian surfaces
  contracts finitely many curves and factoring through the blowup of a point
  strictly decreases the contracted curves", and the retry query "Finite
  contracted curves of a proper birational surface morphism decrease after
  a target point blowup". Eight hits concern rational maps, finite-morphism
  base change, normalization or Weierstrass points, not this theorem.
- LeanSearch: "Finite exceptional curve set of a proper birational morphism
  of regular surfaces". Eight hits concern finite/proper morphisms and
  finite fibres, not one-dimensional contracted subsets or strict decrease.
- Loogle: `"AlgebraicGeometry", "exceptional"`: zero hits.
- Wrapper grep in Mathlib AlgebraicGeometry:
  `exceptional.*curve|contract.*curve|birational.*[Ff]inite`: zero hits.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf`, and the upstream
  item-id search: no statement of this node. Nearby results are the existing
  factorization consumer, blowup-geometry prerequisites and unrelated nodal
  contractions. Those are not the finite exceptional-curve measure lemma.
- Direct rg in Mathlib AlgebraicGeometry and both project roots for
  `isomorphismOpen|exceptionalCurves|contractedCurves|isoLocus|isIsoLocus|isomorphismLocus`:
  no scheme-map isomorphism-open or contracted-curve-set definition; the hits
  for isoLocus are natural-transformation isomorphism loci, a different notion.
  A further search `sSup.*IsIso|IsIso.*sSup` finds a module-map isomorphism
  locus, also a different object. The helpers here render notions already
  introduced by this item's statement, with the owning node's source tags.

Validation: `scompile.py Q81 lem-sfb-exceptional-curve-count` compiled the
module successfully in sandbox and library modes (1.9 and 2.0 seconds), with
no errors or unexpected warnings. No disputed mathematical claim or node
fault was found.

## Second reading by Q81

I reread the node, the full source paragraph, the two definitions and the
complete theorem signature after the successful compile. This is a worker
self-check; the maintainer's independent delivery review remains independent.
The read checks each hypothesis and conclusion using the correspondence
above. In particular I checked the dense-open equality binds the restriction
to f itself, the isomorphism open uses full target restrictions, singleton
image is equality, dimension uses the topology on C, the bad points are
proved closed rather than assumed closed, and the last relation is strict
containment of subsets of the same X. I checked the explicit integral,
regular, Noetherian and dimension-two assumptions on the actual canonical
blowup, and the separate proper/birational assumptions on g. There is no
claim of a canonical enumeration or chosen exceptional curve. No mismatch
or change was needed on this reading. Only the theorem uses sorry; both
helper definitions have concrete bodies, with no chosen unproved data.
