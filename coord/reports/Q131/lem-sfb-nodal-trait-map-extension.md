## Worker report

The module `Sheaf.AlgebraicGeometry.NodalTraitMapExtension` states
`AlgebraicGeometry.nodal_trait_map_extension`, with one postponed theorem and four
real constructions owned by this node. No theorem is proved in this delivery.

Hypothesis and conclusion audit against the unchanged node:

- DVR `A`: `(A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]`.
- Fraction field `F`: `(F : Type u) [Field F] [Algebra A F] [IsFractionRing A F]`.
  The trait is literally `Spec (.of A)` and its generic inclusion is literally
  `Spec.map (CommRingCat.ofHom (algebraMap A F))` throughout.
- Source and target: `C X : Scheme.{u}`, with structure morphisms `f` and `g`.
  `[IsHProjective f] [Flat f] [LocallyOfFinitePresentation f]` renders the source
  conditions. H-projectivity implies properness, hence quasi-compactness and
  quasi-separatedness, so local finite presentation here gives finite presentation.
- Smooth geometrically integral generic fibre: the `Smooth` and
  `GeometricallyIntegral` instances on `pullback.snd f` along the generic inclusion.
- Nonempty connected reduced geometric fibres of pure dimension one: `hfib`
  quantifies over every algebraically closed `Ω : Type u` and every geometric point
  `t : Spec Ω ⟶ Spec A`; it asserts `ConnectedSpace`, `IsReduced`, and
  `(pullback f t).IsPureDimension 1`. ConnectedSpace includes nonemptiness.
  Scheme universe and geometric-field universe agree, following Mathlib's geometric
  morphism convention; no independent smaller test universe is introduced.
- Nodal singularities: `hnodal` quantifies over the same geometric points and all
  fibre points outside the smooth locus, and gives the ring isomorphism from the
  maximal-ideal adic completion of the stalk to
  `MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}`. Over an algebraically closed
  field the singular points of a finite-type curve are exactly its nonsmooth points.
  The node asks for a completed-local-ring isomorphism, not a chosen coefficient action.
- H-projective target: `[IsHProjective g]`, with no flatness, reducedness,
  integrality, or dimension hypothesis on `X`.
- Absence of rational curves: `hnoRational` tests every geometric fibre and every
  `a : ProjectiveLine (Spec Ω) ⟶ pullback g t`. The displayed equation says `a`
  is over Ω. The conclusion provides a section `q : Spec Ω ⟶ pullback g t`
  with `q ≫ pullback.snd g t = 𝟙 _` and the factorization of `a` through `q`.
  Thus “constant” means scheme-theoretic factorization through an Ω-point.
- Generic map: `uη` is a morphism between the two generic pullbacks; `huη` makes
  it an F-morphism. No nonconstancy or dominance condition is imposed.
- Reduced graph closure: `genericGraph` is the pullback lift of the generic source
  projection and `uη` followed by the generic target projection. `graphClosureIdeal`
  applies the existing `Scheme.IdealSheafData.vanishingIdeal` to the closed topological
  closure of its range. `graphClosure` is that ideal's `subscheme`, and
  `graphProjection` is its `subschemeι` followed by `pullback.fst f g`.
  The small proof in `genericGraph` only checks commutativity required to construct
  the pullback lift; its data is explicit, with no existence choice or sorry.
- Conclusions: `IsIntegral C`, `IsIntegral (graphClosure ...)`, stalkwise
  `IsDomain` and `IsIntegrallyClosed` on `C`, and `IsIso (graphProjection ...)`.
- Extension: `∃ v : C ⟶ X, v ≫ g = f ∧ ...`; the last equation identifies
  its restriction on the generic fibre with `uη` after projection to `X`.
  Together with `huη`, the pullback universal property says precisely that the
  base-changed extension is the given F-morphism.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective` and its properness instance.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (reexported by Smooth).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` and
  `Scheme.Hom.smoothLocus`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`:
  `AlgebraicGeometry.GeometricallyIntegral`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, its two projections and its canonical lift.
  This is also the recorded geometric-fibre interface.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, used by the existing
  `AlgebraicGeometry.Scheme.IsPureDimension` in `Sheaf.AlgebraicGeometry.PureDimension`.
  The landed node `def-weil-pure-dimension` is added to stmt_deps, since total
  dimension one alone would not express purity. Its definition and docstring were read.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `MvPowerSeries.X`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`:
  `ProjectiveLine.TwistData` is the recorded standard-P1 node, and the module imports
  the actual `AlgebraicGeometry.ProjectiveLine` from ProjectiveSpace.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`, `IsReduced`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` and `.Basic`:
  `Scheme.IdealSheafData.subscheme`, `subschemeι`, `vanishingIdeal`, `Scheme.nilradical`.
  The reduced graph uses the reduced-induced vanishing ideal, not the reduction of
  an unspecified subscheme. The recorded reduction and closed-immersion interfaces
  are present through these imports.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`.

Proof-only imports are the recorded ProjectiveBaseChange, ReducedInducedClosedSubscheme,
ProperQuasiFinite, FiniteBirationalNormalIso, and Mathlib Noetherian interfaces.
Mathlib closed-immersion composition/base change and surjective base change arrive
through the scheme imports. `lem-sfb-smooth-generic-nodal-trait-normality` has no Lean
record, so there is no module to import. The rational-domination node has a recorded
module `Sheaf.AlgebraicGeometry.NodalTraitRationalDomination`, but its source is absent
locally and `scompile.py --source Sheaf.AlgebraicGeometry.NodalTraitRationalDomination`
returned `Module source unavailable`. Accordingly that unavailable proof-only module
is not imported. Neither missing proof statement is a notion needed to type this
statement, and neither is copied or used as an assumption. Their full proof roles
are recorded in the theorem's five-step docstring for stage 3.

Edge cases checked before writing: constant generic maps are admitted; nonflat,
nonreduced, reducible and higher-dimensional targets are admitted; the empty target
makes the generic map unavailable rather than imposing an extra nonemptiness
hypothesis; empty source fibres are excluded by ConnectedSpace; disconnected or
non-pure fibres are excluded explicitly. Smooth fibres make the nodal condition
vacuous. Nodal total-space equations xy=π^n with n>1 are admitted, so regularity
of the total space is not accidentally required. A projective-line target fails
hnoRational (identity map), as it should. No characteristic restriction or excellence
hypothesis is added. No statement correction or STATEMENT-DISPUTED issue was found.

Searches (performed with the prescribed msearch.py wrapper, results retained in
searches.jsonl):

- LeanFinder: “A map from the generic fibre of a projective nodal curve over a discrete
  valuation ring extends to a projective target without rational curves”: eight hits,
  on Weierstrass reduction and valuative criteria; none states this result.
- Loogle: `"AlgebraicGeometry", "Nodal"`: zero hits.
- Mathlib grep: `[Nn]odal|[Ss]emistable|[Rr]ational.*[Cc]urve` in AlgebraicGeometry:
  one unrelated elliptic-curve point hit.
- LeanSearch: “A morphism from the generic fibre of a projective nodal curve to a
  projective scheme without rational curves extends over a discrete valuation ring”:
  eight valuative-criterion hits; none is the nodal-curve extension statement.
- Project rg in both WeilConjectures and Sheaf for NodalTrait/nodalTrait,
  nodal trait, reducedGraph/graphClosure, noRational and graph closure found related
  geometry and `exists_projective_generic_hom_closure`, not this trait theorem.
  The latter concerns a Hom representing scheme over a normal integral base and
  does not assert that this generic graph projection is an isomorphism.
- Exact node-id search in WeilConjectures found no declaration. Candidate helper
  names `genericGraph` and `graphClosureIdeal` had no existing hit; the module
  specializes existing pullback and vanishing-ideal constructions without adding
  an independent notion or a duplicate definition of graph closure in general.

Source check: opened the publisher PDF
https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf, printed p.609,
Lemma 3.13 and §§3.9--3.12, and read the latest blueprint direct-images statement
and proof. The PDF's contraction argument motivates the already accepted node's
explicit no-rational-maps variant; this delivery preserves that node verbatim.

## Second reading by Q131

This is a second self-reading, not an independent agent review: the dispatcher
explicitly prohibits starting other agents and assigns independent review to the
maintainer. Reopened the node and the final signature, checked every binder and
conjunct against the audit above, and checked the graph map's two projections.
The initial compile exposed a misplaced association in the graph commutativity
proof and ambiguous coercion of `pullback f t` to its point type. Replaced the
former by a three-step calculation and made the latter `↥(pullback f t)` explicit.
The purity check also confirmed that topological dimension one would be insufficient;
the final signature uses the existing IsPureDimension predicate and cites its landed
node. No mathematical hypothesis or conclusion changed. Independent maintainer
review remains required.

Validation: scompile.py compiled both the sandbox view and the named library module
without errors or warnings. The wrapper's displayed sandbox elapsed time includes
slot acquisition and privately compiling landed imports; the per-file 60-second
limit was unchanged. The named library module took 3.5 seconds.
