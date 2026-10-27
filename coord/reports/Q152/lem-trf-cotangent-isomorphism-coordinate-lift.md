## Worker report

Item: lem-trf-cotangent-isomorphism-coordinate-lift (Q152, stage 2).
Module: Sheaf.AlgebraicGeometry.CotangentIsomorphismCoordinateLift.

The unchanged node has two assertion clauses, recorded by two theorems:
`AlgebraicGeometry.Scheme.Hom.exists_compatible_etale_coordinates_of_cotangent_isomorphisms`
and
`AlgebraicGeometry.Scheme.Hom.exists_lift_of_etale_coordinates_of_cotangent_isomorphisms`.
Both proofs are exactly `by sorry`. There are no new definitions, dependency modules,
statement corrections or disputed statements. All original proof steps and dependencies
are preserved. The sole dependency-list additions are the already-landed
`def-pc-module-stalk-functor` and `def-a1-relative-differentials-pullback-map`, whose
canonical constructions are used explicitly.

The prior worker's stage-1 refusal is superseded by the stage-handoff paragraph of
coord/brief-stage2.md section 0: the accepted Q141 split is stage-2 input. The current
node had no lean record; coord/queue.tsv lists stage 2. No repair note was found.
The accepted natural-language statement and split are unchanged.

### Hypothesis and conclusion correspondence

- Field k: `(k : Type u) [Field k]`, with no characteristic restriction.
- Finite-type k-schemes X, M_1, M_2: `X M₁ M₂ : Scheme.{u}` with structural maps
  `p`, `q₁`, `q₂` to `Spec (.of k)`. Each has both `LocallyOfFiniteType` and
  `QuasiCompact`, the recorded finite-type convention. Smooth ambient schemes are
  `[Smooth q₁]` and `[Smooth q₂]`; no smoothness of X is assumed.
- Closed k-immersions: `i₁ : X ⟶ M₁`, `i₂ : X ⟶ M₂`, their
  `IsClosedImmersion` instances, and `hi₁ : i₁ ≫ q₁ = p`,
  `hi₂ : i₂ ≫ q₂ = p`. These equalities express being maps over k, without
  imposing additional geometric assumptions.
- Marked point: `(x : X)`; no closed-point or rationality condition.
- L = kappa(x): `X.residueField x`, definitionally the local-ring quotient
  `IsLocalRing.ResidueField (X.presheaf.stalk x)`.
- The two specified canonical maps: each `hαₐ` is `IsIso` of the map obtained from
  `qₐ.relativeDifferentialsPullbackMap iₐ` by `moduleStalkFunctor X.toRingedSpace x`
  and then `ModuleCat.extendScalars (X.residue x).hom`. This is exactly the
  canonical map on stalks tensored with L. The stalk of tensor pullback is
  `O_X,x ⊗[O_M,i(x)] Ω_M,i(x)`; extension to L cancels the intermediate tensor
  to give the source in the node. The target is Ω for `iₐ ≫ qₐ`, identified with
  Ω for p by hiₐ. No arbitrary linear isomorphism is substituted.
- Dimension d: the first theorem existentially binds `d : ℕ` and identifies it with
  `Module.finrank (X.residueField x)` of the residue extension of the stalk of
  `p.relativeDifferentials`. The second theorem identifies the supplied number n
  with that same dimension, as explained in Step 1 of the accepted proof.
- Affine neighbourhoods: `V₁`, `V₂`, `W` are opens of the original ambient schemes
  and X; their `IsAffineOpen` clauses and `x ∈ W` give the required neighbourhoods.
  `W = i₁ ⁻¹ᵁ V₁` and `W = i₂ ⁻¹ᵁ V₂` ensure the restricted X is the full
  closed inverse image in each restricted ambient scheme. Marked ambient-point
  membership follows from x in W. The inclusion witnesses `hW₁`, `hW₂` merely
  type the restrictions `iₐ.resLE`; the equalities ensure they add no assumptions.
- Etale k-charts: the existential `e₁`, `e₂` have codomain
  `AffineSpace (ULift.{u} (Fin d)) (Spec (.of k))`; `Etale e₁`, `Etale e₂` and
  the two equations with the affine-space structural projection say precisely
  that they are etale k-morphisms. ULift raises only the finite coordinate index
  to Mathlib's affine-space universe, changing no coordinate set.
- Agreement: `i₁.resLE ... ≫ e₁ = i₂.resLE ... ≫ e₂` is equality of actual scheme
  morphisms from W. It is not residue-field or underlying-point agreement.
- Any supplied chart near i_2(x): the second theorem binds an arbitrary dimension
  `n`, open `V₂`, membership `hx₂`, and map `e₂` with `[Etale e₂]` and its structural
  equation `he₂`. It imposes no affineness assumption on the supplied domain.
  It outputs an affine `V₂' ≤ V₂`; `M₂.homOfLE hV₂ ≫ e₂` is the restriction of
  exactly that supplied map, with its coordinates unchanged.
- Actual coordinate lifts: `g : Fin n → Γ(V₁.toScheme, ⊤)` is a family of sections,
  and the first map is exactly `AffineSpace.homOfVector (V₁.ι ≫ q₁)` applied to g.
  The final equality after `i₁.resLE` and `i₂.resLE` says that each g_j restricts
  on W to the corresponding supplied coordinate function. This is equivalent
  to the individual section equalities by `homOfVector_appTop_coord` and
  functoriality of `appTop`, without reducing the quotient ring.
- Differential basis of these same lifts: the existential `Module.Basis (Fin n)`
  has values explicitly equal to `1 ⊗ germ(d(g j))`. Its ambient scheme is the
  restricted first neighbourhood, its point is `⟨i₁ x, hx₁⟩`, and its structural
  map is `V₁.ι ≫ q₁`. Open restriction preserves the stalk; the closed immersion
  identifies this ambient residue field with kappa(x). Transport along those
  canonical identifications gives exactly the L-basis in the node. This uses
  the same fibre convention as lem-pur-etale-at-point-from-differentials.
- Etaleness after restriction: the second theorem explicitly asserts `Etale` of
  the map defined by g on the final affine neighbourhood V₁. The second map is
  the restriction of e₂ along an open immersion, so is etale by the recorded
  etale-composition instance; the first theorem states both Etale clauses directly.

### Dependencies and sources read

Read all ten original statement-dependency nodes, their lean or mathlib_match records,
and the signatures/docstrings of the declarations used. The interfaces used are:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth, .ClosedImmersion, .Etale:
  `AlgebraicGeometry.Smooth`, `AlgebraicGeometry.IsClosedImmersion`,
  `AlgebraicGeometry.Etale`.
- WeilConjectures.AlgebraicGeometry.Modules.Differentials:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsDerivation`,
  the affine and open-restriction identifications.
- Mathlib.RingTheory.Kaehler.Basic: `KaehlerDifferential`,
  `KaehlerDifferential.D`, `KaehlerDifferential.linearMapEquivDerivation`.
- Mathlib.AlgebraicGeometry.ResidueField: `Scheme.residueField`, `Scheme.residue`,
  and `Scheme.Hom.residueFieldMap`.
- Mathlib.LinearAlgebra.TensorProduct.Tower: `TensorProduct`, `LinearMap.baseChange`;
  Mathlib.Algebra.Category.ModuleCat.ChangeOfRings: `ModuleCat.extendScalars` is its
  bundled form. Tensor order is the recorded residue-field-on-the-left convention.
- Mathlib.AlgebraicGeometry.AffineSpace: `AffineSpace`, `AffineSpace.homOfVector`,
  `AffineSpace.coord`, `AffineSpace.homOfVector_appTop_coord`.
- WeilConjectures.Algebra.Homology.ModuleStalkFunctor:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`.
- Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap:
  `Scheme.Hom.relativeDifferentialsPullbackMap`, characterized on the actual
  `relativeDifferentialsPullbackGenerator` by its unique-existence theorem.

The already-stated proof dependencies are imported: EtaleLocalNormalForm,
EtaleAtPointFromDifferentials, the listed Mathlib modules, and OpenImmersion for
principal-localization open immersions. The proof-only dependency
lem-trf-etale-coordinate-derivations-jacobian has no lean record or mathlib_match yet;
it introduces no notion needed to state this item, and its proof dependency is retained.
Read morphisms.tex Tags 054L (affine etale smooth charts) and 02GU (differential
etale criterion), and algebra.tex Tag 0H93 (canonical etale differential base change).
The module docstrings spell out all six accepted proof steps.

### Searches

All service searches were made through the prescribed msearch.py and are recorded
in searches.jsonl. No exact existing declaration was found.

- LeanFinder: "Two closed immersions in smooth schemes inducing isomorphisms of
  cotangent fibres admit compatible etale coordinates by lifting coordinate functions".
  Eight hits, led by `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`
  and the ring-hom version, and standard-etale lifting statements. These supply smooth
  coordinates or standard-etale algebra lifts, not compatible charts for two closed
  immersions with the prescribed cotangent-fibre hypotheses.
- Loogle: "AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap,
  AlgebraicGeometry.AffineSpace.homOfVector". Zero hits; the guessed name
  relativeDifferentialsMap is unknown. Local source inspection found and reused
  the existing `relativeDifferentialsPullbackMap` instead.
- Mathlib grep: "cotangent.*isomorphism|compatible.*coordinates|coordinate.lift"
  under AlgebraicGeometry: zero hits.
- LeanSearch: "Closed immersions in smooth schemes with isomorphic cotangent fibres
  have compatible etale coordinates lifting a prescribed chart". Eight hits, all
  closed-immersion definitions/instances; none asserts the coordinate comparison.
- Local rg of WeilConjectures and Sheaf for cotangent isomorphisms, coordinateLift,
  coordinate_lift, compatible coordinates, and both proposed declaration names,
  plus the node id in WeilConjectures and the names in dag/lean_names_upstream.json:
  no exact match. Read MinimalSmoothEnvelopeComparison: its predicate uses the same
  canonical fibre map, but its comparison theorem assumes characteristic zero and
  concludes a common etale neighbourhood, not these coordinate-lift clauses.
  It is a downstream node, so is not imported or used as a prerequisite.
- Read SmoothClosedCoordinateLift and SmoothPairLocalCoordinates: their regular-equation
  or smooth-pair hypotheses and conclusions differ, so they are not existing matches.

### Edge cases and validation

Checked before writing and again against the final signatures:

- d=n=0: Fin 0 is empty, its basis says the differential fibre is zero, and homOfVector
  has the unique empty vector. Neither positivity nor nonempty coordinates are assumed.
- Nilpotents: X=Spec(k[t]/(t^2)) in A^1 twice at t=0 has the stipulated one-dimensional
  differential-fibre maps. Equality of the scheme morphisms records equality modulo
  t^2, not merely modulo t. No reducedness or smoothness of X is assumed.
- Non-closed and non-rational x: all fibres use residue fields at the actual point;
  no identification with k is assumed. Both closed immersions canonically identify
  their ambient residue fields with kappa(x).
- Arbitrary positive characteristic and imperfect k: no CharZero, algebraic-closure
  or perfectness binder. Only the smooth ambient hypotheses enter.
- Empty X has no marked point; statements quantify over x, so exclude no pointed case.
- Supplied charts on non-affine opens are allowed and are only restricted afterwards.
- All schemes use one arbitrary universe u, the usual scheme-over-k convention;
  ULift (Fin n) meets the affine-space index universe. autoImplicit is disabled.
- Compiled through scompile.py against the live build: the original API mismatch in
  Scheme.homOfLE was repaired to M₂.homOfLE. Subsequent sandbox and library-module
  compilation passed without diagnostics. Final import-list validation and delivery
  use the same wrapper through deliver2.py.

## Second reading by Q152

This is an explicit self-audit by the sole dispatched worker, not a claim of an
independent second agent; the brief forbids starting other agents and specifies
independent maintainer review after delivery. Reopened the node and complete module
and checked every binder and conclusion against the correspondence above. Confirmed
that the second theorem quantifies over the supplied map and retains it by restriction;
that g is used both in the basis formula and the actual etale map; that W is the full
inverse image for both closed immersions; and that the canonical maps are the recorded
ones rather than arbitrary maps with isomorphic source and target. Confirmed that the
basis's residue field is canonically L after restriction and closed immersion, and
that the two structural-map equations are precisely the k-morphism condition.
The only elaboration mismatch found was the explicit ambient scheme argument of
homOfLE; it was corrected and the module recompiled. No mathematical mismatch or
statement correction was found. The two direct proof-dependency imports for Kaehler
Basic and TensorProduct Tower were added in the final pass.
