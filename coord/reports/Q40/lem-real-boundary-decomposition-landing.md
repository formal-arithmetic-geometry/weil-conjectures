## Worker report

The module `Sheaf.Paper.RealBoundaryDecompositionLanding` states
`RealSheaves.exists_boundary_decomposition_landing`, with its proof wholly `sorry`.
No definition is added and no theorem is proved. The node is unchanged except for `lean`.
The source read was main-20261015, sec-purity-real-sheaves/sk-d-real-boundary/d-real-boundary.md,
the decomposition homomorphism clause. The entire seven-step DAG proof is in the docstring.

Hypotheses and objects, in the order of the node:

- The finite field, its algebraic closure, and the chapter's coefficient choices are `D : Setup`.
  The curve over this field is `C₀` with its `Over` instance and `hC : D.IsCurve C₀`.
  This retains nonemptiness, separatedness, smoothness, finite type, pure dimension one,
  and connected geometric base change exactly through the recorded predicate.
- The open immersion is `U₀.ι`, for `U₀ : C₀.Opens`. Every open immersion identifies its
  source with such an open subscheme. `hU` is its nonemptiness; `hS` says its set-theoretic
  complement is finite; `s` and `hs` choose a point of that complement. No closed-point
  assumption is added: closedness follows from the curve and complement hypotheses.
- The stalk is `C₀.presheaf.stalk s`; its residue field is `C₀.residueField s`.
  `hH : Algebra.IsHenselizationAtPrime' ...` uses the recorded universal-property predicate
  at the maximal ideal of this local stalk. Localization at the maximal ideal of a local
  ring is canonically the ring itself. The two algebra structures and their scalar tower
  require the structural map on the stalk to be the composite of that localization and
  the henselization map, rather than an unrelated map.
- `H`, `K`, `[IsDomain H]`, and `[IsFractionRing H K]` present the henselization and its
  fraction field. Domainhood is part of presenting the fraction field of this curve's
  henselization, not a replacement for the curve assumptions. The stalk-to-K algebra
  and scalar tower specify its canonical composite. `Ω` is the chosen algebraic closure
  of K: `[IsAlgClosed Ω]` and `[Algebra.IsAlgebraic K Ω]` are exactly the two fields of
  Mathlib's `IsAlgClosure`, by `isAlgClosure_iff`. Splitting this class allows the existing
  geometric-fibre API to infer separable closedness without assuming it separately.
- The integral closure `integralClosure H Ω`, its locality, local structural map and
  algebraically closed residue extension are the objects and properties supplied by
  `HenselianLocalRing.exists_residue_galois_action`. The chosen restriction `a` is
  characterized on EVERY integral element by `ha`. The residue closure `Ωr` is arbitrary
  (in independent universe w), with compatible identification `e` from that integral
  closure residue field. `r` is characterized on EVERY residue by `hr`, transported by e.
  Thus these binders select precisely the maps supplied by the recorded residue-action
  theorem; no arbitrary group homomorphism or arbitrary action replaces reduction.
  Its surjective residue map and e also make this characterization unique.
- The residue field of the ordinary henselization is canonically the residue field of
  the stalk; this follows from the henselization universal property, as in proof step 5.
  Consequently the `Ωr`-automorphism group over `ResidueField H` is precisely the stated
  G_s under that canonical identification. `Φ` with `hΦ` specifies geometric Frobenius:
  its INVERSE is x ↦ x^(Nat.card κ(s)). It therefore uses the correct residue cardinality,
  rather than the base-field cardinality. No finiteness assumption on κ(s) is added;
  its finiteness follows from the closed-point field theorem.
- `ξ : Spec K ⟶ U₀.toScheme` is the local generic map. `hξ` requires its composition
  into C₀ to be the map from the fraction field through the henselization and the stalk.
  This is a factorization of the canonical map, not an unconstrained morphism. Its
  geometric point is `Spec.map (algebraMap K Ω) ≫ ξ`, exactly the chosen local point.
- `D.geometricCurve U₀.toScheme` is U = U₀ × Spec k. `b` is its chosen geometric basepoint
  over a separably closed field `Ωu`. Its projection is the arithmetic basepoint.
  `γ` is a natural isomorphism of the two recorded finite-etale fibre functors.
  It is arbitrary: no compatibility of this path with a base-field path is imposed.
- `G₀` and `G` are small models of the arithmetic and geometric fundamental groups.
  `e₀` and `eG` identify them continuously and multiplicatively with the respective
  automorphism groups of the fibre functors. This is the explicit equivalence interface
  of `toAutContinuousMulEquiv`, avoiding an additional connectedness typeclass assumption
  merely to elaborate `IsFundamentalGroup`. It expresses the same model choice; it does
  not replace either fundamental group with an arbitrary group or omit the topology.

Clauses of the conclusion:

- `∃ θ : (Ω ≃ₐ[K] Ω) →* G₀` asserts the homomorphism, and `Continuous θ` its continuity
  from the existing Krull topology to the chosen profinite fundamental-group topology.
- The first universal conjunct, on EVERY finite etale cover P and fibre point z, says
  `(γ.inv ... ((e₀ (θ σ)).hom ... (γ.hom ... z))).left = Spec.map σ ≫ z.left`.
  Moving γ to the other side gives exactly γ a_σ γ⁻¹. Equality of the underlying
  scheme morphisms is equality of fibre points (`fiber_ext`). Naturality is built into
  `e₀ (θ σ) : Aut (fiber ...)`, and multiplication into `θ`. This also characterizes
  agreement with the functorial map of `lem-galois-pi1-functoriality`: its canonical
  pullback fibre isomorphism is projection, and its action is the same precomposition.
- `σ ∈ r.ker` is σ ∈ I_s. The next conjunct produces `g : G` whose action, transported
  through `pullbackFiberIso` for U → U₀, is the action of θ(σ) on EVERY fibre.
  This is exactly membership in the image of π₁(U) through U → U₀, characterized by
  the functoriality theorem's equation. It is not replaced by mere triviality on some
  selected covers, nor is geometric π₁ redefined as a kernel.
- `∃ n : ℤ, r σ = Φ ^ n` is membership in W(K_s). The final conjunct produces an
  integer m with `(e₀ (θ σ), Multiplicative.ofAdd m)` in the existing
  `MonoidHom.weilGroup (constantCoverAction ...) (geometricFrobenius ...)`.
  This is precisely the underlying fibre-product definition of the recorded scheme
  `weilGroup`; projection to its first coordinate gives the inverse image of integer
  Frobenius powers. Using that underlying definition avoids adding a redundant
  `GeometricallyConnected` assumption to make a typeclass elaborate. Geometric
  connectedness already follows from hC and hU. The node asserts only landing, so the
  conclusion does not add the more specific degree formula e_s n from its proof.

Dependency declarations used and read:

- `Sheaf.Paper.RealSheavesSetup`: `RealSheaves.Setup`, `.IsCurve`, `.geometricCurve`,
  `.localFrobenius` (the last's inverse-power convention is rendered by hΦ).
- `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`: `Algebra.IsHenselizationAtPrime'`.
- `Mathlib.Algebra.Algebra.Equiv`: `AlgEquiv.aut`, for the chosen-closure Galois groups.
- `Mathlib.CategoryTheory.NatIso`: natural isomorphisms and `Iso.app` for paths.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`: `fiber` and
  its geometric-point morphism description, imported publicly through Restriction.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality` and `.Restriction`:
  `pullback`, `pullbackFiberIso`, `fundamentalGroupMap` and `fundamentalGroupMap_smul`.
  The first two occur literally; the characterization in the latter renders image
  membership without introducing extra instances for connectedness.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup`: `constantCoverAction`,
  `geometricFrobenius`, `weilGroup`, and its fibre-product body `MonoidHom.weilGroup`.
- `Sheaf.RingTheory.HenselianResidueGaloisAction`:
  `HenselianLocalRing.exists_residue_galois_action`, with its full elementwise
  restriction/reduction formulas. Its data are selected with exactly those formulas.

Stated proof dependencies are imported, including ClosedPointField,
SmoothOverFieldRegularLocal, RegularNormalDecomposition, and the exact Weil-group
sequence (through WeilGroup). The Mathlib smooth, Noetherian, base-change and Frobenius
modules are supplied through these public imports and RealSheavesSetup. No proof import
cycle was introduced, and no declaration was copied into this module.

Edge cases checked before writing: an empty curve is excluded by IsCurve; an empty
open is excluded by hU; an empty complement has no s satisfying hs. No affine-open
hypothesis was imposed. A boundary point of degree greater than one uses the residue
cardinality in hΦ. The identity, inertia, zero Frobenius exponent and NEGATIVE integer
powers are covered (the indices are ℤ). The chosen path and compatible residue closure
remain arbitrary. The action's order was checked against contravariance of Spec:
precomposition yields the left action a_σ a_τ = a_(στ), not an opposite group.
Small models avoid equating the automorphism group's larger universe with the
scheme's universe, and the residue closure has its own independent universe.

Searches for an existing statement (2026-10-18):

- msearch leansearch: “local decomposition group homomorphism inertia geometric
  fundamental group Weil group curve”; 8 hits, including
  `Field.instGroupAbsoluteGaloisGroup`, valuation inertia and decomposition subgroups,
  and `InfiniteGalois.asProfiniteGaloisGroupFunctor`; none is this curve statement.
- msearch leanfinder: “decomposition homomorphism of a henselian local field into curve
  fundamental group maps inertia to geometric group and local Weil group to Weil group”;
  8 hits on valuation ramification, absolute Galois groups and inverse limits;
  no curve-local map with the two subgroup inclusions.
- msearch loogle: `AlgEquiv, MonoidHom, Continuous`; 3 hits on continuous Galois
  restriction and cyclotomic characters, none giving the statement.
- msearch grep: `decomposition.*[Hh]om|inertia.*fundamental|local.*[Ww]eil`;
  17 irrelevant algebra decomposition hits, no matching theorem.
- rg in the upstream WeilConjectures tree and side Sheaf tree for
  `boundary_decomposition_landing|decomposition.*[Ww]eil|inertia.*pi1` found only
  unrelated decomposition prose. Name-table boundary/decomposition hits were unrelated.
  grep for the exact node id in upstream WeilConjectures returned no hit.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED issue.
Validation uses only the prescribed scompile.py and deliver2.py wrappers.

## Second reading by Q40

Independent maintainer second reading of Q40's immutable delivery
63c02eefd051c98e381fdf02f565edf894daf023, performed on 2026-10-18.
This section records the present independent reader's work, not a second worker's
participation in the original delivery.

I read check-brief2.md in full, packet.md, the snapshot item and all eight statement
dependency nodes, the delivered module and its docstrings, and the worker report.
The primary source is main-20261015, sec-purity-real-sheaves/
sk-d-real-boundary/d-real-boundary.md, the paragraph beginning “Choose a geometric
point”. I also read d-real-setup.md, the recorded Weil-group and fibre-functor source
places, Stacks algebra.tex (henselization, finite-over-henselian, integral-transitive),
and pione.tex (fundamental-group theorem and Galois functoriality lemma).

Hypothesis-by-hypothesis and conclusion-by-conclusion reading:

1. `D : Setup.{u, v}` carries the finite field, algebraic closure and chapter coefficient
   choices. `C₀`, its `Over` instance and `hC : D.IsCurve C₀` retain the source's nonempty,
   separated, smooth, finite-type, pure dimension-one and geometrically connected curve.
   I read `Setup`, `Setup.IsCurve` and `Setup.geometricCurve` in RealSheavesSetup. Verdict:
   matches; no affine, proper or extra connectedness assumption was introduced.
2. `U₀ : C₀.Opens`, `hU`, `hS`, `s`, `hs` give precisely the nonempty open, finite complement
   and selected boundary point. An open subscheme is a valid presentation of the given
   open immersion. Closedness of s and finiteness of its residue field follow from this
   curve setup; they are not extra binders. Verdict: matches.
3. `H`, `hH` and the localization/stalk scalar tower present the ordinary henselization
   at the maximal ideal of the local stalk. I unfolded the recorded
   `Algebra.IsHenselizationAtPrime'`: its local-map universal property tests rings in
   `Type (max u v)`. Here both rings are in u, so no smaller test universe or hidden
   vacuity occurs. `K`, `IsFractionRing H K` and the stalk/H/K tower present the source's
   canonical fraction-field map. Domainhood is a consequence of the smooth curve's
   regular local ring and its henselization, not a restriction to a different class of
   curves. `ξ` and `hξ` specify its factorization through the open, rather than an
   arbitrary local map. Verdict: matches the source's chosen local generic point.
4. `Ω` is an arbitrary algebraic algebraically closed extension of K. The group
   `Ω ≃ₐ[K] Ω` is the recorded `AlgEquiv.aut` model of the chosen-closure Galois group;
   KrullTopology supplies its topology. The split `IsAlgClosed`/`IsAlgebraic` assumptions
   give the same algebraic-closure notion. Verdict: matches.
5. I read the full signature and docstring of
   `HenselianLocalRing.exists_residue_galois_action`. Its locality, local structural map
   and residue-algebraic-closure conclusions supply precisely the three integral-closure
   structure binders here. `ha` specifies restriction on EVERY integral element and `hr`
   specifies reduction on EVERY residue lift, transported through `e`. Surjectivity of
   the quotient map makes `hr` determine r uniquely. Thus no arbitrary homomorphism is
   substituted for reduction. `Ωr` has independent universe w and `e` implements the
   compatible choice. The henselization residue field is canonically κ(s): the universal
   property gives a local retraction to κ(s), inducing inverse field maps. Verdict:
   matches the stated residue group and inertia kernel.
6. `Φ` with `hΦ` is geometric Frobenius: its INVERSE raises to `Nat.card κ(s)`.
   The cardinality is the residue cardinality, not q. This covers non-rational s.
   Verdict: matches, with the correct sign.
7. `b` is the chosen geometric point on `D.geometricCurve U₀.toScheme`; its projection
   is the arithmetic base point. `γ` is exactly the recorded natural-isomorphism path,
   directed from the local fibre to that arithmetic fibre. No compatibility of the
   arbitrary path with a base-field path is imposed. Verdict: matches.
8. `G₀`, `G`, `e₀`, `eG` present the arithmetic and geometric automorphism groups as
   small topological group models. The equivalences retain their topology and group
   structure. I read `small_aut`, `toAutContinuousMulEquiv` and
   `exists_isFundamentalGroup`; these models are available in the fibre universe and
   do not identify u with the larger functor-category universe. Verdict: matches.
9. The conclusion `∃ θ : ... →* G₀, Continuous θ ∧ ...` gives the continuous homomorphism.
   Its first component equation says γ⁻¹ θ(σ) γ(z) = Spec(σ) ≫ z on the underlying
   scheme morphism, hence exactly θ(σ) = γ aσ γ⁻¹ on every cover. Fibre extensionality
   makes equality of `.left` equivalent to equality of fibre points. The multiplication
   order agrees with `AlgEquiv.aut` and contravariance of Spec. This is also the
   characterization of the induced map in `fundamentalGroupMap_smul`. Verdict: matches.
10. The inertia clause has `∀ σ ∈ r.ker, ∃ g : G, ∀ P z, ...`. The SAME g works for
    all covers and fibre points. The equation uses the actual pullback functor and
    `pullbackFiberIso`, which I read in Functoriality/Restriction; it is precisely
    membership in the image of π₁(U) in π₁(U₀). Verdict: matches, not merely separate
    liftability on each cover.
11. The Weil clause starts with `∃ n : ℤ, r σ = Φ ^ n`. Its conclusion supplies an
    integer m with `(e₀ (θ σ), ofAdd m)` in `MonoidHom.weilGroup` for the recorded
    `constantCoverAction` and `geometricFrobenius`. I unfolded both scheme-level and
    group-level Weil definitions. This is exactly inverse-image membership; using the
    body of the scheme abbreviation avoids an added `GeometricallyConnected` binder.
    The source's geometric connectedness follows from the curve hypotheses. The node
    asks for landing, not the proof's additional degree formula, so the absence of
    an explicit m = e_s n conjunct is correct. Verdict: matches.

I checked all seven proof-docstring steps against the node: curve/open hypotheses,
closed-point residue finiteness, naturality and multiplication of the local action,
Krull continuity, equivariant reduction, constant-cover Frobenius computation and the
geometric/Weil landing argument are present in order. In particular naturality with
constant-cover deck transformations justifies arbitrary paths, including for negative
Frobenius powers. The elementary residue-field identification is written out, rather
than assuming the chosen closure agrees literally with another model.

Edge cases: empty curves/opens are excluded by the SOURCE; empty complement yields no
s satisfying hs. Empty finite covers impose the appropriate vacuous pointwise formula.
Identity elements, zero exponent, negative integer exponents, inertia elements,
non-rational boundary points, arbitrary compatible residue closures and arbitrary paths
are retained. No characteristic-zero, affine-open or additional finiteness condition
has slipped in. All universes u, v, w are bound; autoImplicit is false. The standard
same-universe scheme/field models follow the recorded finite-etale API; independent
coefficient and residue-closure universes remain independent.

One-definition-per-notion: the worker recorded LeanSearch, LeanFinder, Loogle and grep
queries with their results. I independently searched the upstream fundamental-group
and Mathlib field-theory trees and the side Paper tree for decomposition/inertia/Weil
and the exact declaration name. The nearby DecompositionGroup and FrobeniusDecomposition
results concern integral-cover specialization and Frobenius lifts; they do not state
this henselian local map with both subgroup inclusions. The delivered theorem reuses
the recorded notions and adds no definition or private copy.

Mechanical checks: the delivery commit changes only its one module, node lean record
and report. The entire `lean.statement` equals the file signature VERBATIM, up to but
not including `:= by`. The node's statement and dependencies are unchanged. There is
one theorem, whose entire proof is `sorry`; there are no definitions, local proofs,
local instances or notation. Module and declaration docstrings name the source and
blueprint id, and every line is at most 100 characters. No pro-etale construction or
dropped route-pivot machinery is involved. Direct statement/proof citations have empty
intersection with origin/newtargets-dag:coord/route-pivot-dropped.txt; no item-specific
route-pivot repair note exists at that ref.

Compiler evidence: the original worker report mentions the wrappers but supplies no
per-file result. I reproduced the compile on the immutable snapshot with:

    python3 /home/ubuntu/weil-launcher-nt/scompile.py Q40 lem-real-boundary-decomposition-landing /home/ubuntu/weil-launcher-nt/reviews-stage2/Q40__lem-real-boundary-decomposition-landing__63c02eefd051/snapshot/lean/Sheaf/Paper/RealBoundaryDecompositionLanding.lean

Exit code 0, no errors or warnings. The installed prescribed wrapper is presently
server-overlay based (rather than the local launcher variant described in the brief).
It reported sandbox `Sheaf/Stage2/Sandbox0.lean` success, 24.0 s, with side modules in
`/dev/shm/nt-tmp/nt-local-compile-a5wj3ib6/.lbuild`, then library-path
`Sheaf/Paper/RealBoundaryDecompositionLanding.lean` success, 49.5 s. Each invocation
retained the default 60-second limit. No direct ssh, global build, project edit, live
Lean write, claim, merge or delivery command was run by this reader.

Finding and correction: H11, the delivered “Second reading” text explicitly said that
no reading had happened. This complete report preserves the Worker report and replaces
that placeholder with the present independent clause-by-clause review and compiler
evidence. There is no mathematical or Lean correction. No new helper, dependency repair
or §1(C) statement correction is needed. Verdict: FIX (report only).
