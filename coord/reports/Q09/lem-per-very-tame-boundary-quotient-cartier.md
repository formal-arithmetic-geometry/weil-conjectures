## Worker report

This delivery states `AlgebraicGeometry.veryTame_boundary_quotient_cartier` in
`Sheaf.AlgebraicGeometry.VeryTameBoundaryQuotientCartier`. Its sole theorem has
proof `sorry`; every helper definition has real data. The second module,
`Sheaf.AlgebraicGeometry.EffectiveQCartierWeilDivisor`, supplies the missing
scheme-wide finite Weil divisor and effective Q-Cartier definitions.

I read the assigned node and all five original statement dependencies, their
recorded declarations and docstrings, ILO VIII 5.3.5 and 5.3.8 (printed
pp.124–125), and the current blueprint ancestor's Step 3. The original statement,
proof and proof dependencies are preserved. The statement dependencies gain the
new definition and the already landed quotient, normal crossings and modification
nodes whose notions occur in the assigned statement.

Hypothesis and clause correspondence:

- A Noetherian regular scheme is `{X : Scheme.{u}} [IsNoetherian X]`
  and `hX : IsRegularScheme X`. The latter is exactly the recorded conjunction
  of local Noetherianity and regularity of all stalks. No integrality,
  nonemptiness, separation, excellence, or finite-dimensionality is imposed.
- A finite group action is `{G : Type v} [Group G] [Finite G]`
  and `a : G →* Aut X`. The group universe is independent of the scheme universe.
- The finite quotient and admissibility are `hq : IsAdmissibleFiniteSchemeQuotient a q`.
  This is the existing orbit-topology/invariant-structure-sheaf quotient, including
  finite morphism and orbit-containing affine opens. Since q is finite and invariant,
  the inverse images of affine opens of Y give exactly an invariant affine covering
  of X as required in the statement.
- Both boundaries are the actual ideal sheaves `B Bbar : X.IdealSheafData`, with
  `hB` and `hBbar : IsStrictNormalCrossingsBoundary ...`. Their support containment
  is `hsub : B.support ≤ Bbar.support`. Since both ideals are radical this is also
  the specified inclusion of reduced closed subschemes.
- Their invariance is `hBinv` and `hBbarinv`, equalities of their pullbacks by
  every action automorphism with the original ideal. This preserves their schemes,
  including their given reduced structures.
- Tameness and very tameness are `hvery : IsVeryTameDivisorialAction
  Bbar.support.compl a`. This existing predicate includes invertibility of every
  geometric inertia order, triviality of the characteristic monoid action, and
  triviality on the strict-local stratum. Thus the separately mentioned tame
  condition is included. The log structure is the canonical divisorial structure
  on the complement of Bbar, as in that predicate; strict normal crossings on a
  regular scheme supplies its fs charts. No independent arbitrary log structure
  or extra chart hypothesis is substituted. The original fs-log module is imported.
- The first conclusion is `∃ E : Y.WeilDivisor, E.IsEffectiveQCartier ∧
  Scheme.WeilDivisor.support E = q '' (B.support : Set X)`. Thus D is the support
  of an effective Weil divisor with one positive global multiple represented by
  an effective Cartier ideal. The definition retains actual coefficients through
  normalized local orders, rather than only the zero set of an equation.
- The pointed etale local equation is the second conjunct, `∀ y`, an etale
  `e : W ⟶ Y`, a point `w` over y, and `c : Γ(W, ⊤)` in `nonZeroDivisors`, with
  `W.zeroLocus {c} = e ⁻¹' (q '' B.support)`. An affine pointed neighbourhood
  is allowed as W, so requiring a single global equation on the chosen W
  is exactly the local condition.
- `quotientBoundaryIdeal q B` is the vanishing ideal of the closed image, using
  the closure operation to define it without assuming finiteness in the helper.
  In the theorem q is finite, so this closure is exactly q(B). The corresponding
  helper for Bbar describes q(Bbar).
- An arbitrary birational modification is quantified as `∀ Y' h,
  SchemeModification h → IsRegularScheme Y' → ...`. The recorded modification
  notion is proper and an isomorphism over schematically dense opens in both
  schemes, which is the birational modification in the node. In particular extra
  source components over a closed subset are excluded by source density.
- Reduced inverse images are `((quotientBoundaryIdeal q B).comap h).radical`
  and its Bbar counterpart. The ambient normal-crossings hypothesis and the
  subboundary normal-crossings conclusion use the already recorded
  `IdealSheafData.IsNormalCrossingsDivisor`, with its reduced parameter-subproduct
  equations on pointed etale charts.
- The union-of-components clause is a finite set S of actual irreducible components
  of the ambient reduced closed subscheme. The support of the smaller reduced
  closed subscheme equals the union of their images under the actual closed immersion.
  Finiteness follows since h is proper over the Noetherian quotient.
- The last implication in the modification conjunct gives
  `IsStrictNormalCrossingsBoundary` for the subboundary whenever it holds for the
  ambient boundary, preserving the node's distinction between normal and strict
  normal crossings.
- The last paragraph quantifies over every actual geometric point `t` of X.
  `boundaryInertiaOrder a t` is the cardinal of its geometric stabilizer, and
  `boundaryInvariantRing a t` is the intersection of equalizers of the existing
  `automorphismStrictLocalMap` with identity. Thus its data is exactly A^H.
- Having adjoined the Nth roots of unity is expressed by a primitive Nth root in
  that fixed ring (`∃ ζ, IsPrimitiveRoot ζ N`). In this tame strictly local setting
  this is the usual roots-of-unity condition; roots lift from the separably closed
  residue field and are fixed by inertia.
- `boundaryStrictLocalIdeal B t = Ideal.span {b}` and `b ∈ nonZeroDivisors A`
  make b a genuine equation of B in the geometric stalk. The helper is generated
  by germs in the kernels of the canonical restrictions to the etale pullbacks
  of B, so it is the actual extended ideal.
- The units `χ g hg` lie in A^H and satisfy χ^N=1 and the displayed eigen-equation.
  These equations give precisely an H-character: cancellation of the non-zero-divisor
  b and the actual action law give its multiplicative law. The proof-dependent
  indexing is only the presentation of elements of the geometric stabilizer.
- `c : boundaryInvariantRing a t`, `c.val = b^N` asserts invariance of b^N.
  Its `nonZeroDivisors` condition is the Cartier condition on Spec(A^H).
  The equality of radicals with the contraction of the actual boundary ideal
  says its support is the image of B in that invariant local quotient. This is
  the closed-image description used in the node's strict-local paragraph.

Dependency interfaces used:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsNoetherian` and
  `AlgebraicGeometry.IsLocallyNoetherian` (the original pqf dependency).
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: the recorded fs-log framework;
  its structural geometric-stalk constructions come from `LogRegularPair`.
- `Sheaf.AlgebraicGeometry.VeryTameDivisorialAction`:
  `AlgebraicGeometry.IsVeryTameDivisorialAction`,
  `AlgebraicGeometry.automorphismStrictLocalMap`; its public `LogRegularPair`
  supplies `strictLocalRing` and `strictLocalGerm`.
- `Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient`:
  `AlgebraicGeometry.IsAdmissibleFiniteSchemeQuotient`.
- `Sheaf.AlgebraicGeometry.NormalCrossingsDivisor`:
  `AlgebraicGeometry.Scheme.IdealSheafData.IsNormalCrossingsDivisor`.
- `Sheaf.TraceFormula.Modification`: `AlgebraicGeometry.SchemeModification`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `Scheme.IdealSheafData.IsInvertible`, the recorded effective Cartier ideal predicate.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.RingTheory.Length`: `Module.length`, the recorded module-length definition.
- `Mathlib.RingTheory.OrderOfVanishing.Basic`: `Ring.ord`, literally the length
  of the quotient by the principal ideal. Equality is in ℕ∞ to retain finiteness.
- The new node supplies `Scheme.WeilPrime`, `Scheme.WeilDivisor`,
  `Scheme.WeilDivisor.support`, `Scheme.IdealSheafData.HasEffectiveWeilDivisor`,
  and `Scheme.WeilDivisor.IsEffectiveQCartier`.

Every recorded proof-dependency module, and the recorded Mathlib proof leaves,
is imported privately unless already public for the statement. The following
proof dependencies have no recorded module yet, so there is none to import:
`lem-per-admissible-quotient-affine-integral-charts`,
`lem-per-finite-quotient-strict-local-invariants`,
`lem-per-regular-boundary-divisorial-chart`,
`lem-per-very-tame-equivariant-sharp-chart`,
`lem-per-weil-divisor-strict-local-cartier-test`,
`lem-sfb-etale-stalk-invariants`, and
`lem-trf-normal-domain-principal-divisor-kernel`.
They are proof inputs, with no missing object needed to state this theorem.
The module's docstring follows all eight proof steps and names these inputs.

Edge cases checked: empty X and its quotient (no geometric points, E=0);
empty B (E=0, b=c=1 and an empty component selection); B=Bbar; empty intersections;
trivial inertia (N=1); nonfaithful actions; disconnected regular schemes; and
positive characteristic dividing |G| but not any geometric inertia order.
The statement uses no invertibility assumption on |G|. Independent group and
scheme universes and every variable are explicitly bound. The quotient, reduced
inverse images, local boundary ideal and invariant subring are real constructions.
The sign action on A² with B a coordinate axis confirms why the reduced image
need not itself be Cartier: its Weil multiple is retained in the definition.

Searches: `msearch.py leanfinder` for the very tame boundary image gave eight
unrelated normalization/invariant-ring/class-group hits; `loogle` for
`AlgebraicGeometry.WeilDivisor, IsCartier, IsNormalCrossings` gave zero hits
(unknown first identifier); `grep` of Mathlib AlgebraicGeometry for
`WeilDivisor|QCartier|IsNormalCrossings|IsBirational` gave zero hits.
For the new definition, `leansearch` on normal Noetherian scheme Weil/Q-Cartier
divisors returned normalization and Weierstrass results; `leanfinder` on finite
codimension-one sums and locally principal multiples returned Dedekind-domain
support and affine denominator results, with no scheme divisor interface.
`rg` of `lean/WeilConjectures` and `lean/Sheaf`, the prescribed item-id grep,
DAG text search, and `tools/blueprint_refs.py search 'Weil divisor'` found only
curve, affine ring, and algebraic-space notions. The new node retains the raw
msearch summaries in `mathlib_searches`. No duplicate of the assigned theorem
or of these scheme definitions was found.

Validation: both modules were compiled individually, in dependency order, by
`scompile.py` against the live published build. No errors or warnings remain.
No statement correction or disputed statement was needed.

## New nodes

`def-per-effective-q-cartier-weil-divisor` supplies finite Weil divisors on a
scheme, support, the relation to an effective Cartier ideal through local lengths,
and the positive-global-multiple definition of effective Q-Cartier. The source is
Stacks 0BE2/02RJ/01WR and ILO VIII 5.3.8. On a normal Noetherian scheme this is the
node's usual finite integral combination of integral codimension-one closed
subschemes, indexed canonically by their generic points. The general definitions
have genuine Finsupp/set/predicate data and impose finite local lengths; they use
the existing Cartier ideal and dimension definitions. The searches above found
no scheme-wide existing notion: the affine and space interfaces have different
carriers, and the curve definition excludes the higher-dimensional input here.
The new definition is directly cited in the item's statement dependencies.

## Second reading by Q09

I reopened the node and both completed modules for a second self-review. The
assigned dispatcher forbids starting another agent and reserves independent
review to the maintainer; this section records the additional self-review.
I checked each clause against the correspondence above. The checks corrected
the closed-image helper to pass a `Closeds` value to `vanishingIdeal`, qualified
the Finsupp support in the Weil support definition, kept the character values
inside the actual invariant ring, and expressed the order equality in ℕ∞ so an
infinite length cannot silently truncate to zero. Both actual ideal sheaves
remain reduced by the existing SNC predicate, and the modification clause
keeps both normal crossings and the conditional strict assertion. All theorem
proofs are `sorry`; no postponed lemma or existence choice was inserted into data.

The first dry run requested the current schema field `import_flags`; the new
node now includes the standard empty list. The local Stacks tag index also
corrected the effective Cartier reference to 01WR.
