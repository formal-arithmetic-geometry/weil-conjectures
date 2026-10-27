## Worker report

The module `Sheaf.AlgebraicGeometry.FibreComponentNoetherianAffineChart` states
`AlgebraicGeometry.exists_noetherian_affine_chart_of_fibre_component_genericPoint`.
Its only theorem has proof `sorry`; it introduces no definitions. The original
node is unchanged except for its `lean` record. There are no new nodes,
dependency repairs, statement corrections, or statement disputes.

Sources read: `literature/stacks-project/morphisms.tex`,
`lemma-finite-type-noetherian` (Tag 01T6, lines 2765 onward), and
`literature/stacks-project/algebra.tex`, `lemma-irreducible` (Tag 00ES,
lines 4665 onward). The former proves local Noetherianity over the residue field;
the latter identifies affine component generic points with minimal primes.
The docstring carries all four proof steps of the node, including the argument
with the closure of a point for minimality. No reducedness, integrality,
quasi-compactness, or Noetherianity of the base is assumed.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| Schemes X, S and a morphism f | `{X S : Scheme.{u}} (f : X ⟶ S)` |
| f locally of finite type | `[LocallyOfFiniteType f]` |
| t a point of S | `(t : S)` |
| T is the scheme-theoretic fibre X_t | `f.fiber t`, by Mathlib's pullback definition |
| C is an irreducible component of T | `(C : Set (f.fiber t)) (_hC : C ∈ irreducibleComponents (f.fiber t))` |
| y is a generic point of C | `(y : f.fiber t) (_hy : IsGenericPoint y C)` |
| T is locally Noetherian | The first conjunct `IsLocallyNoetherian (f.fiber t)` |
| There exists an affine open neighbourhood U of y | `∃ (U : (f.fiber t).Opens) (hU : IsAffineOpen U) (hyU : y ∈ U), ...` |
| A is the section ring O_T(U) | `Γ(f.fiber t, U)` throughout the conclusion |
| U is identified with Spec A | `hU.isoSpec : U.toScheme ≅ Spec Γ(f.fiber t, U)` is Mathlib's canonical identification, used definitionally by `hU.primeIdealOf` |
| A is Noetherian | `IsNoetherianRing Γ(f.fiber t, U)` |
| The prime p_y corresponds to y under that identification | `(hU.primeIdealOf ⟨y, hyU⟩).asIdeal`; `primeIdealOf` is defined to be `hU.isoSpec.hom` applied to that point |
| No prime is strictly contained in p_y | `∀ q : Ideal Γ(f.fiber t, U), q.IsPrime → q ≤ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal → q = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal` |

Every universe and variable is explicitly bound. The underscore-prefixed
hypothesis names are ordinary hypotheses, retained in the theorem's type.
The affineness witness already supplies the spectrum isomorphism, so no
additional isomorphism assumption or arbitrarily chosen point identification
is involved. `primeIdealOf` has codomain `PrimeSpectrum` and hence its ideal is
prime without adding a hypothesis.

Dependency declarations read and used, with their defining modules:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec` and `Spec.map`;
  the recorded declarations of def-pc-scheme and def-weil-affine-spectrum.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; the locally finite type clause of
  def-weil-finite-type-morphism. Its instance
  `AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange` is the match
  of the proof dependency lem-weil-pbc-lft-base-change.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`,
  `fiberι` and `fiberToSpecResidueField`; def-pc-scheme-fibre. The theorem uses
  the fibre itself; its projections explain the source proof.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, defined by maximal
  `IsIrreducible` subsets; the Mathlib match of def-weil-irreducible-components.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, defined by `closure {y} = C`;
  def-sc-generic-point. This also forces y to belong to C.
- `Mathlib.AlgebraicGeometry.Noetherian`:
  `AlgebraicGeometry.IsLocallyNoetherian`; pqf-def-locnoeth. Its all-affine-open
  formulation is equivalent to the node's cover formulation. The same module
  contains `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, the
  match of pqf-lem-locnoeth-lft, imported for the proof plan.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the self-module
  Noetherian condition, equivalently all ideals finitely generated;
  def-weil-pbc-noetherian-ring.
- `Mathlib.AlgebraicGeometry.AffineScheme`:
  `AlgebraicGeometry.IsAffineOpen.isoSpec` (lines 388 onward) and
  `AlgebraicGeometry.IsAffineOpen.primeIdealOf` (lines 775 onward) implement
  the affine-chart identification using the existing canonical construction.
- `Mathlib.RingTheory.Spectrum.Prime.Topology`: proof-only import for
  `PrimeSpectrum.closure_singleton` and
  `PrimeSpectrum.pointsEquivIrreducibleCloseds`, the matched declarations of
  lem-weil-pbc-spec-irreducible-closed-subsets-primes. Their signatures and
  the latter's docstring were read.

Edge cases checked mathematically before writing:

- Empty fibre: no irreducible component and generic point can be supplied;
  the stated implication is vacuous, without excluding empty schemes.
- A non-Noetherian base: the argument uses only the residue field at t.
- The nonreduced fibre Spec k[e]/(e²): its generic prime (e) is minimal;
  no reducedness assumption is present in the signature.
- The reducible fibre Spec k[x,y]/(xy): the generic primes (x) and (y) each
  satisfy the conclusion; the signature does not ask that the fibre be integral.
- An infinite disjoint union of finite type affine schemes over a field:
  local Noetherianity and the chart conclusion hold, although the fibre need
  not be quasi-compact. The theorem claims only local Noetherianity.
- The candidate smaller prime q = p_y is allowed and yields equality; the
  quantifier excludes precisely strict smaller primes, not equality.

Searches actually run through `batch2/msearch.py` for Q54 and this item:

1. LeanFinder: `For a locally finite type scheme morphism, the fibre is locally
   Noetherian and every generic point of an irreducible component has a
   Noetherian affine chart corresponding to a minimal prime`.
   Eight hits, including `LocallyOfFiniteType.isLocallyNoetherian`, the
   Jacobson-space fibre instance, `LocallyOfFiniteType`, `IsLocallyNoetherian`,
   `LocallyQuasiFinite`, the finite-fibre instance, `IsFinite.instLocallyOfFiniteType`
   and `IsNoetherian.toIsLocallyNoetherian`. None states the full result.
2. Loogle: `AlgebraicGeometry.IsAffineOpen.primeIdealOf, IsGenericPoint`.
   Zero hits.
3. Mathlib grep: `primeIdealOf.*minimal|[Ff]iber.*[Nn]oetherian|[Nn]oetherian.*[Ff]iber`
   in `AlgebraicGeometry`. Zero hits.
4. LeanSearch: `The fibre of a locally finite type scheme morphism is locally
   Noetherian, and its irreducible component generic points correspond to
   minimal primes in an affine open chart`.
   Eight hits, including the local Noetherianity theorem, `Scheme.Hom.fiber`,
   `IsLocallyNoetherian.mk`, `PrimeSpectrum.zeroLocus_minimalPrimes`, and the
   fibre/Jacobson and Noetherianity instances. None states the whole conjunction.
5. `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
   `primeIdealOf.*minimal|[Ff]iber.*[Nn]oetherian|[Nn]oetherian.*[Ff]iber|fibre_component_noetherian`.
   Found ingredients including
   `WeilConjectures.Mathlib.AlgebraicGeometry.Properties`:
   `IsAffineOpen.primeIdealOf_mem_minimalPrimes`, whose full signature and
   docstring were read: it gives minimality on an already supplied affine
   chart of an arbitrary scheme, without the fibre Noetherianity and chart
   existence conclusion. Also read
   `WeilConjectures.AlgebraicGeometry.RestrictedFibreLocallyNoetherian`:
   `isLocallyNoetherian_fibre_of_finite_presentation_restrict`, which gives
   local Noetherianity under a different restricted finite presentation
   hypothesis, with no component chart conclusion. Neither is an exact match.
6. `grep -rn 'lem-trf-fibre-component-noetherian-affine-chart' lean/WeilConjectures`:
   zero hits. Name checks for
   `exists_noetherian_affine_chart_of_fibre_component_genericPoint` in Mathlib,
   `lean/WeilConjectures` and `lean/Sheaf`: zero hits. Additional checks of
   `dag/lean_names_upstream.json` and both source trees for
   `fibre.component.noetherian|fiber_component_noetherian|fibreComponentNoetherian`:
   zero hits.

Validation: the prescribed `scompile.py Q54
lem-trf-fibre-component-noetherian-affine-chart <module>` compiled the sandbox
and library module cleanly (2.8 seconds and 2.6 seconds in the observed run).

## Second reading by Q54

This is the author's second reading, not an independent review; the dispatcher
brief reserves independent review for the maintainer and forbids starting agents.
I reopened the node and the completed module, comparing the type clause by clause.
The arbitrary scheme morphism and its sole local finite type condition match;
there is no accidental finite type or quasi-compactness hypothesis. The component
is a maximal irreducible subset through `irreducibleComponents`, and the supplied
generic point is related to that same C through `IsGenericPoint y C`. The first
conjunct is local Noetherianity of exactly `f.fiber t`. The existential witnesses
are an open of that fibre, an affineness proof and y's membership proof, with the
same section ring used in both Noetherianity and the ideal quantifier.
Reading the actual definition of `primeIdealOf` confirms that this is the prime
under `hU.isoSpec`, rather than an unrelated ring isomorphism. The final order
condition is q contained in p_y, and the conclusion q = p_y has the intended
orientation and excludes exactly strict containments. The isomorphism requested
in the prose is already supplied by the affine witness, not an omitted assertion.
No mismatch was found, and no statement change was needed. The proof remains
exactly `sorry` and the docstring includes all four DAG proof steps.
