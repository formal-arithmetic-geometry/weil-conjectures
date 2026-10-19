## Worker report

The module `Sheaf.TraceFormula.ValuationNodalPolarSection` states
`AlgebraicGeometry.exists_valuation_nodal_polar_section`, with its entire proof `sorry`.
Its only helper, `polarDivisorCanonicalSection`, constructs the canonical section of the
existing dual ideal module by applying `Scheme.Modules.homToΓHomObj` to the inclusion
`J.toModulesι`. This definition contains real data and no postponed proof. Both declarations
are listed in `lean.declarations` and have source/blueprint docstrings. The theorem docstring
contains all ten proof steps of the node, including the named dependency citations.

I read Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3, Proposition 4.4.6,
printed pp. 32--33. The PDF was downloaded into this item's scratchpad and its text read.
The paragraph starting “Let Z1,...,Zn be other irreducible components” constructs the Cartier
points, the divisor line bundle, the lifted section, and exact poles. The node supplies the
expanded argument removing any need for semistability away from Z. No statement correction
or statement dispute is needed. The node's source record remains unchanged; a local archival
copy in the shared literature directory is still outside this delivery's write scope.

The hypotheses and conclusions match as follows.

| Node clause | Lean rendering |
| --- | --- |
| Separably closed field K | `(K : Type u) [Field K] [IsSepClosed K]` |
| Valuation subring of K with fraction field K | `V : ValuationSubring K`; this is an actual subring of K satisfying the valuation alternative, and its fraction field is K. No arbitrary ring map or extra fraction-field hypothesis replaces the inclusion. |
| Finite prime chain | `[Finite (PrimeSpectrum V)]`; comparability is supplied by the valuation-ring property, so a separate chain assumption is unnecessary. |
| T = Spec V and closed point s | `f : Y ⟶ Spec (.of V)`, `s : Spec (.of V)`, and `hs : IsClosed {s}`. The spectrum of a valuation ring is local, hence this specifies its unique closed point, including the field case. |
| Normal Y | `hnormal : ∀ y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)`. This uses precisely the node's local-ring definition without assuming Y integral or connected. |
| Proper relative curve, flat and finitely presented | `[IsProper f] [Flat f] [LocallyOfFinitePresentation f]`; properness supplies quasi-compactness and quasi-separatedness, so together these give finite presentation. |
| Pure relative dimension one | `hpure : ∀ t, (f.fiber t).IsPureDimension 1`, using the existing pure-dimension definition. |
| Geometrically reduced fibres | `hred : ∀ t, GeometricallyReduced (f.fiberToSpecResidueField t)`. This includes every fibre and every algebraic closure. |
| Irreducible component Z of the closed fibre | A reduced scheme `Z` and closed immersion `z : Z ⟶ f.fiber s`, with `hZ : Set.range z ∈ irreducibleComponents (f.fiber s)`. This specifies the component with its reduced closed-subscheme structure. |
| Geometrically projective line | `hgeom` is a `Nonempty` isomorphism in the slice over `Spec (AlgebraicClosure κ(s))` between the actual base change of Z and `ProjectiveSpace (ULift (Fin 2))` over that field. Two homogeneous coordinates mean dimension one. |
| Nodal along Z | `hnodal` quantifies over algebraically closed geometric points of `Spec κ(s)` and points above `Set.range z`; at each nonsmooth such point its maximal-ideal-adic completed stalk is ring-isomorphic to `MvPowerSeries (Fin 2) Ω` modulo `(X 0 * X 1)`. |
| At most two transverse branches meeting other components | `hboundary` bounds by two the `encard` of the geometric intersection of the inverse image of Z with the union of all other irreducible components. Together with `hnodal` and the smooth geometric projective line Z, these are ordinary transverse double branches. No condition is placed on points outside Z. |
| Z is a projective line over κ(s) | The first conclusion is an isomorphism in `Over (Spec κ(s))` to that projective line, retaining its structure morphism. |
| All other components Z1,...,Zn | Existential `n : ℕ` and `Zi : Fin n → Set (f.fiber s)` with injectivity and range exactly the set of all components distinct from `Set.range z`. This neither omits components nor repeats one. |
| Horizontal divisors Pi isomorphic to T | Sections `σ i : Spec V ⟶ Y` with `σ i ≫ f = 𝟙 _`, each a closed immersion, with `(σ i).ker.IsInvertible`. Their images with their kernel ideals are effective Cartier divisors and each is isomorphic to T. The actual section determines horizontality over the generic point. |
| Pairwise disjoint in the relative smooth locus | The range of each `σ i` is contained in `f.smoothLocus`, and ranges for distinct indices are disjoint. |
| Special fibres are the indicated smooth rational points | `σ i s = f.fiberι s (p i)`; `p i` belongs to `Zi i`, lies outside Z, and every component containing it equals `Zi i`. It belongs to the smooth locus of the closed-fibre morphism, and that morphism's residue-field map at `p i` is an isomorphism. Over a one-point field spectrum, this last condition is exactly κ(s)-rationality. A section commutes with base change, so its closed fibre is this reduced point. |
| Positive multiplicity m and P = m sum Pi | `m : ℕ`, `0 < m`, and `J = (∏ i, (σ i).ker) ^ m`. Addition of effective Cartier divisors is multiplication of their ideals, and positive integer multiplication is ideal power. |
| Cartier means one non-zero-divisor locally | `J.IsInvertible` and each `(σ i).ker.IsInvertible` use the existing definition by regular principal ideals on affine neighbourhoods. The pole clause also explicitly supplies `t ∈ nonZeroDivisors Γ(Y,U)` and the equality of the ideal of Pi with `(t)`. |
| L = O_Y(P), the dual ideal, invertible | The section has the exact type `Γ(J.toModulesᵛ, ⊤)` and the conclusion includes `J.toModulesᵛ.IsInvertible`. There is no unspecified line bundle or construction chosen from an existence axiom. |
| a has nonzero values in one-dimensional fibres | `residueValue a (f.fiberι s (p i)) trivial ≠ 0` for every index; the next conjunct explicitly gives residue-fibre module rank one at each such point. |
| Pole order exactly m on the closed fibre | Near every `p i`, an affine neighbourhood U, a regular equation t for Pi, and a section q of the total ideal satisfy `J.toModulesι.app U q = t^m`. The germ of t on the closed fibre is a non-zero-divisor generating its maximal ideal. The functional corresponding to a, evaluated on q, has unit germ on the closed fibre. Thus its represented meromorphic function is exactly the fraction b/t^m with b a unit at this smooth curve point. This is the local-parameter meaning of exact pole order in the node, without replacing it by a bound on poles. |
| No poles outside P | For every x outside `J.support`, the final conjunct supplies an affine neighbourhood U and `b : Γ(Y,U)` such that the functional corresponding to a sends every ideal section q to `b * J.toModulesι(q)`. Thus the represented meromorphic function agrees with a regular function b near every point outside P. |
| Canonical e = 1 has zero divisor P | `polarDivisorCanonicalSection J` is the actual inclusion functional, i.e. multiplication by 1 on the ideal. The scheme-theoretic zero ideal of its corresponding section morphism equals J, using the existing `Hom.zeroLocus`. Equality of ideals records multiplicities, not only support. |
| n = 0 is permitted | `n : ℕ` is unrestricted; no `Nonempty (Fin n)` is imposed. The empty product is the unit ideal, so P = 0 and the dual is the structure module. All pointwise clauses then are empty; a = e = 1 is the witness described by proof step 3. |

The appended explanations of eta-modifications, schematic density, and normalization in the
node do not introduce an eta-modification or normalization into this particular assertion.
Consequently the theorem does not introduce unused modification data or strengthen the
hypotheses to integral Y. The normalization dependency's module is still imported as the
contract requests.

Dependency declarations were read from their recorded module sources (and, for the live
invertible-pullback comparison unavailable in the old checkout, via `scompile.py --source`).
The definitions actually used are:

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`; `Field` is Mathlib's field structure.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, with the recorded
  geometric-fibre specialization, and `Mathlib.AlgebraicGeometry.Fiber`'s canonical fibre maps.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `.Flat`, `.FinitePresentation`, `.Smooth`:
  `IsProper`, `Flat`, `LocallyOfFinitePresentation`, `smoothLocus` (from the same smooth API).
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber` supplies the inherited
  finite-presentation instances on the canonical fibre maps; no new hypothesis is needed.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed` together with
  `IsDomain` on each stalk, as the dependency's inline normal-ring record prescribes.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`;
  `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` via the component-dimension predicate.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace` and its canonical
  structure morphism, with `ULift (Fin 2)` for the correct universe and dimension.
- `Mathlib.RingTheory.AdicCompletion.Basic`/`.Algebra`: `AdicCompletion` and its ring structure;
  `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries` and `MvPowerSeries.X`.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`: the existing dual-ideal interpretation
  of `O_Y(P)` and `IdealSheafData.IsInvertible.isInvertible_dual_toModules`;
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: `Scheme.normalization` and
  `Scheme.fromNormalization`, read for the node's explanatory convention, not additional data.
- Added already-recorded statement dependencies `def-weil-pure-dimension`,
  `def-weil-pbc-module-residue-fiber`, and `def-pc-zero-scheme`, using respectively
  `Sheaf.AlgebraicGeometry.PureDimension` (`Scheme.IsPureDimension`),
  `WeilConjectures.AlgebraicGeometry.Modules.ResidueFiber` (`residueFiber`, `residueValue`),
  and `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus` (`Hom.zeroLocus`). These are
  existing nodes and notions, not new definition nodes or dependency repairs.
- `WeilConjectures.AlgebraicGeometry.Modules.HomObjSections`: `homToΓHomObj` and
  `ΓHomObjAddEquiv`, and `.PullbackFreeGenerator`: `homOfGlobalSection`, implement the actual
  section/functional correspondence and canonical section. The helper creates no alternate
  divisor or residue-fibre definition.

All recorded proof-dependency modules are imported non-publicly, except the smooth dependency
already publicly imported. Unstated proof prerequisites are retained in the DAG/docstring;
no new theorems pretending to prove their content are introduced by this delivery.

Edge cases checked: n = 0; valuation ring a field (generic point = closed point); valuation
rings of arbitrary non-Noetherian finite height; disconnected normal Y; multiple other
components; zero boundary, one boundary point, or two boundary points; singularities away
from Z with no nodality condition; positive characteristic and imperfect separably closed
residue fields. The same universe u is used for the scheme, residue fields and geometric test
fields, avoiding a vacuous lower-universe geometric hypothesis. The presence of the specified
projective-line component excludes an empty closed fibre, exactly as in the node. No extra
connectedness, smooth generic fibre, global semistability, or Noetherian hypothesis is imposed.

Searches actually run:

- `msearch.py leanfinder`, query “A global section with exact poles on horizontal Cartier
  divisors on a proper normal curve over a valuation ring”: 8 hits, about function fields,
  Weierstrass coordinate rings, RatFunc valuations and basic-open section equalities; none
  states the relative polar-section result.
- `msearch.py loogle`, query `AlgebraicGeometry.Scheme, IsValuationRing`: zero hits; the service
  reports the identifier `IsValuationRing` unknown. This was not treated as a service outage
  or as evidence that the valuation-ring notion is absent; the actual `ValuationSubring` API
  is reused.
- `msearch.py grep`, query `polar.*section|exact.*pole|Nodal` under Mathlib/AlgebraicGeometry:
  zero hits.
- `msearch.py leansearch`, query “On a proper curve over a valuation ring a global section of
  a Cartier divisor line bundle has exact prescribed poles”: 8 hits, including analytic
  `MeromorphicOn.divisor`, global-section evaluation, Tilde localization, and elliptic good
  reduction; none states this assertion. The returned types distinguish these unrelated
  results from the relative-curve construction.
- `rg` in upstream WeilConjectures and `dag/lean_names_upstream.json` for the exact node id:
  no match. Concept searches for valuation curves, polar sections and exact poles in upstream
  WeilConjectures and side `lean/Sheaf` found related valuation modules but no same statement.
- Searches for existing local pole, canonical-section, residue-value, and zero-scheme APIs
  found the existing Hom-object, residue-fibre and zero-locus modules used above.
  `tools/blueprint_refs.py search 'nodal polar'` returned zero blueprint nodes; the search for
  pure dimension confirmed that this is an existing notion, and its existing DAG node and
  module were reused. No new notion or node was created.

Validation: every compile used the prescribed `scompile.py` single-file wrapper. Elaboration
initially exposed a missing public finite-presentation instance for canonical fibres and
ambiguous category/type inference in geometric pullbacks; these were repaired by importing
the existing SmoothFiber API, explicitly specifying `Scheme.{u}`, and spelling out the
ring-map constructor. The local no-poles clause explicitly relates the actual section to
regular multiplication. Long-line warnings were repaired without disabling the linter.
The final delivery includes only the module, this node's lean record and added existing
statement-dependency ids, and this report. The natural statement and proof are unchanged.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
