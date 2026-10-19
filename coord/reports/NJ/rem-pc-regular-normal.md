## Worker report

This repairs the returned head `80c6a25c1472aa41749fa13bf4cdb3bcdf206cb3` by supplying
the missing stage-2 statement and the required stage-2 report. That immutable head is
a stage-1 split, with no Lean module or `lean` record. Its report describes that split
and says the shared DAG already contains the equivalent reviewed Q01 split. I read
its node and report from the immutable Git objects without running Git in the shared
checkout. The current main node retains the same statement and seven-step proof;
the extra search entry in the returned head is not replayed. This delivery starts
with the current main node and changes only `lean`.

The return's `--apply-fixes` diagnostic concerned an invalid review-fix report path
and explicitly reported "no module". This is a new, substantive stage-2 packet:
`lean/Sheaf/AlgebraicGeometry/RegularNormalDecomposition.lean`, the corresponding
node record, and this worker report. It is submitted with `deliver2.py`, which puts
the report at the permitted delivery path; it is not an unchanged stage-1 re-push
or an attempt to reuse the failed reviewer fix packet.

The module states
`AlgebraicGeometry.regular_normal_and_normal_decomposition`, with the whole proof
`sorry`. Its three conjuncts render the current node's three numbered assertions.
The module and theorem docstrings cite the blueprint and Stacks 0569, 02IT, 033M;
the theorem docstring carries all seven proof steps and their named dependencies.
No mathematical proof or new definition is supplied.

### Hypotheses and clauses

- The scheme is `(X : Scheme.{u})`, with arbitrary explicit universe `u`.
- The introductory definition of normality is written exactly as
  `∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)`.
  `IsIntegrallyClosed` refers to the fraction ring, so together with `IsDomain`
  this is integral closedness in the field of fractions, at every point.
- Clause (1): its antecedent is the recorded affine-open definition of regularity,
  `∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsRegularRing Γ(X, U)`.
  `IsRegularRing` already includes Noetherianity of the affine section ring. The
  consequent is precisely the stalkwise normal-domain formula above. There is no
  connectedness, nonemptiness, dimension or global Noetherian hypothesis here.
- Clause (2): `IsNoetherian X` is Mathlib's locally Noetherian plus `CompactSpace`
  class, so it expresses the stated locally Noetherian and quasi-compact condition.
  Its other antecedent is the same stalkwise normality formula.
- Finiteness of the decomposition is `∃ (n : ℕ) (U : Fin n → X.Opens), ...`.
  The opens are exactly the irreducible components, by
  `Set.range (fun i : Fin n ↦ (U i : Set X)) = irreducibleComponents X`.
  Thus the assertion covers every component and introduces no extra piece.
- Openness is encoded by `U i : X.Opens`; closedness is
  `∀ i : Fin n, IsClosed (U i : Set X)`. Pairwise disjointness is
  `∀ i j : Fin n, i ≠ j → Disjoint (U i) (U j)`.
  The cover is `(⨆ i : Fin n, U i) = ⊤`.
- Each component has its actual open subscheme structure `(U i).toScheme`.
  Its integrality is `IsIntegral (U i).toScheme`; its normality quantifies over
  every point `x : (U i).toScheme` with the same normal-domain stalk conjunction.
- The scheme disjoint-union conclusion is
  `Nonempty (IsColimit (Cofan.mk X (fun i : Fin n ↦ (U i).ι)))`.
  This asserts the coproduct universal property for the canonical open inclusions,
  with apex the original scheme. It therefore gives precisely the canonical
  coproduct isomorphism, rather than only a partition of the underlying space.
  `Nonempty` here packages a proof of a universal property; it does not choose
  arbitrary scheme or morphism data for a definition.
- Clause (3): the antecedents are again the exact affine regularity condition,
  `IsNoetherian X`, `Nonempty X`, and `PreconnectedSpace X`; the conclusion is
  `IrreducibleSpace X`. `PreconnectedSpace` is the convention in the node that
  permits the empty space, and the separate `Nonempty` is the node's explicit
  extra assumption. Mathlib's `ConnectedSpace` bundles these two conditions.

### Dependency declarations used

I read the statement and record or Mathlib match of every statement dependency,
then the recorded declarations and their docstrings in the supplied sources:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-pbc-normal-ring`:
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`,
  with Mathlib's `IsDomain` and the record's inline normal-domain conjunction.
- `def-weil-regular-scheme`: `Mathlib.RingTheory.RegularLocalRing.Defs`,
  `IsRegularRing` and `IsRegularLocalRing`. I use exactly the affine-open
  specialization explicitly recorded there, with no private regularity predicate.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; its existing
  `AlgebraicGeometry.IsNoetherian` class adds the required quasi-compactness.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`, including nonemptiness and domain section rings.
- `def-weil-irreducible-components`: its Mathlib match in
  `Mathlib.Topology.Irreducible`, `irreducibleComponents` (maximal nonempty
  irreducible subsets), together with `IrreducibleSpace`.

The open subschemes and their inclusions are Mathlib's `Scheme.Opens.toScheme`
and `Scheme.Opens.ι` in `Mathlib.AlgebraicGeometry.Restrict`. `Cofan.mk` and
`IsColimit` are the existing categorical universal-property interface.

Proof-only imports retain the already stated proof plan: the two recorded modules
`Sheaf.RingTheory.RegularRingNormal` (`IsRegularRing.isNormalRing`) and
`Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions`
(`reduced_normal_iff_integrallyClosed_totalFractions`), and the Mathlib modules
for finite minimal primes, scheme coproducts, affine integral spectra and function
fields, and morphism gluing. Affine stalk and point descriptions are already
available through `Mathlib.AlgebraicGeometry.AffineScheme`, imported by these
statement modules; localization of integrally closed domains is in the publicly
imported `IntegrallyClosed` module. Topological component and covering statements
are in `Irreducible`, and finite scheme components are in `Noetherian`.
No proof import is omitted for a known cycle. Adding this module to the already
landed citer's proof imports is maintainer bookkeeping, outside this delivery.

### Edge cases and reuse

I checked the empty scheme (equivalently the spectrum of the zero ring): affine
regularity and stalk normality are vacuous; clause (2) permits `n = 0`, with the
empty colimiting cofan; clause (3) cannot be applied without `Nonempty X`.
A field spectrum gives one component. A disjoint union of two normal integral
schemes satisfies clause (2) and fails the connectedness antecedent of clause (3).
The crossing of two affine lines fails stalk-domain normality at the crossing.
There is no dimension, field, characteristic, separateness or integrality
restriction on the original scheme. The only index type is the finite `Fin n`;
no independent universe is used to make a hypothesis vacuous.

`Sheaf.AlgebraicGeometry.NormalScheme.IsNormalScheme` was inspected: its actual
declaration is `AlgebraicGeometry.IsNormalScheme`, and it includes `IsIntegral X`
as well as normal stalks. Using it for the original scheme would wrongly exclude
the empty scheme and disconnected normal schemes. Thus this statement uses the
inline normality condition already specified by the item and its normal-ring
dependency; no second definition is introduced. The more specialized
`Etale.exists_clopen_normal_integral_components` requires an etale morphism to a
normal integral target and does not state this node.

### Searches made

- `msearch.py ... leanfinder`:
  "Regular schemes are normal and Noetherian normal schemes are finite disjoint
  unions of normal integral schemes" returned eight hits, including `IsIntegral`,
  `IsNoetherian`, `IsLocallyNoetherian`, normalization integrality/reducedness,
  and `finite_irreducibleComponents_of_isNoetherian`; no complete match.
- `msearch.py ... loogle`:
  `AlgebraicGeometry.IsRegular, AlgebraicGeometry.IsNormal` returned zero hits
  and the unknown identifier `AlgebraicGeometry.IsRegular`.
- `msearch.py ... leansearch`:
  "A Noetherian normal scheme is a finite disjoint union of normal integral
  schemes" returned eight hits on finite coproducts, Noetherianity and finiteness
  of components; none proves regular normality or the normal decomposition.
- `msearch.py ... grep`:
  `IsNormal|isNormal|irreducibleComponents` in `AlgebraicGeometry` returned 25
  hits on components and Noetherianity; the relevant sources were read.
- `rg` of the project's `lean/Sheaf` and the upstream `WeilConjectures` tree for
  normality, regularity and decomposition found the specialized normal predicate
  and etale component theorem discussed above. Upstream
  `WeilConjectures.AlgebraicGeometry.Regular` gives the connected consequence
  and a dimension-at-most-one integrally-closed-stalk theorem; neither states
  the combined item. Its `IsRegular` class is stalkwise and alone omits the local
  Noetherian hypothesis in this node's definition, so I retained the recorded
  affine-open formula. Searches for the exact blueprint id and the proposed
  declaration/module name found no existing complete declaration.

No new nodes, dependency repairs or statement correction are needed. In
particular, the current reviewed stage-1 statement already makes nonemptiness
explicit; this delivery does not alter it or revive the old disputed empty-space
consequence. No unresolved statement dispute remains.

## Validation

Every delivered Lean file is compiled separately with `scompile.py`. The final
delivery is checked with `deliver2.py --no-push` before `deliver2.py` pushes it.
The exact theorem signature before the proof delimiter `:=` is recorded verbatim
in `lean.statement`, following the preflight signature reader. The first dry run
identified the extraneous trailing delimiter in the record; it was removed.
All variables and the universe are explicit, the sole theorem has proof `sorry`,
and all Lean lines are at most 100 characters. The direct `scompile.py` check passed cleanly for both the sandbox probe
and the module (5.5 s and 7.8 s respectively), with no errors or warnings. The maintainer's independent statement review remains the
review gate; no second worker or subagent was started.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
