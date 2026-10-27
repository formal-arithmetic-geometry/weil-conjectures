## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedFibrePointQuasiFiniteCriterion` states
`AlgebraicGeometry.Scheme.Hom.isQuasiFiniteAtPoint_of_closed_fibre_no_other_generalization`.
Its proof is `sorry`; no definition or proof has been added. The declaration's docstring
contains all five steps of the accepted DAG proof with their dependency identifiers.

Hypothesis and clause correspondence:

- Schemes Y and T and their morphism g are `{Y T : AlgebraicGeometry.Scheme.{u}}`
  and `(g : Y ⟶ T)`. The universe `u` is explicit and arbitrary.
- Locally of finite type is `[LocallyOfFiniteType g]`. No quasi-compactness,
  separatedness, or Noetherian hypothesis on the schemes is imposed.
- The chosen point is `(y : Y)`, and t is substituted everywhere by the term `g y`.
- The scheme-theoretic fibre Y_t is `g.fiber (g y)`; the given point as a fibre point
  is the existing canonical `g.asFiber y`. Its definition is
  `(g.fiberHomeo (g y)).symm ⟨y, rfl⟩`. Thus the node's specified identification
  with the inverse image of {t} is used, with no arbitrary lift or extra hypothesis.
- Closedness of {y} in Y_t is
  `(hclosed : IsClosed ({g.asFiber y} : Set (g.fiber (g y))))`.
- The quantifier over every fibre point is `∀ y' : g.fiber (g y)`.
  Membership of y in the closure of {y'} is
  `g.asFiber y ∈ closure ({y'} : Set (g.fiber (g y)))`.
  The explicit set type ensures closure is taken in the fibre, not in Y.
  Its consequence `y' = g.asFiber y` is exactly the node's equality of points under
  the canonical homeomorphism. The direction of specialization has been checked.
- The conclusion is `g.IsQuasiFiniteAtPoint y`, the recorded Stacks predicate,
  including finite type of the affine witness map. It is not replaced by the
  more general Mathlib stalk predicate `g.QuasiFiniteAt y`.

Recorded statement dependency declarations, with source signatures and docstrings read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom` (schemes as locally ringed spaces, their morphisms).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, whose field says every eligible affine
  pair has a finite-type section-ring map.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`,
  `fiberι`, `fiberToSpecResidueField`, `fiberHomeo`, and `asFiber`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint`, the existential affine-pair
  definition using a finite-type algebra instance and `Algebra.IsQuasiFiniteAtPrime`.

All statement dependencies are public imports. The stated proof dependencies have
plain imports: `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`
(`PrimeSpectrum.preimageHomeomorphFiber`),
`Sheaf.AlgebraicGeometry.FiniteTypeNoetherianSpectrum`
(`AlgebraicGeometry.noetherianSpace_primeSpectrum_of_finiteType`),
`Mathlib.Topology.Constructible` (`Topology.IsConstructible`),
`Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet`
(`PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible`), and
`WeilConjectures.RingTheory.QuasiFiniteAtPrime` (`Algebra.IsQuasiFiniteAtPrime`).
The affine spectrum is already public through the scheme statement dependency.
The two fibre rings in the proof are related by tensor-factor symmetry; the Lean
statement itself uses the scheme fibre and hence makes no additional ring choice.

Edge cases checked before writing:

- If Y is empty (including an empty affine zero-ring scheme), no y can be supplied;
  the universal statement is vacuous, as in the node. A map from nonempty Y to
  empty T cannot exist. No nonemptiness assumptions are added.
- For an identity morphism each fibre has one point and both hypotheses hold.
- Nonreduced, zero-dimensional finite-type fibres are allowed: the statement only
  constrains their topology, not nilpotents.
- A closed point on the affine line over a field is not isolated: the generic point
  specializes to it and violates `hgeneralization`. Thus the second hypothesis is
  substantive and its specialization direction is correct.
- The generic point of that affine line has no proper generalization but fails
  `hclosed`. Closedness has not been accidentally dropped.
- Arbitrary base characteristic and non-Noetherian base schemes are included.
  There is no finite-type (as opposed to locally finite-type) assumption on g.

Searches for an exact existing statement (2026-10-24):

- `msearch.py ... leanfinder "A locally finite type morphism is quasi finite at a
  closed fibre point with no other generalization in its fibre"`: eight hits,
  including `LocallyQuasiFinite`, `LocallyOfFiniteType`, the fibre Jacobson
  instance, and `isClosed_singleton_iff_locallyOfFiniteType`; no exact statement.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt"`: twelve hits.
  In particular `quasiFiniteAt_iff_isOpen_singleton_asFiber` assumes isolation;
  it does not derive it from the two hypotheses of this node.
- `msearch.py ... grep "QuasiFiniteAt|isOpen_singleton|StableUnderGeneralization"
  AlgebraicGeometry/Morphisms/QuasiFinite.lean`: five hits concerning the stalk
  predicate and its affine restriction, no exact criterion.
- `msearch.py ... leansearch "A closed point of a scheme fibre with no proper
  generalization is quasi finite for a locally finite type morphism"`: eight
  hits on quasi-finiteness and closed points; no exact statement.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for quasi-finite predicates,
  closed fibre criteria, and generalization/specialization: the existing affine
  isolation theorem, comparison predicate theorem, and related criteria were
  found and inspected; none has this statement. In particular the project
  comparison theorem still requires an isolated point.
- `grep -rn` for the exact item identifier in `lean/WeilConjectures`: no match.
- The proposed full declaration name was searched in both project trees and was absent.

Source checked: `literature/stacks-project/morphisms.tex`,
`lemma-quasi-finite-at-point-characterize` (Tag 01TH), its statement and proof.
Its (3) to (1) implication agrees with the node. There is no statement dispute,
no node correction, no new node, and no dependency interface repair.

## Validation

Compilation and delivery preflight results are recorded below after running the wrappers.
The maintainer performs the independent delivery review, as specified in the worker brief.

- `scompile.py Q77 lem-sfb-closed-fibre-point-quasifinite-criterion <module>` passed
  both sandbox (3.8 s) and library (2.5 s) checks with no warnings or errors.
- `deliver2.py Q77 lem-sfb-closed-fibre-point-quasifinite-criterion --no-push`
  returned `OK (dry run)`: the preflight and compilation passed.
- Local record comparison confirmed that only `lean` changed, the signature is
  verbatim, every Lean line is at most 100 characters, and the sole proof is `sorry`.

## Second reading by Q77

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
