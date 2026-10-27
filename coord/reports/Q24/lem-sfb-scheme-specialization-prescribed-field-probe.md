## Worker report

The module `Sheaf.AlgebraicGeometry.SpecializationPrescribedFieldProbe` states
`AlgebraicGeometry.Scheme.exists_valuationSubring_of_specializes_fieldPoint` with
one postponed theorem proof (`sorry`). It introduces no definitions. The source
is Stacks Project, Tag 01J8, parts (1)-(2), read in `schemes.tex` at
`lemma-points-specialize`, together with the prescribed field-point morphism;
the domination input is Tag 00IA. The four steps of the node's proof are included
in the declaration docstring.

Clause-by-clause correspondence:

- The scheme is `{Y : Scheme.{u}}`; the field is `{K : Type u} [Field K]`.
  The common universe is the universe of the category of schemes and of its
  affine spectra; it places no finiteness or cardinal bound on the field.
- The specified scheme morphism is `(u : Spec (CommRingCat.of K) ⟶ Y)`.
  Mathlib's `Scheme.Hom` is a morphism of the underlying locally ringed spaces.
- The unique point of `Spec K` is `IsLocalRing.closedPoint K`: its ideal is
  the maximal ideal, which in a field is zero. Thus `u (IsLocalRing.closedPoint K)`
  is exactly the point called y-prime in the node, with no extra point chosen.
- The specialized point is `(y : Y)`. The hypothesis
  `(h : u (IsLocalRing.closedPoint K) ⤳ y)` has exactly the requested direction:
  `specializes_iff_mem_closure` identifies it with membership of y in the
  closure of the singleton consisting of the image of the unique point.
- The conclusion quantifies `∃ (A : ValuationSubring K)`: this is an actual
  subring of the same K satisfying the element-or-inverse condition.
  Mathlib supplies `ValuationRing A` and `IsFractionRing A K` instances for
  every such A (ValuationSubring.lean, including the instance at line 153).
  Consequently no additional fraction-field witness or hypothesis is needed.
- The morphism is `(v : Spec (CommRingCat.of A) ⟶ Y)`.
  `v (IsLocalRing.closedPoint A) = y` says that its closed point, defined
  by the maximal ideal of A, maps to y.
- `Spec.map (CommRingCat.ofHom A.subtype) ≫ v = u` is equality of scheme
  morphisms on Spec K. `A.subtype : A →+* K` is precisely the inclusion.
  This preserves the prescribed field map, rather than merely its underlying
  image point.

Dependencies used, with signatures and docstrings read from the source:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-field`: Mathlib's `Field` in `Mathlib.Algebra.Field.Defs`, reexported
  by the public imports.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `def-trf-valuation-ring`: `ValuationRing` and its fraction-field
  characterization `ValuationRing.TFAE` in
  `Mathlib.RingTheory.Valuation.ValuationRing`. The statement uses the standard
  bundled `ValuationSubring K` from the public import
  `Mathlib.RingTheory.Valuation.ValuationSubring`; its canonical instances give
  exactly that notion with the specified embedding and fraction field.
- Proof-only imports are `Mathlib.RingTheory.Localization.AtPrime.Basic`
  (`Localization.AtPrime`, the recorded declaration for
  `def-weil-pbc-localization-at-prime`) and
  `Mathlib.RingTheory.Valuation.LocalSubring`
  (`LocalSubring.exists_le_valuationSubring`, the recorded declaration for
  `lemma-nagata-local-domain-valuation-dominates`).

Edge cases checked before writing: an empty Y admits no given u from the
nonempty spectrum of a field, so the implication has no missing empty case.
For y equal to y-prime, the trivial valuation (the whole field) is permitted.
The statement permits nonreduced and nonseparated Y, every characteristic,
and arbitrary algebraic or transcendental extensions encoded by the given u.
It imposes no Noetherian, separated, finite-type, or algebraic-closure condition.
A valuation subring may have arbitrary rank; its closed point remains unique.
The fraction-field property follows from the bundled valuation-subring
condition, including the zero element, so there is no extra conclusion hidden
by omitting a redundant explicit `IsFractionRing` conjunct.

Duplicate searches (all performed for this item):

- LeanFinder: "A field valued point of a scheme extends over a valuation
  subring of the same field centered at any specialization of its image".
  Eight hits, chiefly `ValuativeCriterion.Existence.specializingMap`, the
  converse, and `ValuativeCommSq` projections. No exact statement.
- LeanSearch: "Given Spec K to Y and a specialization of its image, there
  exists a valuation subring of K and a map Spec A to Y extending the
  prescribed morphism". Eight hits, including
  `IsLocalRing.exists_factor_valuationRing`; that is the local-ring input,
  not the scheme statement. The valuative-criterion hits require different
  hypotheses; the commutative-square projections do not assert existence.
- Loogle: `"ValuationSubring", "Specializes"`: no hits.
- Mathlib grep: `exists.*[Vv]aluation|of_specializes` in AlgebraicGeometry:
  one hit in ValuativeCriterion.lean, in the proof of the specializing-map
  theorem. Its full statement and construction were read; it is not a match.
- Project searches in both `lean/WeilConjectures` and `lean/Sheaf` for the
  node id, valuation-subring/specialization names, and the proposed name.
  `Scheme.exists_valuationSubring_of_specializes` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.ValuativeCriterion` fixes the
  algebraic closure of the residue field and its canonical field morphism.
  Its full docstring and signature were read: it does not state the result
  for the prescribed K and u. Other hits only use that special case.
  There is no occurrence of this node id in upstream Lean and no collision
  for the new theorem name or module.

No new nodes, dependency repairs, statement corrections, or disputed statements.
Only the item's `lean` record changes. Its `statement` is the verbatim theorem
signature. The file compiles cleanly through scompile.py on the server
(sandbox 1.6 seconds; library path 1.4 seconds).

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
