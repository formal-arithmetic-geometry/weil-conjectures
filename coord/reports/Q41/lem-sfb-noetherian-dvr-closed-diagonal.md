## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianDvrClosedDiagonal` states
`AlgebraicGeometry.isClosedImmersion_diagonal_of_dvr_uniqueness`, with a single
`sorry` proof and the five-step DAG proof in its docstring. There are no definitions,
new nodes, dependency repairs, or statement corrections.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes and morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the conjunction
  in the recorded finite-type dependency.
- Noetherian base: `[IsLocallyNoetherian S] [CompactSpace S]`. Mathlib's
  `IsNoetherian` class extends precisely these two classes; neither separatedness
  nor affineness of S is added.
- Every DVR: `∀ (A : Type u) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]`. Mathlib's class is a local PID with nonzero
  maximal ideal, exactly the dependency definition. Fields are excluded by that
  definition, rather than an added condition.
- Its fraction field: `(K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]`.
  Every fraction-field algebra structure is tested, not just one selected model.
- The canonical map j is written directly as
  `Spec.map (CommRingCat.ofHom (algebraMap A K))`.
- The two maps are `(h₁ h₂ : Spec (CommRingCat.of A) ⟶ X)`.
- Equality over the base is `h₁ ≫ f = h₂ ≫ f`.
- Equality after generic restriction is the equality between the two composites
  of the displayed `Spec.map` with h₁ and h₂. These two assumptions imply
  `h₁ = h₂`; no existence of lifts is required.
- The conclusion is exactly `IsClosedImmersion (pullback.diagonal f)`, with
  Mathlib's actual diagonal into its chosen fibre product.

Dependencies read and used (all names below are fully qualified by
`AlgebraicGeometry` unless otherwise specified):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `Scheme` and `Scheme.Hom`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `QuasiCompact`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`, `IsLocallyNoetherian`.
- `def-sc-discrete-valuation-ring`: its `mathlib_match`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, `IsDiscreteValuationRing`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, its projections and lift.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `IsClosedImmersion`.
- Fraction fields use `IsFractionRing` from
  `Mathlib.RingTheory.Localization.FractionRing`.

The proof-only imports provide the stated DAG plan:
`Sheaf.AlgebraicGeometry.NoetherianImageBoundaryDvr` supplies
`exists_dvr_of_mem_closure_range_not_mem_range`;
`Mathlib.AlgebraicGeometry.Morphisms.Immersion` supplies diagonal immersion
and local finite type of immersions. The public Noetherian, FiniteType,
QuasiCompact and ClosedImmersion imports also supply finite-type base change,
Noetherian permanence, Noetherian opens and
`IsClosedImmersion.of_isPreimmersion`. Every other proof dependency is a Mathlib
match in these modules, so no dependency module is missing.

Edge cases checked before writing: X empty (uniqueness vacuous, empty diagonal
closed), S empty (X then empty), nonreduced schemes (no reducedness assumption),
fields as test rings (not DVRs under the definition), arbitrary characteristic,
and the affine line with doubled origin over a field (its distinct trait maps
agree generically, so the uniqueness hypothesis fails as required). No lift
existence, excellence, finite-type test-ring condition, or generic-image
restriction is imposed. Test rings and fraction fields use the scheme's
universe u, as in Mathlib's `ValuativeCommSq` and the recorded boundary-DVR
lemma. There is no independent lower universe that could make the hypothesis
vacuous; larger objects are handled by universe enlargement as usual.

Source read: local `literature/stacks-project/limits.tex`,
`lemma-Noetherian-dvr-valuative-separation` (Tag 0207), including the finite-type
Noetherian diagonal/boundary contradiction. Its (3) implies (1); the node asks
for the finite-type, globally Noetherian specialization, so the statement needs
no correction. The five proof steps follow the accepted DAG, using the boundary
selection lemma instead of repeating the local-domain DVR construction.

Searches for an existing statement (2026-10-24):

- `msearch.py leanfinder`: "A finite type morphism over a Noetherian scheme whose
  discrete valuation ring lifts are unique has closed immersion diagonal".
  Eight hits, including `IsSeparated.of_valuativeCriterion`,
  `IsSeparated.isClosedImmersion_diagonal`, and diagonal immersion. None has the
  DVR-only uniqueness hypothesis.
- `msearch.py loogle`: `AlgebraicGeometry.IsSeparated,
  AlgebraicGeometry.ValuativeCriterion.Uniqueness`. Three hits:
  `IsSeparated.valuativeCriterion`, `.of_valuativeCriterion`,
  `.eq_valuativeCriterion`. These test every valuation ring, not just DVRs.
- `msearch.py grep`: `dvr|discrete.*valuation|uniqueness.*[Ss]eparated`,
  subdirectory `AlgebraicGeometry`. Ten hits. `ValuativeCriterion.lean:29`
  explicitly lists the Noetherian DVR reduction as future work; other hits are
  unrelated elliptic-curve DVRs. Read the actual uniqueness definition and
  fraction-ring/test-universe binders in this file.
- `msearch.py leansearch`: "Uniqueness for discrete valuation ring diagrams
  implies closed diagonal over a Noetherian scheme". Eight hits on the general
  valuative criterion and DVRs being valuation rings, no exact statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the node ID,
  DVR uniqueness/separatedness and closed-diagonal names: no duplicate.
  `grep -rn` of the node ID in `lean/WeilConjectures`: no hit. The nearby
  `NoetherianDvrProperness` theorem requires existence as well as uniqueness
  and concludes properness; it is not this statement and is not imported.
- `rg` of `dag/lean_names_upstream.json`, Mathlib, WeilConjectures and Sheaf
  for `isClosedImmersion_diagonal_of_dvr_uniqueness`: no existing declaration.

## Second reading by Q41

The dispatcher explicitly forbids starting other agents; this is a second
in-thread reading, not a claimed independent review. The maintainer supplies
the independent review of this delivery.

Reopened the node and the written signature. The finite-type conjunction and
the two Noetherian base hypotheses are both present. The huniq binder ranges
over all DVRs and all their fraction-field structures, then both actual maps
to X, with the two equalities in the correct categorical composition order.
The two arrows after `Spec.map` use the same canonical ring inclusion. The
conclusion is closed immersion of the actual diagonal, not merely closed
range or a set-theoretic injectivity statement. No clause is missing and no
additional geometric hypothesis was found. The signature contains no `let`,
`show`, private notation or auto-bound variable. No mismatch required a change.
