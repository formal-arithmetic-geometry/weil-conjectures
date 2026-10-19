## Worker report

The module `Sheaf.AlgebraicGeometry.GabberEquivariantLogModification` states
`AlgebraicGeometry.exists_gabber_equivariant_log_modification` with proof `sorry`. It also
provides three public helper predicates belonging to this statement:
`IsFreeInvariantOpen` records invariance and freeness on all algebraically closed geometric
points; `IsLargestFreeInvariantOpen` adds density and maximality by inclusion; and
`IsAffineLocallyHProjective` expands the node's projectivity convention to every affine target
open using `IsHProjective (f ∣_ W)`. These are real `Prop` definitions with no postponed data.

The theorem renders the hypotheses as follows. `[IsIntegral C]`, `[IsNoetherian C]`, and
`[C.IsSeparated]` are the integral, Noetherian, and separated hypotheses. `hExcellent` says
that the coordinate ring of every affine open is `IsExcellent`, which is the recorded
excellent-scheme convention. `B : TopologicalSpace.Closeds C`, `U : C.Opens`, `hBU`, and
`hU` state that `U` is the dense complement of the nowhere-dense closed boundary `B`.
`hlog` is exactly `IsDivisorialFineSaturatedLogRegularPair C U.toScheme U.ι hU`.
`G`, `[Group G]`, `[Finite G]`, and `a : G →* Aut C` give the finite group action;
`horder` makes the group order invertible in every geometric residue stalk, and `hboundary`
expresses preservation of the pair. `V` and `hV : IsLargestFreeInvariantOpen a V` state that
`V` is the dense largest invariant free open, and `T` with `hT` identifies the non-free locus
with its closed complement.

The conclusion existentially supplies an integral Noetherian scheme `C1`, an action
`a1 : G →* Aut C1`, a morphism `f : C1 ⟶ C`, and a dense open `C0`. `Dense C0` and
`IsIso (pullback.snd f C0.ι)` render the dense-open full-preimage isomorphism. The equation
`(a1 g).hom ≫ f = f ≫ (a g).hom` is equivariance. `IsAffineLocallyHProjective f` renders
projectivity over each affine open of `C`. The universal density clause quantifies every dense
open `W` and asserts density of `f ⁻¹ᵁ W`. The final existential supplies the closed boundary
`B1`, its dense complement `U1`, and `hU1`; the first equality is exactly
`B1 = f⁻¹(B ∪ T)`. The second identifies `U1` with its complement. The displayed
`@IsDivisorialFineSaturatedLogRegularPair` gives the required log regular pair, while the next
conjunct states that `a1` preserves it and `IsVeryTameDivisorialAction U1 a1` renders the
very-tame geometric-stalk conditions.

Dependencies used:

- `AlgebraicGeometry.IsIntegral` from `Mathlib.AlgebraicGeometry.Properties`.
- `AlgebraicGeometry.IsNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`.
- `AlgebraicGeometry.IsDivisorialFineSaturatedLogRegularPair` and its divisorial stalk
  constructions from `Sheaf.AlgebraicGeometry.LogRegularPair`, the declaration recorded for
  `def-trf-log-regular-pair`.
- `IsExcellent` from `Sheaf.RingTheory.ExcellentRing`, recorded for
  `def-exc-excellent-ring`.
- `AlgebraicGeometry.IsHProjective` from
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, recorded for `def-kun-projective`.
- `AlgebraicGeometry.IsVeryTameDivisorialAction` and its canonical strict-local map from
  `Sheaf.AlgebraicGeometry.VeryTameDivisorialAction`, recorded for
  `def-per-very-tame-divisorial-action`.
- `CategoryTheory.Limits.pullback` and `pullback.snd` from Mathlib, recorded for
  `def-pc-fibre-product`; `IsClosedImmersion` is supplied by the projective convention.

Edge cases checked before writing: the trivial finite group has the whole scheme as its free
open and empty non-free boundary; an empty original boundary gives `U = ⊤`; dimension-zero
integral schemes are allowed; residue characteristic zero makes the order-unit condition
automatic; and the universal density clause includes `W = ⊤`. The projectivity predicate also
quantifies empty affine opens, whose restriction is covered by the finite-projective-space
convention. No positive-dimensional, nontrivial-group, or nonempty-boundary assumption was
introduced.

Searches made:

- `msearch.py ... leanfinder "Gabber equivariant very tame projective modification of an
  integral excellent separated Noetherian log regular scheme with finite group action"`:
  ordinary `Proj`, normalization, and properness declarations only; no match.
- `msearch.py ... loogle "IsHProjective IsVeryTameDivisorialAction
  IsDivisorialFineSaturatedLogRegularPair"`: zero hits; the service reported `IsHProjective`
  unknown, so the exact declarations above were checked in their recorded modules instead.
- `msearch.py ... grep "gabber.*equivariant.*modification|IsLargestFreeInvariantOpen|
  IsAffineLocallyHProjective" AlgebraicGeometry`: zero hits.
- `rg` over `WeilConjectures/` found no declaration of this theorem or the two helper predicates;
  `rg` over project `lean/Sheaf` found only the distinct relative Gabber log-smooth theorem and
  the already recorded very-tame action definition.
- The shared DAG search found the existing `def-per-very-tame-divisorial-action` node and its
  recorded declaration, so no duplicate action definition was added.

The stage-1 split and Q24 review are unchanged. There is no `STATEMENT-DISPUTED` flag and no
node correction or dependency repair.

## Second reading by Q126

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
