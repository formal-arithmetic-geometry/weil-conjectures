## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.UnramifiedMapNonconstant` states
`AlgebraicGeometry.unramified_curve_map_nonconstant`, with one `sorry` proof.
It introduces no definitions. The original statement and dependencies are unchanged.

Hypothesis and conclusion correspondence:

- A field k: `{k : Type u} [Field k]`, with explicit universe `u`.
- Curves X and Y over k: `{X Y : Scheme.{u}}`, structure morphisms
  `(pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))`, and
  `[IsIntegralCurve pX] [IsIntegralCurve pY]`. The recorded class extends
  `IsVariety`, which includes integrality, separatedness, local finite type and
  quasi-compactness. Its remaining field is `topologicalKrullDim X = 1`.
  Local finite type plus quasi-compactness is finite type. The existing dimension
  comparison identifies this with the local-ring dimension convention.
- A k-morphism h: `(h : X ⟶ Y) (h_over : h ≫ pY = pX)`.
- If h is unramified: the antecedent `IsUnramified h` of the first conjunct.
- Its image contains at least two points: `∃ x₁ x₂ : X, h x₁ ≠ h x₂`.
  Choosing preimages is equivalent to two distinct points in the image.
- Every nonempty open subscheme V: `∀ V : X.Opens, Nonempty V → ...`.
  This quantifies over all opens, with no affine or quasi-compact restriction.
- If the restricted map is unramified: `IsUnramified (V.ι ≫ h) → ...`.
- V is again a curve over k: `IsIntegralCurve (V.ι ≫ pX)`.
- The restricted image has at least two points:
  `∃ v₁ v₂ : V.toScheme, (V.ι ≫ h) v₁ ≠ (V.ι ≫ h) v₂`.
- The last sentence of the node is respected: no smoothness, normality, perfectness,
  algebraic closedness, or rational-point assumption is present. In particular the
  second conjunct does not assume that h is globally unramified.

Statement dependencies used, with signatures and bodies read:

- `def-pc-curve`: `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`,
  `AlgebraicGeometry.IsVariety` and `AlgebraicGeometry.IsIntegralCurve`.
- `def-weil-unramified-morphism`: `Sheaf.AlgebraicGeometry.UnramifiedMorphism`,
  `AlgebraicGeometry.IsUnramified`. Its body is exactly
  `LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)`.

Both modules are public imports. All recorded proof prerequisites are imported
as plain imports: Mathlib Properties, Pullbacks, Morphisms.Proper, Noetherian,
Morphisms.FiniteType, Morphisms.QuasiCompact, Topology.KrullDimension, and the
project modules `WeilConjectures.AlgebraicGeometry.Dimension`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`WeilConjectures.AlgebraicGeometry.UnramifiedFibrePointIsolated`.
These provide, respectively, integrality, open fibre products, separatedness,
Noetherianity and quasi-compact open immersions, finite-type composition/base change,
dimension, nonempty-open dimension invariance, and isolated fibre points. No
proof import is omitted for a cycle. The theorem docstring gives all four DAG
proof steps with their dependency ids; stage 2 leaves the proof postponed.

Sources read locally: Stacks `curves.tex`, `lemma-generically-etale` (Tag 0C1C),
including the omitted nonconstancy step before `lemma-flat` (Tag 0CCK), and
`morphisms.tex`, `lemma-unramified-over-field` (Tag 02G7), especially part (2).
The latter gives discrete fibres without smoothness or normality and justifies
the stronger generality explicitly required by this supporting DAG node.

Edge cases checked: empty X and Y are excluded by integrality and dimension one;
the empty open V is excluded precisely by `Nonempty V`; V = top is included.
Identity maps and nonempty open immersions fit. A constant map to a closed point
or to a generic point cannot satisfy the unramified antecedent: its whole source
would be a discrete irreducible fibre and hence a singleton of dimension zero.
The argument also works for singular integral curves and imperfect fields. No
positive-characteristic case is dropped: Frobenius is not presumed unramified.
Non-affine opens are included; finite type follows from Noetherianity as in the
node's proof. The explicit common scheme/field universe follows the recorded
curve interface and places no bound on the choice of universe.

Searches on 2026-10-24:

- `msearch.py`, LeanFinder: "An unramified morphism between integral curves has at
  least two points in its image, including on every nonempty open subset".
  Eight hits, including `AlgebraicGeometry.FormallyUnramified`,
  `Algebra.isOpen_unramifiedLocus`, the multiplicativity and ring-hom-property
  instances, and `AlgebraicGeometry.formallyUnramified_iff`; none states this node.
- `msearch.py`, Loogle:
  `AlgebraicGeometry.FormallyUnramified, AlgebraicGeometry.IsIntegral`: zero hits.
- `msearch.py`, LeanSearch: "An unramified morphism of integral curves over a field
  has nonsingleton image". Eight hits on formal unramifiedness, integral morphisms,
  and algebraic unramifiedness; no curve nonconstancy statement.
- `msearch.py`, grep in Mathlib/AlgebraicGeometry:
  `(unramified|Unramified).*(nonconstant|Nonconstant|image|range)|(nonconstant|Nonconstant).*(unramified|Unramified)`:
  zero hits.
- `rg` in project `lean/WeilConjectures` and `lean/Sheaf`:
  `(unramified|Unramified).*(nonconstant|Nonconstant|nonsingleton)|(nonconstant|Nonconstant).*(unramified|Unramified)`:
  zero hits. Broader curve/nonconstant searches located flatness and function-field
  results, but none states this unramified two-clause result.
- `rg` for the node id in `lean/WeilConjectures`: zero hits.
- Exact proposed declaration-name search in Mathlib, both project trees and
  `dag/lean_names_upstream.json`: zero hits.

Validation: `scompile.py Q28 lem-a1-unramified-curve-map-nonconstant <file>` passed
both sandbox and library module compilations (8.4 s and 7.2 s), with no errors or
unexpected warnings. Auto-bound implicits are disabled. No node fault or
STATEMENT-DISPUTED issue was found.

## Second reading by Q28

A second pass was performed by this worker with the node and finished file open;
the dispatcher explicitly forbids starting another agent. The independent
maintainer review remains the delivery review.

The first conjunct has its own unramified antecedent and uses two unequal images,
not merely unequal source points. The second independently quantifies over every
nonempty open, uses the actual composite `V.ι ≫ h`, and concludes both the
recorded curve predicate on `V.ι ≫ pX` and unequal restricted images. Both
`IsIntegralCurve` binders and the equality over k are present; there is no
extra smoothness, normality or perfection binder. The full signatures and bodies
of the two recorded dependencies were read, so neither predicate was replaced.
The proof docstring was checked against all four steps, including the global
finite-type check for non-affine opens and the generic singleton-image case.
No mismatch was found and no statement correction was needed. The node's JSON
signature was extracted verbatim from the file. No new nodes or dependency repairs.
