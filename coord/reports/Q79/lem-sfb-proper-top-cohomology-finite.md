## Worker report

The module states Tag 0EX4 without changing the accepted DAG statement or split.
Its only theorem has a `sorry` proof; no definitions or helper axioms are added.
The source was read at limits.tex, lemma-proper-top-cohomology-finite-type,
including all four proof paragraphs. Its conclusion's O_X is the already-recorded
source typo: the module lies on Y.

Hypothesis and clause correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`; morphism: `(h : X ⟶ Y)`.
- Properness: `[IsProper h]`, the recorded Mathlib class. Universal closedness
  implies quasi-compactness, so its locally finite-type clause is finite type.
- A nonnegative integer d: `(d : ℕ)` includes exactly those integers.
- Every scheme-theoretic fibre has dimension at most d: `hd : ∀ y : Y,
  topologicalKrullDim (h.fiber y) ≤ (d : WithBot ℕ∞)`.
- H is an O_X-module: `(H : X.Modules)`.
- H is quasi-coherent and finite type: `hH : H.IsQuasiCoherentFiniteType`.
  The dependency's actual definition is the conjunction of Mathlib's
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`.
- R^d h_*H is the object of `.rightDerived d` of the recorded
  `RingedSpace.moduleDirectImage h.toLRSHom.toShHom`, applied to H, exactly the
  ordinary higher direct image in pqf-def-cohomology.
- The conclusion applies `Scheme.Modules.IsQuasiCoherentFiniteType` to that
  object, simultaneously asserting quasi-coherence and finite type on Y.
- No Noetherian, flatness or finite-presentation assumptions are introduced.

Recorded statement dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: AlgebraicGeometry.IsProper.
- Mathlib.AlgebraicGeometry.Fiber: AlgebraicGeometry.Scheme.Hom.fiber.
- Mathlib.Topology.KrullDimension: topologicalKrullDim.
- Sheaf.AlgebraicGeometry.CoherentFiniteType:
  AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType.
- WeilConjectures.AlgebraicGeometry.PQFCohomology:
  AlgebraicGeometry.sheafCohomologyAndHigherDirectImages. Its right-hand side
  explicitly uses RingedSpace.moduleDirectImage.rightDerived; that functor's
  real construction and its moduleGrothendieckAbelian instance were also read.

All already-stated proof dependency modules are imported without `public`,
including Mathlib matches. The following proof dependencies have no recorded
Lean declaration yet, so are omitted from imports (they are not needed to type
the statement): lem-sfb-proper-quasicoherent-fibre-dimension-vanishing, lem-sfb-top-degree-base-change.

Edge cases checked: d = 0 asserts finite type of ordinary proper pushforward
for zero-dimensional fibres; an empty fibre has dimension bottom, hence satisfies
the bound; empty X gives zero output; empty Y forces empty X and the assertion is
vacuous locally; the zero module is allowed; no nonemptiness, positive degree,
Noetherian base, flatness, finite presentation or field is assumed. The universe
u is explicit and arbitrary and matches the recorded scheme/module interfaces.

Searches for an existing declaration:

- msearch.py leanfinder: "For a proper scheme morphism with fibres of dimension
  at most d the dth higher direct image of a finite type quasi coherent module
  is finite type". Eight hits: properness, finite morphisms, and fibre finiteness;
  none states this theorem.
- msearch.py loogle: `"higherDirectImage", "IsFiniteType"`: zero hits.
- msearch.py grep: `higherDirectImage.*[Ff]inite|[Ff]inite.*higherDirectImage`,
  Mathlib/AlgebraicGeometry: zero hits.
- rg of WeilConjectures and Sheaf for proper/top cohomology, finite type of
  higherDirectImage and this node id: no same statement. The source's
  isFinitePresentation_higherDirectImage has a Noetherian base and finitely
  presented coefficient; the top-coherent-cohomology modules concern schemes
  over a field, so neither covers this node. The exact item-id search is empty.

No statement dispute, correction, new node or dependency repair is needed.

Validation: scompile.py compiled the exact module as both a sandbox file and its
library module, with no errors or unexpected warnings. deliver2.py --no-push
returned OK: the complete packet passes the server preflight and compiles.

## Second reading by Q79

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
