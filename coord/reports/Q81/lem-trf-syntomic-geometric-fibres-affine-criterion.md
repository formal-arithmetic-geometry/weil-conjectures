## Worker report

The module `Sheaf.TraceFormula.SyntomicGeometricFibresAffineCriterion` states the
three-way affine criterion.  `IsLocalCompleteIntersectionOver` renders the item's
field-relative scheme notion by an affine-open cover represented by open immersions
from spectra of `CommRingCat` objects, with an explicit algebra map to the base
spectrum, finite-type instances, and `Algebra.IsLocalCompleteIntersection` on each
coordinate ring.  `IsSyntomicAffineChart` renders the three ring clauses for an
individual affine pair: `RingHom.Flat`, `RingHom.FinitePresentation`, and local
complete intersection of every residue-field fibre (`Ideal.Fiber`).

The theorem's first clause is `Flat f ∧ LocallyOfFinitePresentation f` together
with the universal quantification over fields carrying `[Field Ω] [IsAlgClosed Ω]`
and geometric points `ybar : Spec (.of Ω) ⟶ Y`; its fibre is
`Limits.pullback f ybar` and its projection to `Spec Ω` is
`Limits.pullback.snd f ybar`.  The second clause universally quantifies affine
opens `V` and `U`, their affine-open proofs, and `hUV : U ≤ f ⁻¹ᵁ V`, then applies
`IsSyntomicAffineChart`.  The third clause supplies an index type and affine target
opens covering every point of `Y`, and for each target chart an index type and
source affine opens covering every point of `f ⁻¹ᵁ V i`; each source chart has a
witness of the inclusion into the target preimage and satisfies the same three
ring conditions.  The outer proposition is the nested equivalence of these three
conditions.

The dependency declarations used are `AlgebraicGeometry.Scheme` (Mathlib),
`AlgebraicGeometry.Flat` from `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`AlgebraicGeometry.LocallyOfFinitePresentation` from
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`CategoryTheory.Limits.pullback` and its projections from
`Mathlib.AlgebraicGeometry.Pullbacks`, `IsAlgClosed` from
`Mathlib.FieldTheory.IsAlgClosed.Basic`, `Algebra.FinitePresentation`,
`RingHom.Flat`, `Localization.AtPrime`, `Ideal.ResidueField`, and
`Ideal.Fiber` from Mathlib, and
`Algebra.IsGlobalCompleteIntersection` / `Algebra.IsLocalCompleteIntersection`
from `Sheaf.RingTheory.CompleteIntersectionOverField`.

I checked empty schemes and empty source covers, the zero coordinate algebra
(the helper permits it through the complete-intersection predicate), arbitrary
fields including imperfect fields, nonreduced examples such as `k[t]/(t^2)`, and
identity affine charts.  No Noetherian, separated, surjective, or nonemptiness
hypothesis was added.  The quantified chart covers use pointwise membership, so
empty inverse images remain permitted.

Searches made: `msearch.py Q81 ... leanfinder` for an affine criterion for flat
finite-presentation morphisms with complete-intersection geometric fibres (only
flatness/smoothness results); `msearch.py ... leansearch` for affine-local
syntomic criteria (only generic affine-locality results); `msearch.py ... loogle
"syntomic"` (no hits); grep over Mathlib, `WeilConjectures/`, and `lean/Sheaf`
for `syntomic`, `CompleteIntersection`, and `complete.intersection` (no full
criterion; only the existing ring complete-intersection definition and unrelated
syntomic constructions).  The exact item id and the Tags 01UD/01UG text were
also searched across the DAG and project sources; no existing declaration states
this criterion.  The helper notions were therefore written explicitly in this
module and are listed in the node's `lean.declarations`.

No `STATEMENT-DISPUTED` finding or node fault.

## Second reading by Q81

The theorem and both helper definitions were read against the node statement.
The first condition retains flatness, local finite presentation, every algebraically
closed geometric point, and its fibre.  The second retains every affine pair and
all three coordinate-ring clauses.  The third retains target and source affine
covers, the preimage inclusion, and the three clauses on every chart.  The only
formal expansion is the explicit chart predicates and pointwise cover witnesses;
no hypothesis or conclusion was dropped.

Independent maintainer reading of immutable delivery
`3fff89ff9756feb28b4ad526e88ce2f6f346c411` (2026-10-18):

- Objects: `X Y : Scheme.{u}` and `f : X ⟶ Y` are arbitrary schemes and a
  morphism. The scheme helper is a cover by open immersions of affine spectra,
  with explicitly compatible maps to `Spec k`, finite type and the recorded
  `Algebra.IsLocalCompleteIntersection` predicate. This implies local finite
  type, so no extra `LocallyOfFiniteType` premise is needed.
- Condition (1): `Flat f`, `LocallyOfFinitePresentation f`, every algebraically
  closed field and every `ybar` are retained. `Limits.pullback f ybar` and
  `Limits.pullback.snd f ybar` give the correct fibre and field structure.
- Condition (2): both opens are universally quantified and explicitly affine;
  `hUV` is exactly containment in the target preimage. `f.appLE` induces the
  coordinate map. The chart helper requires its flatness, finite presentation,
  and for every prime the finite-type local-complete-intersection fibre.
  `Ideal.Fiber` orders the tensor factors as `κ(p) ⊗[A] B`; tensor symmetry
  gives the node's expression. The module structure is explicitly induced by
  `f.appLE`, not an unrelated scalar action. The finite-type witness is needed
  by the recorded complete-intersection predicate and follows from finite
  presentation; it is not an extra mathematical restriction.
- Condition (3): target affine opens cover every target point. For each member,
  source affine opens cover every point of its preimage and are each contained
  in that preimage. The same chart predicate applies to every source member.
  `(P ↔ Q) ∧ (Q ↔ R)` gives precisely equivalence of all three conditions.
- Dependencies: read every snapshot statement-dependency node and its recorded
  declarations in pinned Mathlib or `Sheaf.RingTheory.CompleteIntersectionOverField`.
  In particular, stalkwise flatness agrees via `Flat.iff_flat_stalkMap`, local
  finite presentation is affine-local, and the ring complete-intersection
  predicate includes zero rings. Read all six proof steps and cited node
  statements; they supply the facts used. The existing field-change module is
  now imported as the proof-dependency convention requires.
- Sources: read Morphisms 01UC--01UG, 01TP/01TQ, and the flatness definition;
  Algebra 00S9, 00SJ and 00SL. No separated, quasi-compact, Noetherian, perfect
  field, reducedness or nonemptiness assumption is present. Empty schemes,
  empty inverse images and fibres, zero chart algebras, `n=c=0`, imperfect
  fields and nonreduced complete intersections remain covered. All binders and
  the universe `u` are bound; the field and cover sizes follow the recorded
  `Scheme.{u}` and geometric-point convention, with no site-universe equality.
- Searches: independently searched Mathlib algebraic geometry, slopmaster2
  `WeilConjectures`, group `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  syntomic, complete intersection, and both helper names. No exact existing
  criterion or scheme helper was found. The delivered report records
  LeanSearch, LeanFinder/Loogle and grep searches. The helpers merely name
  the item's own predicates and are listed in `lean.declarations`; no
  independent missing DAG prerequisite is being concealed.
- Repairs: H8 source citations were absent from the helper docstrings and the
  theorem docstring compressed the six proof steps without their dependencies.
  The complete replacement restores citations and the six-step argument.
  Added the already stated field-change proof dependency import (H9).
  All definition bodies and theorem signatures are unchanged; `lean.statement`
  remains verbatim. No theorem is proved beyond `by sorry`, no hollow
  definition is introduced, and no node statement or dependency record changes.
- Compiler evidence: `scompile.py Q81
  lem-trf-syntomic-geometric-fibres-affine-criterion <snapshot module>` returned
  0, no errors or warnings; sandbox 2.5 s, library module 3.1 s. The wrapper
  currently uses its server side overlay, confirming against the actual
  library despite its older local-overlay documentation. The corrected module
  returned 0 with no errors or warnings through the same wrapper: sandbox
  20.3 s, library module 3.2 s. No global build, live Lean edit or direct SSH command
  was used. No dropped route-pivot dependency or pro-etale substitute occurs.
