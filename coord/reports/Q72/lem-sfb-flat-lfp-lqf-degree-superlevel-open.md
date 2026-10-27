## Worker report

Item: `lem-sfb-flat-lfp-lqf-degree-superlevel-open`.
Module: `Sheaf.AlgebraicGeometry.FlatLfpLqfDegreeSuperlevelOpen`.
Declaration: `AlgebraicGeometry.Scheme.Hom.isOpen_fiber_degree_ge_of_flat_lfp_lqf`.
This is a statement-only delivery: the theorem's entire proof is `sorry`.
The node is unchanged except for `lean`. No new notion, dependency repair,
statement correction, or disputed statement is needed.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 086R,
`lemma-stratify-flat-fp-lqf`, and preceding Tag 07RZ,
`lemma-stratify-flat-fp-qf`. Tag 086R explicitly says its assertion means
openness of the degree-superlevel sets; the node restricts it to fibres
finite over their residue fields. Its affine-local proof and the node's
six expanded steps are recorded in the theorem docstring.

Hypotheses and clauses, in statement order:

- Schemes and their morphism: `{Y T : Scheme.{u}} (f : Y ⟶ T)`.
  The arbitrary universe `u` is explicitly declared, as are all variables.
- Flat: `[Flat f]`, the recorded affine-local predicate, equivalent to
  flatness of all stalk maps by `Flat.iff_flat_stalkMap`.
- Locally of finite presentation: `[LocallyOfFinitePresentation f]`.
- Separated, meaning closed-immersion diagonal: `[IsSeparated f]`.
  This is the separated clause supplied by `def-weil-proper-morphism`;
  no properness assumption is imposed.
- Locally quasi-finite: `(h_lqf : f.IsLocallyQuasiFinite)`, using the
  dependency's Stacks predicate, including its finite-type requirement.
- At every point, finite scheme-theoretic fibre over its residue field:
  `(h_finite : ∀ t : T, IsFinite (f.fiberToSpecResidueField t))`.
  This requires scheme-theoretic finiteness, rather than just a finite
  set of points. `f.fiber t` is the canonical pullback along
  `T.fromSpecResidueField t`; the displayed morphism is its second projection.
- Write the fibre as `Spec B_t` and take its dimension over `κ(t)`:
  `(f.fiberToSpecResidueField t).finrankΓ`. The existing definition is
  `Module.finrank (T.residueField t) Γ(f.fiber t, ⊤)` with the canonical
  algebra structure induced by that second projection and `ΓSpecIso`.
  The finite-fibre hypothesis ensures affineness and finite dimension,
  so this is exactly the node's finite fibre degree, as already used by
  `BoundsFiberDegrees` in the recorded fibre-degree dependency.
  Writing an arbitrary presentation `B_t` is unnecessary: its canonical
  section algebra is the same coordinate algebra up to algebra isomorphism.
- Every nonnegative integer threshold: `(d : ℕ)`.
- The superlevel subset is open:
  `IsOpen {t : T | d ≤ (f.fiberToSpecResidueField t).finrankΓ}`.
- No uniform bound and no quasi-compactness of either scheme: no such
  binder occurs. In particular `BoundsFiberDegrees` and
  `HasUniversallyBoundedFibers` are not assumed.

Statement dependencies used, with their source signatures and docstrings read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: the recorded proper-morphism
  family; its separated member `AlgebraicGeometry.IsSeparated` is defined in
  `Mathlib.AlgebraicGeometry.Morphisms.Separated` by the closed diagonal.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, unfolding to
  `IsQuasiFiniteAtPoint` at every point. The weaker bare Mathlib predicate
  is not substituted.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `WeilConjectures.AlgebraicGeometry.FiberDegreeBound`: `BoundsFiberDegrees`
  and `HasUniversallyBoundedFibers` expose the shared degree convention.
  Their public import `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`
  defines `Scheme.Hom.ΓAlgebra` and `Scheme.Hom.finrankΓ`, used here directly.

Proof dependencies have plain imports: `Restrict` (open preimage pullback),
`QuasiSeparated` (qcqs permanence and affine schemes), `AffineScheme`,
`ClosedImmersion` (base change), `Limits` (finite discrete schemes affine),
`RingTheory.QuasiFinite.Basic` (finite algebra spectrum discrete), and the
recorded upstream modules `SeparatedLqfBaseChange`, `IsLocallyQuasiFiniteResLE`,
`QuasiFiniteLocallyQuasiFinite`, `FlatQuasiFiniteStratification`.
The remaining proof dependency modules (`Flat`, `FinitePresentation`, `Finite`,
and `Morphisms.FiberDegree` for finite locally free morphisms) are already
publicly imported for the statement. No import cycle was introduced.

Edge cases checked before writing:

- `d = 0`: the predicate is true at every point; the set is the whole base.
- Empty target: every quantified fibre hypothesis is vacuous and the conclusion
  is openness of the empty subset of the empty space.
- Empty source: every fibre is the empty finite scheme with zero section algebra;
  thresholds above zero give the empty set, and zero gives the whole base.
- Nonreduced finite fibres: `finrankΓ` counts algebra dimension and therefore
  multiplicities; it does not count underlying points.
- No globally bounded degree: a disjoint union of base components carrying
  finite free families of ranks tending to infinity is permitted.
- Non-quasi-compact source and target: no `CompactSpace`, `QuasiCompact`, or
  finite-type assumption on the whole morphism is added.
- Arbitrary residue-field characteristic and inseparability are allowed.

Searches actually run (2026-10-24 UTC):

- `msearch.py ... leanfinder` with query
  `The degree of finite fibres of a flat locally finitely presented separated locally quasi finite scheme morphism has open superlevel sets`:
  8 hits. The leading results were `AlgebraicGeometry.UniversallyOpen.of_flat`,
  `AlgebraicGeometry.LocallyQuasiFinite`, and
  `AlgebraicGeometry.isOpenMap_of_generalizingMap`; the other hits were basic
  finite-presentation, finite-fibre, finite-type and finite-morphism predicates.
  None states degree-superlevel openness.
- `msearch.py ... loogle "AlgebraicGeometry.Flat, IsOpen"`: 0 hits.
- `msearch.py ... grep "(fiberDegree|fibreDegree|finrank.*fiber|LowerSemicontinuous)" AlgebraicGeometry`:
  0 hits in the wrapper's Mathlib search.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `fiberDegree|fibreDegree|finrank.*fiber|superlevel|stratify-flat-fp-lqf`:
  found the existing degree API and related bounded/quasi-finite stratifications.
  Opened `FiberDegreeBound`, `Morphisms/FiberDegree`, `QuasiFiniteMorphism`,
  `FlatQuasiFiniteStratification` and `FlatFpLqfMaximalDegreeLocus`.
  The quasi-finite stratification assumes quasi-compactness; the maximal-degree
  locus theorem assumes a global degree bound. Neither is the present theorem.
- Direct `rg` for `isOpen.*(finrankΓ|fiberDegree)|(finrankΓ|fiberDegree).*isOpen|086R|degree.superlevel`
  over both project roots: no exact existing statement.
- `grep -rn "lem-sfb-flat-lfp-lqf-degree-superlevel-open" lean/WeilConjectures`:
  no match. Direct search for the chosen theorem name in Mathlib and both
  project roots and `dag/lean_names_upstream.json`: no match.
- No repair note for this item was present in `coord/repair-notes`.

Validation: compiled with the prescribed `scompile.py`; delivery dry-run and
push use `deliver2.py`. The compiler result and preflight outcome are recorded
below after completion.

## Second reading by Q72

Performed a separate rereading of the node, source, dependency definitions and
completed signature in this worker session. The dispatcher explicitly prohibits
starting another agent, so this section does not claim an independent worker review;
the maintainer's independent review remains the delivery review.

The three typeclass hypotheses match flatness, local finite presentation and
separatedness individually. `h_lqf` uses the exact recorded Stacks predicate;
`h_finite` quantifies over every base point and requires finiteness of the second
fibre projection. The `finrankΓ` definition was checked to use the structural
residue-field algebra, not an arbitrary scalar action. The final set has inequality
`d ≤ degree`, including equality and threshold zero. There are no hidden choices of
coordinate algebra, global finiteness bounds, reducedness assumptions, or restrictions
to closed/geometric points. The source's affine-local union argument is recorded in
all six steps, including the multiplicity and finite-fibre-capture arguments.
No mathematical or signature mismatch was found; no correction was made.

Compiler outcome: `scompile.py Q72 lem-sfb-flat-lfp-lqf-degree-superlevel-open`
accepted both its sandbox probe and the actual library module (exit 0), with no
reported compiler errors or warnings. The actual library compile took 5.4 seconds;
slot acquisition is outside the compiler's 60-second execution limit. A local
record check confirms that `lean` is the sole changed node field, the signature
is verbatim, every Lean line is at most 89 characters, and the only postponed
proof is the one named theorem.

Delivery dry-run outcome: `deliver2.py ... --no-push` printed
`OK (dry run): commit 53888fd094e passes the preflight and compiles; nothing pushed`.
