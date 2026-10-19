## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricSpecializationStrictLocalLift` states
`AlgebraicGeometry.Scheme.exists_geometricPoint_strictHenselization_lift`, with a sorry
proof, exactly the lifting assertion of Stacks Tag 0GJ5 (remark-can-lift). Read the local
Stacks source, including its prescribed embedding of residue fields and commutative diagram.
No definitions or auxiliary theorems are introduced.

Hypothesis and conclusion correspondence:

- Scheme S: `{S : Scheme.{u}}`.
- Points t and s: `(t s : S)`.
- s in the closure of {t}: `(hts : t ⤳ s)`, in this direction of specialization.
- Geometric coefficient fields: `{Ωt Ωs : Type u}`, each with `Field` and `IsAlgClosed`.
- Chosen geometric points: `barT : Spec (.of Ωt) ⟶ S` and
  `barS : Spec (.of Ωs) ⟶ S`.
- They lie over t and s: `hbarT : barT (IsLocalRing.closedPoint Ωt) = t` and
  `hbarS : barS (IsLocalRing.closedPoint Ωs) = s`. A field spectrum has this unique point.
- The strict local scheme: `strictHenselizationScheme barS`.
- Its structural map p: `strictHenselizationStructuralMap barS`.
- Existence of the required morphism: `∃ a : Spec (.of Ωt) ⟶ strictHenselizationScheme barS`.
- The exact commuting triangle: `a ≫ strictHenselizationStructuralMap barS = barT`.
  This preserves the prescribed geometric morphism, including its residue embedding.

Statement dependencies used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points use the recorded
  inline field-spectrum convention. Read `Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField`, which describes exactly the underlying point
  and residue embedding.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationScheme` and
  `Scheme.strictHenselizationRing`, the spectrum of the small affine coordinate-ring colimit.
- `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap`, characterized by
  `Scheme.exists_strictHenselizationStructuralMap` as the common projection composite.

All modules recorded for stated proof dependencies are imported, directly or through
the existing public statement imports. The proof imports include
`Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap` (which publicly imports the
residue-parametrized functoriality theorem used in step 2) and
`Sheaf.RingTheory.WeaklyEtaleField` (whose residue-field clause is used in step 4).
The docstring carries all five DAG proof steps with their dependency names.

Edge cases checked: the empty scheme admits no chosen points or geometric points, so
introduces no exception. For t=s the assertion still allows arbitrary independently
chosen algebraically closed fields and residue embeddings. Nonclosed t, infinite
algebraic residue extensions and positive characteristic are allowed. No finiteness,
Noetherian, separation, or characteristic hypothesis is added. The common universe is
the one used by the recorded strict-local construction and Mathlib field-spectrum
encoding; u is arbitrary. No index-universe restriction is introduced.

Searches for an existing statement:

- msearch leanfinder, “Geometric specializations lift to the strict local scheme at the
  special point”: eight hits on stalk specialization morphisms, none this lift.
- msearch loogle, `"StrictHenselization"`: zero hits.
- msearch grep, `strictHensel.*special|special.*strictHensel|geometricSpecialization`:
  zero Mathlib hits.
- msearch leansearch, “Lift a geometric point through the strict henselization along a
  specialization”: unavailable (Internal Server Error).
- rg with the same regular expression in the upstream WeilConjectures tree, project
  Sheaf tree and upstream-name index: no hits. grep for this node id in upstream:
  no hits. Read both project strict-henselization modules to identify the existing
  constructions rather than duplicate them.

Validation: scompile.py compiled the delivered theorem module cleanly on the server
(nice 19, two threads, 60 seconds per file). No statement dispute or correction.

## Dependency record repair (return L, immutable head f680dd7cd8ea)

The return reports that `def-weil-pbc-strict-henselization-structural-map` acquired a
new Lean record on newtargets-dag after the previous delivery's base. Reviewed the
current dependency node and fetched the current server source with
`scompile.py --source Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`.
The current record, by NA on 2026-10-15, already names
`AlgebraicGeometry.Scheme.strictHenselizationStructuralMap` and its characterization
`AlgebraicGeometry.Scheme.exists_strictHenselizationStructuralMap`. Their signatures
use the same `strictHenselizationScheme barS` as this theorem. The characterization
identifies the map with each affine-neighbourhood projection followed by its
structural morphism, exactly the dependency's definition and the map p in this item.
Thus the new record is usable unchanged; the earlier NL override is unnecessary.
Removed the stale dependency JSON from the sandbox delivery, retaining the current
published dependency record rather than overwriting it. No dependency module or
new node is now delivered. No theorem signature or mathematical statement changes.

The second reading below is the historical independent reading of the original
statement. Its account of delivering a dependency-record repair is superseded by
this section; the next reader should review this explicit removal and validation.

## Earlier second reading (a previous round; superseded)

Independently compared the node, its four statement dependencies, their actual
Lean declarations, and Stacks etale-cohomology.tex, Tag 0GJ5,
remark-can-lift (including the preceding specialization-map discussion).
The source assumes an arbitrary scheme, with no ambient Noetherian,
quasi-compactness, separation, or characteristic assumption.

Object/hypothesis/conclusion checklist (all pass):

- Arbitrary scheme S: `{S : Scheme.{u}}`; Mathlib's locally ringed-space
  scheme and its actual scheme morphisms, as def-pc-scheme records.
- Ordinary points t and s: `(t s : S)`, with no extra point property.
- Specialization s in the closure of {t}: `(hts : t ⤳ s)`; the order agrees
  with the source's t leadsto s and permits t=s.
- Independently chosen geometric points: `{Ωt Ωs : Type u}` with separate
  `Field` and `IsAlgClosed` instances, and the morphisms
  `(barT : Spec (.of Ωt) ⟶ S) (barS : Spec (.of Ωs) ⟶ S)`.
  This is exactly def-weil-geometric-point's inline convention. Opened
  Mathlib's `Scheme.SpecToEquivOfField`: it identifies each full morphism
  with the underlying point and residue-field embedding; no common field
  or common embedding is assumed.
- They lie over the named points: `hbarT : barT (IsLocalRing.closedPoint Ωt) = t`
  and `hbarS : barS (IsLocalRing.closedPoint Ωs) = s`. A field spectrum has
  exactly this one point; these equalities add no restriction beyond lying over.
- The specified strict local scheme: `strictHenselizationScheme barS`.
  Opened StrictHenselization.lean: its ring is the coordinate-ring colimit
  over a small representative category of all affine pointed etale
  neighbourhoods; its scheme is that ring's spectrum, and its canonical
  cone has the claimed inverse-limit interpretation. It is the object of
  def-weil-pbc-strict-henselization-limit, not a substitute local scheme.
- The specified structural map p: `strictHenselizationStructuralMap barS`.
  Opened StrictHenselizationStructuralMap.lean, including
  `exists_strictHenselizationStructuralMap`: it is precisely the common
  composite of each limit leg, the affine spectrum identification, and
  the neighbourhood's map to S. Its definition chooses this uniquely
  specified map from that theorem, so has no hollow data.
- Required morphism and quantifier order: after all the above data,
  `∃ a : Spec (.of Ωt) ⟶ strictHenselizationScheme barS`.
- Required triangle: `a ≫ strictHenselizationStructuralMap barS = barT`.
  This is equality of scheme morphisms with the prescribed barT, hence
  includes its residue embedding, exactly as the source's embedding over
  kappa(t) and commutative diagram demand. There is no extra conclusion.

Edge cases: an empty S cannot supply t,s or barT,barS; the assertion is
correctly vacuous. The zero-ring spectrum is covered by that case; zero
fields are excluded by the very definition of geometric point. Equality
of points t=s still allows unrelated algebraically closed coefficient
fields and embeddings. Nonclosed points, infinite residue extensions,
positive characteristic and characteristic zero all remain allowed. There
is no n, finite index set, or finiteness condition to restrict. The arbitrary
universe u is the one in Mathlib's scheme category and the recorded
geometric-point and strict-local APIs; it introduces no independent small
universe of test objects and no additional restriction on those APIs.

Independent searches with different wording: msearch leanfinder,
"A geometric generization factors through the spectrum of the strict local
ring at a special point", returned only stalk-specialization results;
msearch loogle `"strictLocalization"` returned zero hits; msearch grep
`strictLocalization|generization.*hensel|hensel.*generization` returned zero.
Also searched the actual Mathlib, upstream WeilConjectures, project Sheaf
sources and upstream-name index for strictLocalization, strict-henselization
lifts and geometric-point lifts. The old strictLocalization name appears
only in the name index, not in pinned upstream source. Opened the nearby
`AlgebraicGeometry.strictHenselizationMapExists`: it concerns functoriality
between two strict local schemes with pointed residue data, and does not
state this geometric-generization lift. Other geometric-point lifts concern
immersions or field-extension stalk comparisons. None is this statement.
The worker's LeanSearch service-unavailable result is retained.

Dependency delivery reviewed: the structural-map dependency changes only
its lean record to the existing project declaration just checked. The old
record names an unavailable pinned upstream module. Reuse is correct and
introduces no duplicate definition. There are no new nodes or sibling modules.
No statement correction was needed, so there are no corrected citers to audit.

No mismatch found; no Lean or node text changed in this second reading.
Appended this independent audit only. The module has no definitions or
proved auxiliary statements, and its sole theorem has a whole-proof sorry.
Both docstrings identify Tag 0GJ5 and the blueprint id. The theorem docstring
carries all five DAG proof steps, including affine reduction, local faithful
flatness, prime lifting, residue algebraicity, and the prescribed embedding.
Checked the imports against recorded proof dependencies, explicit binders,
namespace, and line widths. The node's lean.statement equals the file's
signature verbatim. Server scompile.py compiled the delivered module cleanly
at nice 19, two threads, 60 seconds per file, with no warnings or errors.

## Second reading by NL

This reading independently opened the item JSON, the delivered Lean file, all four
statement dependency nodes, the actual strict-henselization modules, Mathlib's
`Scheme.SpecToEquivOfField`, and Stacks etale-cohomology.tex at
`remark-can-lift` (Tag 0GJ5), including its preceding context. The source starts
with an arbitrary scheme; no global finiteness or characteristic hypotheses apply.

Object, hypothesis, and conclusion checklist:

- Scheme S: `{S : Scheme.{u}}`. Pass: this is the recorded Mathlib scheme,
  with genuine scheme morphisms, not just continuous maps.
- Ordinary points t,s: `(t s : S)`. Pass: neither point is required to be closed.
- Specialization: `(hts : t ⤳ s)`. Pass: s lies in the closure of t, in the
  source's direction, including equality.
- Chosen geometric points: `{Ωt Ωs : Type u}`, separate `Field` and
  `IsAlgClosed` instances, and `(barT : Spec (.of Ωt) ⟶ S)` and
  `(barS : Spec (.of Ωs) ⟶ S)`. Pass: exactly the dependency's inline
  convention; no shared field or residue embedding is assumed. Opened
  `SpecToEquivOfField`: the entire morphism records both point and embedding.
- Lying over the named points: `hbarT` and `hbarS` evaluate at
  `IsLocalRing.closedPoint` and equate the images with t and s. Pass: a
  field spectrum has this unique point, so these assert exactly lying over.
- Strict local scheme: `strictHenselizationScheme barS`. Pass: opened its
  definition as Spec of the coordinate-ring colimit on the small representative
  category of affine pointed etale neighbourhoods, together with the canonical
  cone and representative equivalence. This is the recorded dependency object.
- Structural map p: `strictHenselizationStructuralMap barS`. Pass: fetched
  the current server source using `scompile.py --source` and read the full
  `exists_strictHenselizationStructuralMap` characterization. Each projection,
  affine-spectrum identification, and neighbourhood map has composite p.
  The definition chooses this uniquely determined map, not arbitrary data.
- Existence, after all chosen data: `∃ a : Spec (.of Ωt) ⟶
  strictHenselizationScheme barS`. Pass: correct source, target and quantifier order.
- Triangle: `a ≫ strictHenselizationStructuralMap barS = barT`. Pass:
  equality of full morphisms retains the prescribed embedding over kappa(t),
  exactly as the source's diagram and embedding-of-extensions requirement say.

Edge cases: empty schemes (including Spec of the zero ring) cannot supply t,s,
so are vacuous. Fields are nonzero by definition. The case t=s permits unrelated
algebraically closed fields and embeddings. Arbitrary nonclosed points, infinite
algebraic extensions, and every characteristic are included. No integer degree
or index set occurs. The arbitrary common universe u is precisely the recorded
scheme/geometric-point/strict-local API universe, and imposes no additional
size equation or small test-object quantifier.

Independent searches, using different wording from the worker:
`msearch.py ... leanfinder "An algebraically closed geometric generization
factors through a strict local scheme"` returned eight unrelated generic-point,
rational-map and generalizing-map results; `loogle '"strictHenselization"'`
returned zero hits. Direct rg on Mathlib, upstream WeilConjectures, and project
Sheaf for `strictLocalization`, strict-henselization lifts, and strict
 generizations found no exact theorem. Opened the nearby
`AlgebraicGeometry.strictHenselizationMapExists`: it constructs functoriality
between two strict local schemes with compatible pointed residue data, not
this lift of an arbitrary prescribed geometric generization. The worker's
recorded unavailable LeanSearch query is retained. No duplicate notion is needed.

No mathematical mismatch found and no Lean or node text changed. The stale
structural-map dependency override was already removed by the worker's current
repair; this reading verifies that removal against the current published NA
record and the actual server source. There are no new nodes or dependency
modules to deliver, and no statement correction or citer audit is required.
The only delivered theorem has whole-proof `sorry`; no definitions or auxiliary
proofs are introduced. Both docstrings have the source and blueprint id, and
the theorem docstring follows all five node proof steps. Checked explicit
binders, namespace, line widths and signature extraction: `lean.statement`
equals the theorem signature verbatim. Validation results follow below.

Server validation: `scompile.py NL
lem-weil-pbc-geometric-specialization-strict-local-lift
lean/Sheaf/AlgebraicGeometry/GeometricSpecializationStrictLocalLift.lean`
passed both sandbox and library single-file checks without errors or warnings
(nice 19, two threads, default 60 seconds per file).


## Maintainer second-reader correction

The immutable delivery at 6a816b772ccef7026c6d8596ebb8f8a045bbf91c has an H9
proof-dependency import omission. Its base already records
`lem-weil-pbc-strict-henselization-functoriality` in
`Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap` and
`lem-weil-pbc-weak-etale-field` in `Sheaf.RingTheory.WeaklyEtaleField`.
The worker paragraph saying the latter has no recorded declaration was stale.
The complete replacement module imports both recorded modules without `public`;
the canonical-map module publicly retains the older residue-parametrized
functoriality theorem, so the proof plan's closed-point clause remains available.
The complete report replacement corrects the stale paragraph. Earlier statements
that all imports were checked are superseded by this explicit finding.

No theorem signature, mathematical statement, dependency record, or proof changes.
All object/hypothesis/conclusion and edge-case checks in the substantive second
reading above were independently confirmed by the maintainer reviewer.
The original module passed server-only scompile.py backend compilation in 1.4 s
(nice 19, two threads, 60 seconds per file); the complete replacement also passed cleanly in 1.4 s with the same limits.
The server compiled its canonical-map and weakly-etale-field side imports
separately in 1.3 s and 1.4 s respectively. No global build or live Lean write was performed.
