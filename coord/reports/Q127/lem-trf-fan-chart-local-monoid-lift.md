## Worker report

This stage-2 delivery states AlgebraicGeometry.fan_chart_local_monoid_lift, with one
sorry theorem and three real canonical helper definitions. The accepted Q157 split,
its statement, proof and dependencies are preserved. The previous worker ending was
about stage 1; coord/brief-stage2.md §0 explicitly authorizes this stage-2 handoff.

Hypothesis and clause correspondence:
- A locally Noetherian fs log scheme is X : FineSaturatedLogScheme; its fields are
  scheme, locallyNoetherian, logStructure and fineSaturated.
- Association from the Zariski site is c.zariski : X.logStructure.IsZariski, the
  recorded framework's characteristic-germ/unit-extension criterion.
- A fine fan is F : FineFan.Fan, with sharp stalks and fine affine charts.
- The given morphism with inverse-image characteristic isomorphism is c : LogFanChart
  X F. Its map retains the continuous map and every section map; stalkBijective
  expresses the inverse-image isomorphism. Bijective monoid maps are local, so no
  separate locality assumption is omitted.
- The point v is x : X.scheme, z is c.map.hom.base x, and P is exactly
  FineFan.stalk F.space.presheaf (c.map.hom.base x), not an unrelated chart monoid.
- The canonical open affine fan F_z is L : FineFan.PointLocalization F z.
  L.generalizations identifies its points with those generalizing z, L.iso identifies
  its restricted space with FineFan.affine P, and L.normalization fixes canonical germs.
- The fs and sharp assertions are IsFineSaturatedMonoid P and FineFan.IsSharp P.
  The finite free group assertion is an existential Module.Basis (Fin n) ℤ of
  Additive (Algebra.GrothendieckGroup P), including n=0.
- The quotient of the ordinary log stalk is c.stalkQuotient x: the canonical
  Associates quotient followed by sheafification, then the inverse of c's stalk
  isomorphism. Its groupification is c.stalkGroupQuotient x, defined by lift.
- Existence of a section is explicit, preventing the arbitrary-section quantifier
  from making the chart-existence clause vacuous.
- Every prescribed group section s with Function.RightInverse s
  (c.stalkGroupQuotient x) admits U, hx, h and a. Here U is an actual Zariski open,
  hx is x∈U, and h has precisely source P and target the log sections on U.
- The containment U⊆c⁻¹(F_z) is ∀ y∈U, c.map.hom.base y∈L.openSet.
- The log-chart assertion is X.logStructure.IsChart ((logOpenEtale X.scheme).obj U) h,
  the recorded associated-log pushout-isomorphism criterion on every geometric stalk.
- The restricted morphism a factors the given c via the equality of sheafed-space
  morphisms a ≫ ofRestrict = ofRestrict ≫ c.map, retaining all section maps.
- The ∀p y hy germ equality says the sharpening of h pulls back the canonical P
  sections through a ≫ L.iso.hom. All-point germ equality is equality of sections
  of the characteristic sheaf, hence gives the full prescribed characteristic map.
- The final ∀p equality in the ordinary log-stalk group completion says that the
  germ of h is exactly s on canonical generators. By the group-completion universal
  property this is equality of the entire group homomorphism with the chosen s.

The helpers contain actual data: quotient, sheafification unit, the inverse of the
specified bijection, and group-completion lift. They choose no arbitrary map or object.
Their small naturality proof is the definitional construction of a morphism; every
new theorem proof is sorry. No source statement correction was needed.

Dependency declarations used:
- Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup: FineSaturatedLogScheme,
  EtaleLogStructure.IsChart, EtalePrelogStructure and the actual monoid sheaf.
- Sheaf.AlgebraicGeometry.FineFanBlowup: FineFan.Fan, IsSharp, stalk, germ,
  stalkMap, sharpPresheaf, affine and AffineOpen.
- Sheaf.AlgebraicGeometry.LogFanChartBlowup: logOpenEtale,
  EtaleLogStructure.zariskiPresheaf, sharpSpace, sharpSection, IsZariski, LogFanChart.
- Sheaf.AlgebraicGeometry.StrictFanChartLocalComparison: FineFan.PointLocalization.
  Only its normalized localization structure is used, not the downstream theorem.
- Sheaf.AlgebraicGeometry.AffineFanHomUniversal: FineFan.affinePullback.
- Proof imports: FgCommutativeMonoidFinitePresentation.fg_commutative_monoid_finite_presentation
  (the declaration is at root), associatedLog_universal_stalks,
  FineFan.affineFan_localization_sections, AlgebraicGeometry.face_sharpening.
  The source modules and full recorded statement signatures were opened. The other
  proof dependencies have no Lean record and are not needed to elaborate this statement;
  no missing proof prerequisite is silently assumed as a new theorem.
- The geometric-stalk isomorphism criterion is the recorded Mathlib match in
  Mathlib.AlgebraicGeometry.Sites.EtalePoint; it is already in the public import closure.

Edge cases checked before accepting the statement:
P=1 (additive zero) gives rank zero, the unique group section and the trivial chart.
The empty scheme has no x, so no impossible witness is required. A standard log point
has log stalk P×Aˣ: arbitrary sections are unit twists and are all retained. Unit groups
may have torsion; only the characteristic group is asserted free. Singular sharp fs
monoids are allowed: no free-monoid hypothesis is present. At generalizations the unit
face can be nonzero; the all-point IsChart condition and sharpening equality still apply.
No log regularity, global saturation of F, affineness of U or scheme separateness is added.
Universe u is explicit and autoImplicit is disabled.

Searches:
- msearch.py leanfinder: “A prescribed characteristic fan chart of a Zariski fine
  saturated log scheme lifts locally to a monoid chart with any group section at the
  point.” Eight hits, including exists_lift_of_germInjective and manifold chart lemmas;
  their types concern rings/schemes/manifolds, not logarithmic monoidal-space charts.
- msearch.py loogle: "LogFanChart"; zero hits.
- msearch.py grep: fan.?chart|characteristic.?monoid|log.?structure; zero Mathlib hits.
- msearch.py leansearch: “Zariski locally lift a prescribed characteristic fan chart
  of a fine saturated log scheme with any stalk group section.” Eight unrelated ring
  spreading and localness hits. The actual responses are in sandbox searches.jsonl.
- rg of lean/WeilConjectures and lean/Sheaf for the node id, theorem name and helper
  names found no pre-existing theorem or canonical helper with these names. The
  existing LogFanChart, sharpening and point-localization interfaces are reused.
- Read ILO VI 3.7(a) p.75 (split exact sequence and extension to a chart), VIII
  3.1.4(iii), 3.1.8(ii), 3.1.10(ii), pp.98–100, and 3.3.12–3.3.13, pp.108–109.

Validation update, 2026-10-23 UTC: the required initial saved-packet dry run
reproduced the two module-ownership refusals. Reading all seven repaired modules
with scompile.py --source showed that the live server now already has their
module-mode public interfaces. The saved conversions are identical to those
sources apart from whitespace. The obsolete dependency modules and node copies
were therefore removed from the delivery, retaining the actual theorem module
and item record unchanged. The original full packet is preserved in the sandbox
archive retained-interface-repairs.zip. All original definitions are reused via
their published modules. No DAG edge or mathematical statement was changed.

The original ownership refusal no longer requires delivery changes, because these
interfaces are already in the live sources. However, an item-only scompile.py and
normal deliver2.py --no-push both now fail with:

    error: cannot import non-`module` Sheaf.AlgebraicGeometry.LogFanChartBlowup from `module`

This disagrees with the module-mode live source returned by scompile.py --source.
For diagnosis, the seven unchanged live sources were saved under
scratchpad/live-source-check/lean and supplied with the item to scompile.py.
All eight files compiled separately, including sandbox and library checks,
with no errors or warnings. The item library check took 5.4 seconds. This proves
the retained statement compiles on the current source interfaces; the normal
published artifact still exposes the legacy non-module interface. These diagnostic
source copies are not delivery modules and no dependency node is changed.
The canonical definitions and theorem statement remain exactly as in the saved packet.

## Retained-packet self-check

Re-read the node and FanChartLocalMonoidLift.lean after removing the now-published
interface repairs. X and c supply locally Noetherian fs, Zariski association and
the characteristic-sheaf isomorphism. L supplies the canonical generalization
affine open at c(x), with normalized stalk coordinates. The first three clauses
assert fs, sharpness and a finite integral basis of the group completion of that
same stalk. The quotient is the canonical sharpening/sheafification map followed
by the inverse given chart isomorphism; no arbitrary comparison map is used.
Existence of a group section is asserted separately. Each prescribed section
then yields U containing x, its containment in the inverse image of L.openSet,
a genuine log chart h and a restricted fan morphism a. Equality of sheafed-space
morphisms fixes the restriction of c, all-point germ equality fixes the prescribed
characteristic sections, and the final equality fixes the chosen group section
on every generator. Together these render every clause of the node, including
arbitrary section and rank-zero cases. No mismatch was found and no declaration
or node statement was changed. This is a retained-packet self-check; no other
agent was started, as explicitly required by the dispatcher brief.

## Final validation

The final prescribed deliver2.py --no-push completed successfully: commit
12c00fb2e8b passes server preflight and compiles. Its staged paths are exactly
the item node, FanChartLocalMonoidLift.lean and this report. The earlier
published-interface failure no longer blocks the prescribed wrapper.
The signature is verbatim in lean.statement, autoImplicit is disabled, no
Lean line exceeds 100 characters, and the only postponed proof is the named
fan_chart_local_monoid_lift theorem. The theorem and its canonical helper
definitions were retained without changes throughout this repair.


## Maintenance resolution (Q127, server commit 69f882ab12e)

Server commit 69f882ab12e1c7e4973f52887348436143cf6f99 fixes the legacy module
interfaces that blocked this packet. AffineFanHomUniversal,
AffineFanLocalizationSections, LogFanChartBlowup, StrictFanChartLocalComparison,
FineMonoidFiniteSaturation and GordanRationalCone now have the saved
module/public-import/exposed-section conversions on sheaf-dag. Their
mathematical declarations, bodies and docstrings are unchanged. FineFanBlowup
was already converted. Each repaired file, FineFanBlowup and the retained
item passed tools/lean_file.sh individually with the 60-second limit.

The final packet intentionally retains seven dependency Lean files and their
seven owner node files as EXACT COPIES OF THE COMMITTED BASE. The previous
worker's lean.note patches are backed up as *.maint-Q127-1792780141.bak
and are no longer active. The copies are needed temporarily as compile
inputs: without them scompile still selects the last green build's legacy
LogFanChartBlowup.olean. Supplying these already committed sources compiles
them privately; they produce NO delivery delta. This has been verified:
the dry run stages only the item's Lean file, item node and report and
passes both compilation and server preflight (d45e1ea1609).

Next worker: retain these exact base copies while the published build lags,
run deliver2.py --no-push, then deliver normally. Do not reinstate the old
dependency lean.note patches or add log-fan-chart-blowup/strict-fan-chart-
local-comparison as prerequisites; their theorem nodes are downstream. The
item's Lean statement and all mathematical dependencies are unchanged.
No mathematics needs to be redone. The original archived packet and the
maintenance .bak files remain available for provenance.

## Second reading by Q127

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
