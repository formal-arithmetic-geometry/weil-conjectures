## Worker report

Q06, stage 2, 2026-10-22. Item: lem-sfb-knudsen-pointed-forgetful-universal-curve.

The module Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve states
AlgebraicGeometry.exists_knudsen_pointed_forgetful_universal_curve, with `sorry`.
It also supplies real auxiliary data for the very universal curve in the node:
Knudsen's category C_{g,r}, its projections, the classifying map of an ordered
family, the comparison in its 2-fibre product, the represented point, and the
geometric insertion predicate. All these helpers belong to this node's
construction and are listed in lean.declarations. No definition contains sorry
or chooses a family, a morphism or an equivalence from a mere existence theorem.
The auxiliary pullbackCurveMap_properties is a named theorem with `sorry`,
carrying the fibre-product proof in its docstring; it provides the cartesianness
and marking proofs needed by the classifying map, rather than hiding proofs in
definition data. Category and functor laws are actual identity/composition data.

The previous dispatch status misidentified Q05's reviewed stage-1 split as an
already completed stage-2 statement. The current node has no Lean binding, and
Q05's report explicitly says stage 1 only. The module was absent in the live
server source as well. This delivery adds the actual Lean statement; it does
not re-record an unchanged already-landed binding. No node statement, proof,
dependency list or maintainer-owned review field is changed.

Clause-by-clause correspondence:

1. An arbitrary scheme S, g at least 2, and r at least 0 are the explicit binders
   `(S : Scheme.{u}) (g r : ℕ) (hg : 2 ≤ g)`. Using ℕ introduces no further
   restriction on these nonnegative integers. All universes and variables are
   explicit; autoImplicit is false. StablePointedModuli is exactly the recorded
   definition, including geometric genus, projective-bundle projectivity,
   connected nodal curves and individually labelled smooth disjoint sections.
2. The natural forgetful-and-stabilizing morphism is
   `StablePointedUniversalCurve.forgetful c`, the composite of contraction c
   with the projection that forgets its arbitrary extra section. Both are
   BasedFunctor objects over Over S. The projection never forgets an old label.
3. For every stable family X, `X.familyMap` sends a test arrow A to the recorded
   `X.pullback A.left A.hom`, with the paired sections. Its map on arrows is
   the actual pullback map, not an arbitrary map with a cartesianness assumption.
   `moduliTwoFiberProduct X.familyMap (forgetful c)` is the dependency's actual
   2-fibre product, retaining its comparison and its automorphisms.
4. Its representing functor R has target `schemeSlice X.totalScheme`, and
   `R.toFunctor.IsEquivalence`. Here totalScheme is Over.mk of
   `X.projection ≫ X.base.hom`; the objects of its slice over a test scheme U
   are precisely S-maps U → X. Slice fibres have only identity arrows, so this
   is the usual discrete functor of points, without replacing a moduli fibre
   by its set of isomorphism classes. This slice formulation is the formulation
   explicitly used in Knudsen's displayed universal-curve square.
5. The point identification is fixed, not just asserted abstractly:
   `(R.obj Z).hom.left = eqToHom (...) ≫ representedPoint c X Z`.
   representedPoint transports `(c.obj Y).extra` along the inverse of the
   comparison `X_U ≅ F(Y)` and projects X_U to X. The comparison remains part
   of Z. The following equation with X.projection says this representation
   is over X.base, not merely over S. The equality transports only the strict
   equality of bases supplied by R.w_obj.
6. The arbitrary extra section is the field `extra` with only its section
   equation. The last-marking equation says `Y.sections (Fin.last r) ≫ q Y`
   is this extra section, after the stated equality transport of bases. The
   old-marking equation uses `i.castSucc`, preserving each label separately.
7. Stabilization's inserted rational component is specified by HasFiberGeometry.
   Over every algebraically closed field and every geometric base point, the
   actual fibreContraction is an isomorphism on all opens away from the extra
   point; it is an isomorphism on the entire fibre when the point is smooth
   and avoids every old marking; otherwise its scheme fibre at the extra
   point is the actual ProjectiveLine over that field, with the structure map
   respected. Stable nodal source/target and preservation of markings give
   precisely the rational tail at an old marking and the bridge at a node.
   The line is not just a set of rational points or a genus-zero numerical test.
8. Contraction and stabilization are c and s with the natural isomorphisms η
   from the identity to c.comp s and ε from s.comp c to the identity. Both
   use ModuliTwoIso, whose components lie over identities on schemes. Their
   arrows preserve all old labels and, in C_{g,r}, the arbitrary extra section.
   Thus they assert mutual inversion including arrows and automorphisms.
9. Naturality of q is the equation `h.map ≫ q Z = q Y ≫ (c.map h).val.map`
   for every cartesian family arrow h, including arrows over arbitrary base
   changes. Together with the based functors and based natural isomorphisms,
   this expresses compatibility of contraction, stabilization and both
   comparisons with arbitrary base change, without a restriction to fields,
   reduced schemes or Noetherian bases.
10. The structural-morphism conclusion asserts IsProjectiveBundle, Flat,
    LocallyOfFinitePresentation, QuasiCompact and QuasiSeparated of
    X.projection. The last three are finite presentation in the stated
    convention. The curve assertion, including nodality, connectedness,
    pure dimension one and genus g, is already data of X. Because R is over
    X.base, this is precisely the base change of the forgetful morphism.
11. For X in the universal-curve category, Smooth X.family.projection and
    disjointness of its extra section from every old marking imply
    `IsIso (q (s.obj X) ≫ (ε.val.hom.app X).val.map)`.
    This is the canonical stabilization projection to X, through the counit,
    and identifies the underlying curve with X. The previously stated
    marking and extra-section equations, followed by ε (an arrow preserving
    all these sections), identify its labels with the old labels followed
    by the appended extra section. It imposes no arbitrary choice of an
    underlying isomorphism.
12. The final quantified clause states stability of the specified recorded
    pullback for every X, T and a. It uses the dependency's actual pullback,
    sections and section_projection, not a second stability predicate.

Dependencies read and used:

- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids:
  AlgebraicGeometry.StablePointedModuli, StablePointedModuli.Hom,
  StablePointedModuli.forget, StablePointedModuli.pullback,
  StablePointedModuli.pullbackArrow and pullback_properties;
  CategoryTheory.ModuliTwoIso and moduliTwoFiberProduct. The full source and
  docstrings were read locally and checked with scompile.py --source against
  the live server. The level-structure and coarse-moduli clauses of that
  dependency are not assumptions of this theorem.
- Sheaf.AlgebraicGeometry.StablePointedCurve: IsStablePointedCurve, including
  the geometric component and marking convention; its source and nodal-fibre
  dependency were read. HasNodalGeometricFibres includes connectedness.
- Mathlib.AlgebraicGeometry.Scheme: Scheme and Scheme.Hom.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback,
  pullback.fst, pullback.snd, pullback.lift and pullback.map.
- Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism: IsProjectiveBundle, with
  its finite-type quasi-coherent projective-bundle presentation.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: Flat, its full affine signature
  and stalkwise characterization.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  LocallyOfFinitePresentation, with quasi-compact and quasi-separated clauses
  for global finite presentation.
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace: ProjectiveLine, the
  existing abbreviation of projective space with two homogeneous coordinates,
  and its canonical structure map. No alternative projective line is defined.
- Mathlib.CategoryTheory.FiberedCategory.BasedCategory and
  Mathlib.CategoryTheory.Comma.Over.Basic: based functors, their equality of
  projections, slice categories and their forgetful projections.

The already-stated proof dependencies are imported privately:
Sheaf.TraceFormula.ProjectiveBundleProper,
Mathlib.AlgebraicGeometry.Morphisms.Proper (the proper-base-change match),
Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange,
Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry, and
Sheaf.AlgebraicGeometry.UniversalIsomorphismOpen. The three recently split
algebra/expansion/evaluation proof nodes have no Lean declarations yet; no
imports are invented for them. Their role is spelled out step by step in the
main theorem's proof docstring. They are proof inputs, not missing notions
needed to type the present statement.

Edge cases checked before and during statement construction:
r=0 (Fin 0 and the old-marking/disjointness conditions are empty); g=2;
empty base schemes and empty pullbacks; smooth disjoint sections; collision
with one old marking; passage through a node including a self-node; rational
tails and bridges; arbitrary and nonreduced bases; nontrivial automorphisms
of the old family. The comparison in a 2-fibre-product object is retained,
so automorphisms of the old curve do not produce a spurious stabilizer in
the represented fibre. An exceptional self-nodal rational or genus-one
component after deleting a marking would force a connected genus-one fibre,
excluded by hg; this check is retained in the proof docstring. Geometric
fields use the same universe as schemes, exactly as in the dependency,
so no independent smaller test universe makes the fibre conditions vacuous.

Searches performed with the prescribed msearch.py wrapper:

- LeanFinder: "Knudsen forgetful stabilization stable pointed moduli groupoid
  universal curve". Eight generic comma, scheme-limit and forgetful-functor
  results; none states this theorem or defines these moduli constructions.
- Loogle: "StablePointedModuli, IsStablePointedCurve,
  GroupoidTwoFiberProduct". Zero hits; StablePointedModuli is not a Mathlib
  identifier. The project declaration is used from its recorded module.
- Mathlib grep: "Knudsen|StablePointed|stabili[sz].*curve" in
  AlgebraicGeometry. Zero hits.
- LeanSearch: "Stable pointed curve with arbitrary additional section
  contraction stabilization Knudsen universal curve". Eight general results
  about universal closedness, surjectivity/base change and normalization;
  no match for the statement or its universal-curve category.
- rg over lean/WeilConjectures and lean/Sheaf with
  "Knudsen|StablePointed|stabili[sz].*curve": the recorded definitions and
  the generic-extension/isomorphism/level-parameter modules, but no
  forgetful universal-curve theorem or category with arbitrary extra section.
- grep -rn of the exact blueprint item id in lean/WeilConjectures: no hits.
- Exact auxiliary and main declaration names were checked against the
  project sources; no existing declaration is replaced.

Source check: Knudsen's primary-author paper arXiv:1106.1588v2, Introduction,
pp.1–3, explicitly defines C_{g,n} by unrestricted extra sections, defines
σ_n by forgetting that section, identifies its base change with the total
curve using slice categories, and states that contraction and stabilization
are inverse. Its §5 gives the inserted projective line at a node. This was
read online, alongside the node's complete seven-step proof and Q05's
stage-1 source report. No new source hypothesis is needed. No
STATEMENT-DISPUTED flag, statement correction or dependency repair is made.

Validation: the module is compiled with scompile.py only, in module mode,
against the live published library; expected sorry warnings alone are allowed.
The exact main signature is extracted verbatim into lean.statement. The final
required deliver2.py dry run and delivery are recorded below when complete.

## Delivery preflight tool failure

The first required deliver2.py --no-push run compiled the module and staged
exactly the report, item node and item module, but server preflight rejected
one import:

```text
(c) imports module(s) of route-pivot dropped nodes:
Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
(def-per-projective-bundle-quotient-data) (coord/route-pivot-dropped.txt)
```

This is a module-to-node alias false positive: the item's unchanged proof
step 5 explicitly uses lem-trf-projective-bundle-quotient-geometry, whose
current Lean record points to the actual theorem
AlgebraicGeometry.ProjectiveBundleQuotientGeometry.projective_bundle_quotient_geometry
in exactly that module. The dropped definition node def-per-projective-bundle-quotient-data
is an existing:true alias for TautologicalQuotient, pulledQuotient and Classifies
in the same live module, not the proof theorem used here. Its record even
explains that distinction. The module's source and the two node records were
read in full. The theorem has no other source definition in WeilConjectures
or Sheaf. Q05's accepted stage-1 review of this item expressly accepts the
projective-bundle quotient geometry as a generic scheme tool.

The final module directly imports all recorded statement-dependency modules
and retains the required plain import of the stated proof dependency. It
does not cite the dropped definition node, redefine the proof theorem,
change the proof route, or hide the required import through a larger module.
Those would evade the gate or violate the statement-stage import contract.
No launcher or repository tool was edited. The complete delivery is retained
in this sandbox for a corrected gate or module-to-node mapping.

The final scompile.py run succeeded in both sandbox and final library-module
forms (12.9 s and 13.4 s), without errors or warnings. The item copy differs
from the live node only in lean; the recorded signature is verbatim, and
all Lean lines meet the 100-character limit. A second deliver2.py --no-push
run again compiled and staged the three expected files, then failed with
exactly the same sole route-pivot import refusal quoted above. Nothing was
pushed. This persistent tool refusal prevents the required successful dry
run and therefore delivery; it needs the maintainer's gate/mapping repair.

## Retained-packet retry, 2026-10-22

The resumed worker inspected this report and retained the saved packet, then ran
`deliver2.py Q06 lem-sfb-knudsen-pointed-forgetful-universal-curve --no-push`
before attempting any change. The wrapper compiled the one delivered module
successfully against the live server library and staged exactly the report,
item node and item module. Server preflight again returned exactly the sole
route-pivot import refusal quoted above. Nothing was pushed.

Self-check against the current read clone: only `lean` differs in the node;
the main signature matches `lean.statement` verbatim; every Lean line is at
most 100 characters; both postponed theorems are named and documented. The
current stable-moduli dependency and its full pullback and 2-fibre-product
interfaces still match the saved usage. Searches of the live project source
find the required `projective_bundle_quotient_geometry` theorem only in
`Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`. Its non-dropped
proof node still records that module, while the dropped definition alias
still records the same module. The gate in `tools/stage2_delivery.py`
`route_pivot_fails` assigns whole modules to dropped nodes and rejects every
such import, without distinguishing the non-dropped theorem owner.

There is no packet repair that preserves the required direct import of this
already-stated proof dependency and passes that module-level gate. No module,
node binding, proof route or launcher tool was changed to evade the refusal.
The retained packet remains ready for another dry run after the maintainer
repairs the gate or the shared module ownership mapping.

## Dispatcher retry: current gate still refuses the required import

The next dispatcher retry on 2026-10-22 began with the saved report and the
required fresh `deliver2.py Q06
lem-sfb-knudsen-pointed-forgetful-universal-curve --no-push`. The wrapper's
single-file compile passed and its server preflight failed with the same sole
reason: the required direct import of
`Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry` is attributed to
route-pivot dropped `def-per-projective-bundle-quotient-data`. Nothing was pushed.

The current source and both node records still distinguish the required proof
theorem `lem-trf-projective-bundle-quotient-geometry` from the dropped definition
alias, while assigning both to that same module. The import is required by
stage 2 rule 7 and the item's unchanged proof dependency. Its removal, a hidden
transitive import or a copied replacement would evade the contract. Only the
item's `lean` field differs from its current repository node; its main signature
matches the saved module verbatim, and the maximum Lean line length is 89.
The packet is retained unchanged apart from this retry record. No tool or
read-only repository file was edited. The gate or ownership mapping needs
repair by its owner before the prescribed dry run can pass.

## Fresh retained-packet dry run, 2026-10-22

This dispatcher attempt began by reading the saved report and running the required
`deliver2.py Q06 lem-sfb-knudsen-pointed-forgetful-universal-curve --no-push`.
The wrapper completed its single-file compilation, staged the same three packet
files, and failed server preflight with one reason, unchanged:

```text
(c) imports module(s) of route-pivot dropped nodes:
Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
(def-per-projective-bundle-quotient-data) (coord/route-pivot-dropped.txt)
```

The current read clone confirms the conflict: stages/2-statements.md §3 rule 7
requires importing already-stated proof dependencies; the item's proof step 5
and proof_deps retain lem-trf-projective-bundle-quotient-geometry, whose Lean
record names this module. The dropped definition node is an existing alias of
three definitions in that same module. tools/stage2_delivery.py route_pivot_fails
maps each dropped node's entire module to that node and rejects the direct import,
without distinguishing the required non-dropped theorem. This is a persistent
wrong refusal of the gate, not a Lean compilation or packet-shape diagnostic.

The node copy still differs from the current repository node only in lean;
lean.statement matches the theorem signature verbatim; the maximum line length
is 89; there is no repair note for this item. No Lean source, node binding,
proof dependency, or tool was changed. Nothing was pushed. The complete saved
packet remains available for delivery once the gate or module ownership mapping
is repaired by its owner.

## Current dispatcher retry, 2026-10-22

Started with the retained report and the prescribed dry run. Its per-file compile
succeeded and preflight returned the same single module-ownership refusal:
`Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry` is attributed to
`def-per-projective-bundle-quotient-data`, a dropped definition alias. The live
non-dropped proof dependency `lem-trf-projective-bundle-quotient-geometry` still
records that exact module and the actual theorem at line 320. Stage 2 rule 7
requires its direct import. The current `route_pivot_fails` implementation
assigns each dropped node's whole module to that node, ignoring the theorem's
separate owner. Removing or concealing the import would evade that contract.

Refreshed the node copy's stale `lean_audit` from the read clone, retaining the
saved `lean` record, so the packet changes only `lean`. Its recorded signature
occurs verbatim in the saved Lean file, whose maximum line width is 89. There is
no repair note for this item. No live source, tool, or proof route was changed.
A second dry run follows this metadata refresh; delivery remains subject to the
same gate's correction by its owner.

The second dry run after the metadata refresh compiled successfully, staged
exactly the three expected files, and failed with the same sole `(c)` refusal.
Unlike the first run it reported no moved-base notice. Nothing was pushed.

## Latest retained-packet verification, 2026-10-22

The prescribed fresh dry run again compiled the retained module and failed only
preflight rule (c), attributing its required ProjectiveBundleQuotientGeometry
import to dropped alias def-per-projective-bundle-quotient-data. The current
non-dropped proof dependency still records that module; stage-2 rule 7 requires
its direct import. Inspection of route_pivot_fails confirms that it rejects
whole modules by dropped-node ownership, without distinguishing declarations.
The saved node differs only in lean, its signature matches verbatim, and its
maximum Lean line length is 89. No packet repair preserves both requirements;
no tool, live file, proof route or Lean declaration was changed. Nothing pushed.

## Retained-packet dry run and gate check, 2026-10-22

This attempt started with the saved report and the prescribed deliver2.py
--no-push. Compilation passed; the wrapper staged exactly the report, item
node and item module, then exited 1 with the same sole preflight (c) refusal:
Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry is attributed to
dropped def-per-projective-bundle-quotient-data. Nothing was pushed.

Read the current stage-2 rules, item and dependency records, required theorem
source and route_pivot_fails implementation. The non-dropped proof dependency
lem-trf-projective-bundle-quotient-geometry still owns the required theorem in
that module. Stage-2 rule 7 requires its import, whereas route_pivot_fails
rejects the entire module based on its dropped definition alias. This is a
wrong tool refusal; removing or concealing the import would not repair it.
The packet still changes only lean, its signature is verbatim, its maximum
Lean line width is 89, and no repair note is present. No tool or shared file
was modified. The saved packet is retained pending an owner repair of the gate.

## Current saved-packet retry, 2026-10-22

Started with report.md and the required deliver2.py --no-push. Its server
single-file compile passed, then preflight failed with exactly one reason:
(c) the required Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
import is attributed to dropped def-per-projective-bundle-quotient-data.
The current non-dropped lem-trf-projective-bundle-quotient-geometry record
still names that module. Stage 2 rule 7 requires its direct import; the
current route_pivot_fails gate rejects its whole module through the dropped
alias. The worker may not edit the gate or bypass this required import.

The node still differs only in lean, the recorded signature is verbatim,
and the longest Lean line is 89 characters. The current repair note exists
but concerns stage 1 re-splitting, not a stage 2 interface return. No Lean
source, node, shared repository file or tool was changed. Nothing was pushed.

## Successful retained-packet validation, 2026-10-22

The prescribed deliver2.py --no-push now succeeds: commit 18418f7f343 passes
server preflight and the per-file compile. The former module-ownership gate
refusal no longer blocks this packet. Retained the saved Lean and node unchanged.
Self-check: the node differs from the current read clone only in lean; the main
signature is verbatim; the longest Lean line has 89 characters; all recorded
statement dependencies and all already-stated proof dependencies are imported.
The current repair note concerns stage 1 re-splitting, not a stage 2 interface
return. No live source, tool, proof route or statement was changed.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
