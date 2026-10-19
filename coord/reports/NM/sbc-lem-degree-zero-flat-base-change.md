## Worker report

The module Sheaf.AlgebraicGeometry.EtaleSetDegreeZeroFlatBaseChange states degree-zero
flat base change for arbitrary étale sheaves of sets, and the smooth special case.
All theorem proofs are sorry. The canonical arrow has real data and is independent of
these postponed theorems. The node statement and dependencies are unchanged.

Hypotheses and clauses, in order:

- The four schemes and arrows are the explicit binders X Y S T and h e f g.
  `sq : ChosenCartesianSquare h e f g` contains commutativity and the chosen
  isomorphism Y ≅ pullback f g with both projection equations.
- Flatness is `[Flat f]`; local finite presentation is `[LocallyOfFinitePresentation f]`.
- Geometric reducedness of every residue-field fibre is exactly
  `hf : ∀ s : S, GeometricallyReduced (f.fiberToSpecResidueField s)`.
  No reducedness assumption on S is imposed.
- Arbitrary set-valued étale coefficients are
  `F : Sheaf T.smallEtaleTopology (Type (u + 1))`, with no algebra or torsion structure.
- Inverse image is the already defined `Scheme.etaleSetPullback`, the same left Kan
  extension followed by sheafification used by the recorded composition-and-units node.
- Direct image is `Etale.lowerStar (Type (u + 1))`, which is defined for arbitrary
  coefficient categories and is evaluation on base-changed étale objects. Its definition
  carries no Abelian or GrothendieckAbelian argument despite the surrounding source section.
- `etaleSetDegreeZeroBaseChange sq F` has source f⁻¹g_*F and target h_*e⁻¹F.
  Its body applies the inverse Hom equivalence for the f-adjunction to g_* of the
  e-unit, followed by the inverse of `Etale.squareLowerStarIso ... sq.toCommSq`.
  This inverse is precisely g_*e_* → f_*h_* for this square orientation.
  The generic squareLowerStarIso already works with Type coefficients, so no second
  definition of the direct-image comparison or dependency repair is necessary.
- The conclusion is `IsIso (etaleSetDegreeZeroBaseChange sq F)`.
- `isIso_etaleSetDegreeZeroBaseChange_of_smooth` states the same conclusion with
  `[Smooth f]` and no extra flatness/reducedness assumptions. The main docstring
  carries all six steps of the DAG proof, including the smooth reduction.
- g is an arbitrary morphism throughout: no quasi-compactness, quasi-separatedness,
  smoothness or torsion restriction appears.

Dependency declarations used:

- Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso: imports the recorded square
  notion; its abelian inverse-image comparison is unnecessary for this construction.
  Sheaf.AlgebraicGeometry.ChosenCartesianSquare provides ChosenCartesianSquare.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: AlgebraicGeometry.Flat.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  AlgebraicGeometry.LocallyOfFinitePresentation.
- Mathlib.AlgebraicGeometry.Geometrically.Reduced: AlgebraicGeometry.GeometricallyReduced.
- Mathlib.AlgebraicGeometry.Fiber: Scheme.Hom.fiberToSpecResidueField, the second
  projection of the recorded Scheme.Hom.fiber pullback construction.
- Mathlib.CategoryTheory.Sites.Sheaf: CategoryTheory.Sheaf.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits:
  etaleSetInverseImageCompositionUnits; its inverse-image implementation is
  Scheme.etaleSetPullback from Sheaf.AlgebraicGeometry.EtaleSheaves.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs:
  Etale.isContinuous_overPullback, Etale.lowerStar, Etale.lowerStarComp.
- WeilConjectures.SixFunctors.BaseChange.Square: Etale.squareLowerStarIso.
- Mathlib.CategoryTheory.Sites.Continuous: the generic continuous-site adjunction
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous.

Imports also include the published proof dependencies (étale reducedness, slicing-flat
charts, set inverse-image restriction, flat connected-fibre sections, smooth geometric
reducedness, finite-presentation stability, finite-limit preservation of base change and
quasi-compact base change). sbc-lem-smooth-criterion has no recorded module and is
not imported; it is a proof dependency, not a missing object needed to type the statement.

Edge cases checked: empty schemes and empty fibres are permitted (geometrically reduced
is not a connectedness/nonemptiness condition). Identity squares, arbitrary g, the empty
set sheaf and non-torsion/infinite set sheaves are included. Universes are explicitly
bound: schemes in u and coefficient sets in u+1, matching the existing set inverse image;
no equality between unrelated universes is imposed and no implicit variables are used.
The stronger flat-finite-presentation theorem in the upstream DegreeZero module is
restricted to Grothendieck abelian coefficients; it is not the arbitrary-set statement.

Searches:

- msearch leanfinder: “Etale sheaves of sets degree zero flat base change geometrically
  reduced fibres”: 8 results about étale/formally étale ring maps, no match.
- msearch loogle: `"baseChange", "Sheaf"`: 2 precoverage sheaf-condition results, no match.
- msearch grep: `baseChange.*[Ss]heaf|geometricallyReduced`, AlgebraicGeometry:
  14 results about geometric reducedness and affine spaces, no set exchange theorem.
- rg of WeilConjectures and lean/Sheaf for the item id, degree-zero base change,
  flat isomorphisms and set pullback/base change: upstream
  SixFunctors.Etale.SmoothBaseChange.DegreeZero gives only the abelian version.
  Read its actual coefficient binders, not just its blueprint label.
- Read actual definitions/signatures and docstrings of all recorded statement
  dependencies, including the server source of UpperLowerStar.Defs via scompile --source.
- rg of the chosen new declaration names in the source tree, lean/Sheaf and
  dag/lean_names_upstream.json: no collisions.

Sources checked directly: Stacks etale-cohomology.tex labels
lemma-base-change-f-star-general and lemma-fppf-reduced-fibres-base-change-f-star
(Tags 0EZX and 0EYS), and blueprint sec-smooth-base-change/sk-prop-deg0/_section.md.
No mathematical statement fault or dispute was found.

Validation: the complete file compiles cleanly through the prescribed scompile.py
wrapper (2026-10-15): sandbox probe 3.2 seconds, library-path probe 3.6 seconds.
The wrapper's local side-project overlay is authorized by the human's parallel-landing
update; the earlier report's claimed local-compilation policy blocker is superseded.
No compiler or delivery tool was modified. The required deliver2.py --no-push dry run
is performed before handing this sandbox to the independent second reader.

## Earlier second reading (a previous round; superseded)

Independent review on 2026-10-15, with the sandbox node and module open. I read
Stacks etale-cohomology.tex, lemma-fppf-reduced-fibres-base-change-f-star (0EYS),
lemma-base-change-f-star-general (0EZX), and the unit sk-prop-deg0/_section.md.
0EYS introduces arbitrary schemes, a Cartesian square, flatness, local finite
presentation and geometrically reduced fibres; there is no ambient Noetherian,
separatedness, quasi-compactness or coefficient restriction to add.

Object/hypothesis/conclusion checklist, in node order:

1. Schemes X, S, T, Y and arrows f, g, h, e: exactly the explicit Scheme.{u}
   binders and morphism binders in both theorems. Verdict: exact.
2. Cartesian identification Y ≅ X ×_S T: `sq : ChosenCartesianSquare h e f g`.
   I opened BaseChangeInverseImageIso.lean and ChosenCartesianSquare.lean:
   the latter extends CommSq and has isoPullback, hom_fst and hom_snd. Thus this
   is an identification respecting both projections, not a bare scheme iso.
   Verdict: exact reuse of the dependency's square datum.
3. f flat: `[Flat f]`. I read Mathlib Morphisms/Flat.lean: its affine definition
   is identified with flat stalk maps by Flat.iff_flat_stalkMap, as recorded in
   def-weil-flat-morphism. Verdict: exact, no faithful-flat/surjective assumption.
4. f locally of finite presentation: `[LocallyOfFinitePresentation f]`.
   Mathlib Morphisms/FinitePresentation.lean tests affine ring maps; the recorded
   def-sbc-locally-finite-presentation match identifies this with affine
   neighbourhoods at every point. Verdict: exact; no global finite presentation.
5. Every residue-field fibre geometrically reduced:
   `hf : ∀ s : S, GeometricallyReduced (f.fiberToSpecResidueField s)`.
   I read Mathlib Fiber.lean: fiber is pullback along S.fromSpecResidueField s,
   and fiberToSpecResidueField is its second projection. Reduced.lean defines
   GeometricallyReduced by reducedness after all field-valued base changes.
   This is reducedness over κ(s), not reducedness of the total space, not just
   ordinary reducedness, and not the set of geometric lifts. The geometric-fibre
   dependency's recorded pullback is the same construction after algebraic
   closure, while this hypothesis uses the ordinary fibre dependency and the
   geometrically-reduced clause of def-pc-geometrically-irreducible. Verdict: exact.
6. Every sheaf of sets F on T_et:
   `F : Sheaf T.smallEtaleTopology (Type (u + 1))`.
   I read the sheaf-of-sets dependency record and the actual EtaleSheaves.lean
   set pullback. No additive, module, torsion, finiteness or constructibility
   condition is present. Verdict: exact under the recorded size convention.
7. Specified inverse images, compositions and units: the map uses the existing
   Scheme.etaleSetPullback and the generic sheafAdjunctionContinuous. I opened
   EtaleSetInverseImageCompositionUnits.lean: these are exactly its inverse image
   and unit, including its composition construction. Verdict: same construction.
8. Direct image evaluates F on base-changed étale objects: Etale.lowerStar.
   I read the recorded continuity node and UpperLowerStar.Defs, also through
   `scompile.py --source`. lowerStar is sheafPushforwardContinuous along
   MorphismProperty.Over.pullback @Etale ⊤, with no inherited abelian argument.
   Verdict: exact, applicable to sets and arbitrary g.
9. Canonical β has source f⁻¹g_*F and target h_*e⁻¹F: these are precisely the
   definition's displayed source and target. Its data are homEquiv.symm applied
   to lowerStar g mapped over the e-unit, followed by squareLowerStarIso.inv.
   I read Square.lean: for sq.toCommSq its hom goes h_* then f_* to e_* then g_*;
   hence its inverse is the required g_*e_* → f_*h_*. Verdict: the actual
   adjoint transpose in the node, not an arbitrary map with those endpoints.
10. β is an isomorphism: `IsIso (etaleSetDegreeZeroBaseChange sq F)` in
    isIso_etaleSetDegreeZeroBaseChange_of_flat. Verdict: exact.
11. Smooth special case: isIso_etaleSetDegreeZeroBaseChange_of_smooth uses
    `[Smooth f]` with the same square and arbitrary F, and the same conclusion.
    I read the Smooth class signature and the recorded def-sbc-smooth-morphisms
    identification. No additional flatness/reducedness binders are required.
    Verdict: exact second clause of the same node.
12. No restriction on g and no torsion hypothesis: g is an arbitrary morphism;
    coefficients are Type, with no extra instances. Verdict: exact.

Edge cases: empty schemes and empty fibres are allowed; reducedness requires
neither a point nor connectedness. Initial and terminal set sheaves are allowed
(the initial sheaf has its required singleton value on an empty étale object,
not a constant-empty presheaf). Identity squares are allowed. No cover index,
cohomological degree n, integer modulus, characteristic, or nonzero-ring
hypothesis occurs. Universes are explicitly bound; schemes in u and sets in u+1
are exactly the dependency's convention. No unbound variable or extra universe
equality occurs, and smaller sets are included by lifting to that universe.

Independent H4 searches used different words from the worker:

- msearch leanfinder, `pushforward inverse image exchange isomorphism for set
  valued sheaves flat morphism reduced fibers`: eight hits, concerning module
  pushforward composition/congruence or topological presheaves, no exact match.
- msearch loogle, `"baseChangeMap"`: zero hits.
- msearch grep, `exchange|beckChevalley|baseChangeMap`: generic exchange hits,
  no matching étale theorem. Focused rg on Mathlib/CategoryTheory/Sites,
  WeilConjectures and lean/Sheaf for baseChangeMap, exchange, set base change,
  and the proposed names found no duplicate arbitrary-set exchange theorem.
- I opened upstream SmoothBaseChange/DegreeZero.lean, rather than trusting its
  blueprint label. isIso_baseChangeMap_app_of_flat explicitly takes
  `F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`; the surrounding generic
  construction assumes abelian/Grothendieck abelian coefficients. It cannot
  replace this arbitrary-set statement or its canonical arrow. The existing
  squareLowerStarIso does work with sets and is reused, not redefined.

H5–H9: the sole new definition has actual adjunction/comparison data, no sorry
or choice from an uncharacterized existence theorem. Both theorems are sorry;
there are no proved theorems. Each declaration has a source and blueprint
identifier. The main docstring follows all six node proof steps: connected-fibre
charts, the first sections bijection, base change of charts, the second bijection
and canonical-map equation, overlap injectivity/gluing, then smooth reduction.
The smooth theorem's docstring supplies its specialization proof. No private
notion, file-local notation, or overlong line occurs. Proof dependency imports
are retained; the unstated smooth-criterion proof dependency is documented by
the worker and is not needed to type either statement. There are no new nodes,
dependency modules, or statement_change in this packet, so H12/H13 and a citer
correction audit are inapplicable.

Mismatches and changes: none found in the mathematical statement or module.
I left the Lean and node unchanged and appended this independent review.
The node differs from the repository only in lean; lean.statement is verbatim
the theorem signature, checked mechanically. Prescribed scompile.py compiled
the delivered file cleanly in sandbox and library-path modes (3.2 s and 3.5 s),
with no errors or warnings. An initial invocation with a path relative to the
read-only repository failed to locate the sandbox file; rerunning with its
absolute sandbox path succeeded. No compiler tool was changed.

## Repair note

The returned packet contained the complete module, node lean record, and worker report. I revalidated the same files after the reviewer's apply-fixes packaging return; no statement, dependency, or Lean correction was required. The prescribed stage-2 dry run below was rerun on this repaired packet.

## Second reading by NM

This is the current independent second reading (2026-10-15); the earlier readings
above describe the packet before this repair. I read the node, all its statement
dependency records, their actual relevant declarations, Stacks etale-cohomology.tex
0EYS/0EZX, and the blueprint unit sk-prop-deg0. The source assumes arbitrary schemes:
no ambient Noetherian, separated, quasi-compact, characteristic or torsion condition.

Object/hypothesis/conclusion checklist, in node order:

1. Four schemes X,Y,S,T and morphisms h,e,f,g: explicit Scheme.{u} and morphism
   binders in both theorems. Exact.
2. Cartesian square with chosen identification respecting both projections:
   `sq : ChosenCartesianSquare h e f g`. Opened ChosenCartesianSquare and the
   recorded BaseChangeInverseImageIso module: the structure extends CommSq and
   includes isoPullback, hom_fst and hom_snd. Exact; no bare unrelated isomorphism.
3. Flat f: `[Flat f]`, the existing affine-local Flat predicate, equivalent to
   flat stalk maps. Exact, without surjectivity or faithful flatness.
4. Locally finitely presented f: `[LocallyOfFinitePresentation f]`, whose
   affine ring maps are finitely presented. Exact, without global qc/qs.
5. Every residue-field fibre geometrically reduced:
   `hf : ∀ s : S, GeometricallyReduced (f.fiberToSpecResidueField s)`.
   Read Fiber and Geometrically/Reduced: fibre is pullback along the canonical
   residue-field point; its second projection defines its residue-field structure.
   GeometricallyReduced tests reducedness after field base change. This uses the
   ordinary fibre with geometric reducedness, as the node says; the separate
   geometric-fibre dependency is not the set of geometric lifts. Exact.
6. Every sheaf of sets on T_et: `F : Sheaf T.smallEtaleTopology (Type (u + 1))`.
   Matches the existing Sheaf and set inverse-image size convention. Exact;
   no additive, module, finiteness or constructibility requirement.
7. Inverse images and units: existing Scheme.etaleSetPullback and
   Etale.setUpperLowerAdjunction, read in EtaleSheaves, composition-units, and
   BaseChangeMapAbelianAndSets. The adjunction is the same continuous-site
   sheafification/left-Kan-extension adjunction. Exact.
8. Direct image: existing Etale.lowerStar is continuous pushforward along
   MorphismProperty.Over.pullback, evaluating on base-changed etale objects.
   Its definition does not use the ambient abelian instances. Exact.
9. Canonical arrow f⁻¹g_*F → h_*e⁻¹F: now `Etale.setBaseChangeArrow sq F`.
   I opened its definition: inverse image f applied to g_* of the e-unit,
   followed by the two direct-image composition comparisons, followed by the
   f-counit. By the defining adjunction hom equivalence this is exactly the
   node's adjoint transpose. Its endpoints are precisely those displayed here.
10. Isomorphism: `IsIso (Etale.setBaseChangeArrow sq F)` in the flat theorem.
    Exact, with F quantified after the hypotheses.
11. Smooth special case: second theorem has `[Smooth f]`, the same square and
    arbitrary F, and the identical IsIso conclusion. Read Mathlib Smooth's
    affine smooth-ring-map definition and the recorded 02H6 equivalence. Exact.
12. Arbitrary g and no torsion: no extra binder or instance restricts g or F.
    Exact.

Edge cases: empty schemes and empty fibres are included; geometric reducedness
requires no nonemptiness. Identity squares and initial/terminal set sheaves are
included (the initial sheaf has singleton sections on the empty object).
There is no index set, cohomological n, modulus, characteristic, or nonzero-ring
binder. All universes and variables are bound: schemes in u, sets in u+1,
matching the recorded inverse image; no additional equality of universes.

Independent searches (different wording from the worker): msearch leanfinder
“Beck Chevalley exchange for inverse image pushforward of set valued etale
sheaves with reduced fibers” returned eight module pushforward/restriction hits,
no exact theorem; loogle `"baseChangeMap"` returned zero hits; grep
`exchange|beckChevalley|baseChangeMap` returned unrelated generic hits.
Focused rg across Mathlib Sites, upstream WeilConjectures and project lean/Sheaf
found the important existing `Etale.setBaseChangeArrow` in
BaseChangeMapAbelianAndSets. I read its actual definition and owning node
sbc-def-base-change-map, whose lean.declarations records this helper. The
upstream SmoothBaseChange/DegreeZero flat theorem instead explicitly quantifies
ModuleCat coefficients, so does not supply the arbitrary-set theorem.

Mismatch and repair: H4, the packet duplicated an already landed canonical set
exchange under etaleSetDegreeZeroBaseChange. Removed that definition, imported
BaseChangeMapAbelianAndSets, used Etale.setBaseChangeArrow in both conclusions,
removed the duplicate from lean.declarations, and added the landed owning node
sbc-def-base-change-map to stmt_deps (brief-stage2 §5). Updated lean.statement
verbatim from the repaired signature. The natural-language statement is unchanged;
no statement_change or citer correction audit is required. No new nodes or
new dependency modules are supplied. Existing dependency modules were checked
against their node signatures; no dependency interface repair is needed.

H5–H9: no new definitions remain, both theorem proofs are sorry, no theorem is
proved, every declaration has source and blueprint docstrings, and the main
proof docstring follows all six DAG steps (charts, first sections comparison,
base change, second comparison and unit equation, overlap gluing, smooth case).
The existing proof imports are retained. No private definition, local notation,
overlong line, unbound variable or universe remains.

Validation of the repaired file: prescribed scompile.py passed sandbox (3.1 s)
and library-path (3.3 s) checks without errors or warnings. lean.statement was
extracted verbatim from the repaired theorem signature.
