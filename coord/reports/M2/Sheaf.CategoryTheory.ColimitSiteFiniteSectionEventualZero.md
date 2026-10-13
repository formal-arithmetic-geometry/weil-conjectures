## What changed

Reduced `CategoryTheory.colimit_site_finite_section_eventual_zero` to two independent
raw abelian section computations, with its signature and public imports unchanged.
Added proof-only imports of `ColimitSiteRawAbelianSectionDiagram`,
`ColimitSiteRawAbelianSectionSheaf`, and `ColimitSiteRawAbelianSectionEvaluation`.
The first constructs the actual Kan diagram and is fully proved, by adapting the
already proved type-valued diagram's categorical argument to abelian groups.
The latter two isolate the finite-cover sheaf condition and the raw pointwise
Kan evaluation calculation respectively. Their statements assert neither the
original eventual-zero conclusion nor its comparison-bijectivity parent.

The item proves the adjunction comparison after sheafification, takes its colimit
on connected Under i, cancels the two sheafification units, and compares the
supplied cocone legs with the raw evaluation legs. It then cancels group
isomorphisms and applies Mathlib's same-stage filtered-set equality criterion
to x and zero. The new diagram and the entire combining proof compile.

Sources read: Stacks 0A35, `lemma-compute-pullback-to-limit`, especially the
presentation, finite-cover equalizer, and adjunction paragraphs
(https://stacks.math.columbia.edu/tag/0A35), and 03CO
(https://stacks.math.columbia.edu/tag/03CO). The raw diagram's proved code adapts
`Sheaf.CategoryTheory.ColimitSiteRawSectionDiagram`; the private adjunction
helpers adapt `Sheaf.CategoryTheory.ColimitSiteSetSectionEventualEquality`.
Neither existing module is imported or modified.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.colimit_site_finite_section_eventual_zero`
(node `lem-weil-pbc-colimit-site-finite-section-eventual-zero`).
No sorry remains in the item's module.

Also proved:
`CategoryTheory.colimit_site_raw_abelian_section_diagram`
(node `lem-weil-pbc-colimit-site-raw-abelian-section-diagram`).
All private helpers in the item and the diagram module are proved.

Added two holes, both exactly `:= by sorry` in separate new modules:

- `CategoryTheory.colimit_site_raw_abelian_section_isSheaf`
  (node `lem-weil-pbc-colimit-site-raw-abelian-section-sheaf`).
- `CategoryTheory.colimit_site_raw_abelian_section_evaluation`
  (node `lem-weil-pbc-colimit-site-raw-abelian-section-evaluation`).

This is a decomposition, not a sorry-free proof of the transitive closure:
one original hole closed and two strictly separate raw computations added.
Evaluation has no finite-cover hypotheses and allows an arbitrary abelian
presheaf target T. Sheafness has no alpha, supplied section diagram D,
comparison cocone K or eventual-zero conclusion. The adjunction identification
which combines these independent statements is proved in the item.

Edge cases checked mathematically: a constant identity diagram reduces the raw
Kan diagram and evaluation to the ordinary stage presheaf and its sections;
zero abelian sheaves give zero groups; an empty cover uses the zero group as the
empty matching-family limit. There is no source object U on an empty category,
so evaluation is vacuous there. The sheafness statement is still meaningful for
an empty limit category and then has no covers to test. Abelian Kan elements are
finite sums, not necessarily single generators; both docstrings explicitly
handle finite sums, linearity relations and common-stage refinement. No object
is defined by choosing an arbitrary witness of an unproved mere existence claim.

Validation: all four delivered modules compile through lcompile.py in import
order, and all lines have at most 100 characters. No existing definition,
signature, universe or visibility changed; no forced adaptations.

## No longer needed

Removed the redundant proof-only imports
`Mathlib.CategoryTheory.Limits.Types.Filtered` and
`Mathlib.CategoryTheory.Limits.Connected`; both are already supplied through
`Mathlib.CategoryTheory.Filtered.Final`.

No original import was removed: all original public imports remain, preserving
the item's public interface. A trial extra import of
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic` was removed; the final
proof uses `Types.FilteredColimit.isColimit_eq_iff'` after forgetting abelian
groups, not the two-stage concrete equality criterion.

The original route's general initial-functor criterion
`lem-weil-pbc-initial-functor-cofiltered-criterion` is no longer a dependency of
this item's route. The raw evaluation docstring constructs explicit inverse
maps by lifting finite Kan relations, without calling a finality criterion.
Under i filteredness is supplied directly by Mathlib's filtered-comma instance.
This is pruning from this item, not a claim that no other target branch uses
the criterion.

The old direct dependencies
`def-weil-pbc-arrows-functor`, `def-weil-pbc-finite-precoverage`, and
`lem-weil-pbc-filtered-colimits-commute-finite-limits` are removed from this
node's direct `proof_deps`. They now belong to the appropriate raw statements;
they remain needed indirectly and are not reported as globally pruned.
The abelian universality, finite-section colimit-presentation, finite-unit
zero-detection and abelian eventual-equality modules are deliberately not
imported: their current proofs reach this item and would make an import cycle.
No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item's original four-step proof plan includes the presentation construction,
sheaf equalizers and adjunction comparison, but its eight named dependencies
provide only general definitions, adjunctions and filtered-colimit tools.
They do not state the independent raw abelian construction or evaluation.
The corresponding existing raw section modules are type-valued and their
statements cannot be applied to abelian left Kan extensions simply by forgetting:
forgetting does not preserve arbitrary Kan colimits. Thus the delivery states
the two missing abelian raw computations instead of importing an inappropriate
set-valued lemma or a downstream zero-detection result.

The ancestry tool returns no blueprint ancestor for this newly created item's
current metadata. Each new node records the exact steps of this item's
presentation argument that it refines. All share chapter sec-proper-base-change
and unit sk-thm-p1, whose realized projective-line route is unchanged.
LeanSearch returned Internal Server Error and is recorded as unavailable.
LeanFinder and grep found supporting Mathlib tools, not an exact abelian
varying-site computation. Blueprint search found no raw abelian section node.

## New nodes

`lem-weil-pbc-colimit-site-raw-abelian-section-diagram` records the proved
explicit left Kan construction, coherence of stage transitions by adjunction
injectivity, and naturality of the raw comparison. Its new module is
`Sheaf.CategoryTheory.ColimitSiteRawAbelianSectionDiagram`.

`lem-weil-pbc-colimit-site-raw-abelian-section-sheaf` records only the finite-cover
sheaf condition for the supplied raw abelian diagram. Its new module is
`Sheaf.CategoryTheory.ColimitSiteRawAbelianSectionSheaf`.

`lem-weil-pbc-colimit-site-raw-abelian-section-evaluation` records the pure raw
pointwise Kan calculation at V_i(U), including the coprojection formula into an
arbitrary target presheaf. Its new module is
`Sheaf.CategoryTheory.ColimitSiteRawAbelianSectionEvaluation`.

No change record is needed: every existing statement and definition is unchanged.

## Second reading by M2

1. Compared the item with the repository using diff and checked its entire
theorem signature byte for byte: unchanged, including universes and visibility.
Only proof-only imports, private proved helpers and the original proof changed.
The other three delivered modules are new; no existing definition changed.
Verdict: pass; no change record or forced adaptation is needed.

2. Read all four modules and their combining argument. The diagram uses actual
Mathlib Kan extensions, universal units and desc maps; the item only eliminates
existentials inside a theorem proof. There is no hollow definition or arbitrary
existence-based data definition. Exactly the two reported public named theorems
contain sorry; no forbidden axiom, unsafe, opaque, extern or implemented_by occurs.
All modules compile locally. Explicit axiom probes and delivery preflight check
the declarations; sorryAx is expected only through the two reported raw holes.
Verdict: pass as a decomposition, not a closed import closure.

3. Read the split statements, full docstring arguments and node records. Raw
sheafness asserts only descent; raw evaluation computes a presheaf Kan colimit
without finite-cover hypotheses or a sheaf target. Neither repeats the original
zero-detection assertion. Checked constant identity diagrams, zero groups, empty
covers, and absence of U in an empty source category. Finite sums and finite
relation witnesses in abelian Kan colimits are handled explicitly. The stage
unit equations determine the transition maps by adjunction injectivity.
Verified the cited presentation/sheaf/adjunction argument at Stacks 0A35 and
the abelian presheaf/sheaf colimit facts at 03CO. New LeanFinder searches used
“evaluation at an object from one stage” and “finite covering equalizer”; grep
searched IsLeftKanExtension/colimit and isSheaf_pointwiseColimit. Read the existing
ColimitStageKanCocone, FinitePresieveFilteredColimit and abelian stage-image sheaf
interfaces: these are set-valued, fixed-site, or concern a different subpresheaf,
not replacements for either raw abelian statement. Verdict: true, needed and
strictly separate parts of the argument; neither hole has a short available proof.

4. The proved adjunction comparison and connected colimit argument cancel
sheafification units before raw evaluation and Mathlib filtered equality are used.
No downstream zero-detection result is imported. Checked sk-thm-p1.realized: none
of its statement or step nodes is bypassed. All four old direct dependencies
removed from proof_deps are now explicitly accounted for under No longer needed;
three remain indirect dependencies of raw lemmas, and only the initiality
criterion leaves this route. Tested removing Grp.FilteredColimits and making the
diagram's Grp.Colimits private: these are required by public signatures through
sheafification and Kan-existence instances, so retained them. Removed only the
two redundant proof imports named above. Verdict: pass.

5. Checked that existing node changes are restricted to proof, proof_deps and
proof_origin. Every new node contains source, creation, blueprint, chapter/unit,
searches and Lean metadata. Its stored Lean statement equals the actual signature,
and every proof_deps list equals the union of step uses. The existing node follows
the four compiled proof steps and accurately distinguishes the two open raw
computations. Corrected new-node prose from Arrow(Set) to Arrow(Ab), matching Lean.
Verdict: pass.

Second reading changed two redundant proof imports, clarified all removed direct
dependencies in the report, corrected the new nodes' arrow-category wording, and
added this independent review. No proof or signature repair was necessary.
