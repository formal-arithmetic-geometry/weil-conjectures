## What changed

Proved the body of `TopCat.topological_filtered_cohomology`, with its signature unchanged,
by induction on the derived degree and transport of colimit universal properties along
a natural isomorphism. The existing, proved
`CategoryTheory.Functor.preservesColimitsOfShape_rightDerived_succ` packages the
functorial injective embedding, exact-colimit, and long-exact-sequence steps of 01FF.
The item's node now records this actual route. All new proof imports are private.

Added three modules, each with one public theorem and a matching node:

- `Sheaf.Topology.AbelianSectionsFilteredColimit`: completely proved preservation of
  directed colimits by sections on compact opens. Its private helpers adapt the existing
  proved sets-section argument to abelian groups directly, using concrete stalk colimits,
  eventual equality, finite compact refinements, and gluing. This avoids any detour through
  constant-integer module sheaves.
- `Sheaf.Topology.DirectedInjectiveDerivedSectionsAcyclic`: the acyclicity part of 01FF,
  restricted to injective diagrams and positive derived sections, with the actual directed
  index category. This is one remaining named obligation.
- `Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections`: the natural Ext-to-derived-
  sections comparison needed because Mathlib's cohomology presheaf is defined using Ext.
  This is the other remaining named obligation.

Compiled the four files together cleanly through `lcompile.py --all`. Checked edge cases:
empty opens have zero sections, empty finite covers cause no nonempty-index assumption,
I is nonempty but need not have a least element, and no separation condition on X is used.
The degree-zero proof is a full Lean proof, including those cases. No existing definition,
statement, target, or original public import was changed. No blueprint unit step is bypassed:
`sk-thm-curveestimate` realizes its statement at `thm-sc-proper-cohomology`, not here.

## Proved and sorry left

Closed the item's only original sorry:
`TopCat.topological_filtered_cohomology`, node
`lem-sc-topological-filtered-cohomology`. This is a decomposition into two strictly
smaller obligations, not a claim that the target closure is already sorry-free.

Also completely proved `TopCat.abelianSections_preservesDirectedColimits`, node
`lem-sc-topological-abelian-sections-filtered-colimit`, including all five private helpers.

Exactly two sorries are added, each the entire proof of one named public theorem:

- `TopCat.directedInjective_isZero_rightDerived_sections`, node
  `lem-sc-directed-injective-derived-sections-acyclic`: only positive-degree vanishing
  for colimits of injectives, not commutation of arbitrary cohomology with arbitrary diagrams.
- `CategoryTheory.Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived`, node
  `lem-sc-site-cohomology-right-derived-sections`: comparison of two models of cohomology,
  with no filtered diagrams or compactness hypotheses.

Both have full sourced proof plans in their docstrings and nodes. Neither repackages the
original cohomology-colimit theorem. No sorry is left inside the item's proof, a definition,
or any private helper. The induction and natural-isomorphism transport are complete Lean.

## No longer needed

Removed these five original private proof imports from the item:

- `Sheaf.CategoryTheory.ModuleDirectedColimitUnderlyingSets`
  (`lem-weil-pbc-module-directed-colimit-underlying-sets`): entirely unnecessary on this route.
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
  (`lem-weil-pbc-right-derived-universal-delta-functor`): the proved generic successor lemma
  supplies the exact induction step instead.
- `Sheaf.CategoryTheory.SiteCechVanishingCriterion`
  (`lem-weil-pbc-site-cech-vanishing-criterion`): no direct use in the main proof; still needed
  by the new acyclicity node's proof plan, so not globally pruned.
- `Sheaf.Topology.FilteredInjectiveCechAcyclic`
  (`lem-sc-topological-filtered-injective-cech-acyclic`): replaced by the focused directed
  acyclicity obligation. Its extra Cech conclusion is not needed by the main induction.
- `Sheaf.Topology.SheavesDirectedColimitSections`
  (`lem-weil-pbc-sheaves-directed-colimit-sections`): no theorem dependency; its proved private
  argument was adapted to abelian groups and independently compiled in the new section module.

The main node no longer directly depends on
`lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`,
`lem-weil-pbc-filtered-colimit-abelian-groups-exact`,
`lem-weil-pbc-grothendieck-functorial-injective-embedding`, or
`lem-weil-pbc-derived-functor-injective-vanishing`. These ingredients remain needed through
Mathlib instances, the generic successor theorem, or the acyclicity proof plan; they are
not claimed globally redundant. The two cohomology definition nodes remain statement
dependencies. No other existing module was modified.

## Where the brief, the DAG or earlier work was wrong

The existing `FilteredInjectiveCechAcyclic` Lean statement takes a diagram over
`Discrete I`, although its node and the 01FF argument require a directed diagram over I.
A discrete diagram has coproduct as its colimit and cannot be used as the directed-colimit
acyclicity premise. The new focused node uses I itself. This delivery does not modify or
claim the existing module; its replacement is a strict subargument of the main proof.

Mathlib's cohomologyPresheafFunctor is an Ext construction; the planned right-derived
induction cannot directly conclude the displayed canonical Ext comparison without a
natural comparison. The existing `def-weil-pbc-sites-and-cohomology` notes already defer
this bridge to stage 3. The new comparison module states it explicitly. Its universes
are all equal, avoiding the independent-universe problem recorded in the existing site
injective Cech module. If that module is used in the acyclicity proof, specialize its
coefficient and Ext universes equally, as its warning requires.

A further attempt to close the acyclicity proof reached finite Cech products and compact
finite intersections, but the precoverage-topology transport and product-cone naturality
were not completed. No partial private proof or uncompiled code enters the delivery.

WANTED: literature/stacks-project/cohomology.tex, Lemmas 01FF and 01EW, and
literature/stacks-project/sites-cohomology.tex, Section 01FT, for the two new obligations.
These source files are absent locally. The corresponding official Stacks pages 01FF and
01FT were read; node proof_origin is marked agent for the elaborated proof plans.
LeanSearch was attempted and returned Internal Server Error; other search kinds worked.

## New nodes

`lem-sc-topological-abelian-sections-filtered-colimit`:
`dag/nodes/sec-curve-estimates/lem-sc-topological-abelian-sections-filtered-colimit.json`;
module `Sheaf.Topology.AbelianSectionsFilteredColimit`, fully proved degree-zero preservation.

`lem-sc-directed-injective-derived-sections-acyclic`:
`dag/nodes/sec-curve-estimates/lem-sc-directed-injective-derived-sections-acyclic.json`;
module `Sheaf.Topology.DirectedInjectiveDerivedSectionsAcyclic`, sourced 01FF step-4 obligation.

`lem-sc-site-cohomology-right-derived-sections`:
`dag/nodes/sec-curve-estimates/lem-sc-site-cohomology-right-derived-sections.json`;
module `Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections`, natural comparison obligation.

No change record is needed: no existing signature or definition was changed.


## Second reading by E2

1. Compared the main module with its repository version using a textual diff and
   checked every delivered module. The sole existing declaration's signature is
   byte for byte unchanged. Only its proof, proof docstring, and private imports
   changed. The other three modules are new and add no definitions. No change
   record is required. Verdict: pass.

2. Recompiled all four files in import order with `lcompile.py --all`; no errors
   or warnings. Searched all delivered Lean files for forbidden declarations and
   checked the two remaining sorries are exactly the named public obligations
   listed above. Scratch copies with `#print axioms` give only `propext`,
   `Classical.choice`, and `Quot.sound` for
   `TopCat.abelianSections_preservesDirectedColimits`; the other three public
   theorems additionally use `sorryAx`. No hollow definitions or private holes.
   Verdict: pass as a decomposition; the original hole is closed, two are added,
   so the delivered holes have net -1. This is not a sorry-free target proof.

3. Read both split statements, docstrings, and nodes. The injective-diagram
   restriction is strictly smaller than arbitrary cohomology-colimit preservation;
   the natural comparison has no colimit or compactness hypothesis. Reviewed empty
   opens, empty covers, singleton directed indices, zero diagrams, degree zero,
   and general nonterminal site objects. The sections proof handles finite empty
   covers using nonemptiness of I for its common upper bound. Compact overlaps and
   a finite cover suffice; no Hausdorff or least-index condition is hidden.
   Searched with LeanFinder for derived additive coyoneda and compact-open injective
   colimit acyclicity, with Loogle for Ext functors, and with grep/rg for flasque
   colimits and cohomology/right-derived comparisons. The existing proved
   `Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ` applies only
   to global cohomology at a terminal object in positive degrees and does not
   supply the natural all-object, all-degree comparison here. No exact existing
   replacement was found. Reviewed the official Stacks 01FT definition and the
   finite-Cech argument of the sourced plans. Neither open obligation can be
   closed in a few minutes from the available declarations. Verdict: pass.

4. Read the complete main induction and the complete compact-open sections proof.
   The main proof genuinely combines degree zero, the generic successor theorem,
   acyclicity, and natural-isomorphism transport; neither obligation restates it.
   Checked all original proof dependencies against `No longer needed`, including
   ingredients now supplied transitively by instances or the generic successor.
   The five discarded private imports are all named there. The unit record
   `dag/units/sk-thm-curveestimate.json` realizes its statement through
   `thm-sc-proper-cohomology`; none of its realized steps is bypassed.
   Verdict: pass. Removed an unused cohomology import from two new modules.

5. Checked the existing node diff is limited to allowed proof/Lean fields, and
   checked all three new nodes' statement, source, searches, creation, blueprint,
   chapter, unit, and verbatim Lean signatures. Main `proof_deps` is precisely
   the four nodes whose declarations the proof uses. The open nodes give the
   sourced plans for their remaining proofs. Verdict: pass.

Second-reading changes: removed the unused public import
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` from the new modules
`AbelianSectionsFilteredColimit` and `DirectedInjectiveDerivedSectionsAcyclic`;
recompiled the complete set and performed axiom probes; corrected the report's
path for the discarded module-directed-colimit import and recorded the honest
hole accounting. No proof body, statement, or definition needed repair.
