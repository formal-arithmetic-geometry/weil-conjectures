## What changed

Replaced the sorry in AlgebraicGeometry.openModuleCohomology_directedColimit with a
complete Lean proof, with exactly the existing signature and public imports.
The proof establishes section preservation, inducts using the existing derived-functor
successor theorem, verifies its acyclicity premise by abelian-sheaf cohomology and the
exact-composite comparison, and extracts representatives and eventual zero from the
concrete colimit universal property. Updated the original DAG node's proof, proof_deps
and proof_origin to this route. No definitions, interfaces, or other modules changed.

Only proof imports were added: the compact-open sections theorem, topological filtered
cohomology, injective-module abelian acyclicity, object-cohomology/derived-sections
comparison, exact-composite comparison, and derived-colimit successor theorem; Mathlib
concrete colimits and HasExt, and the proved upstream module-sheaf Grothendieck instances.

The replacement is valid at q=0, on the empty open, on a noncompact whole scheme, and
for directed preorders without antisymmetry. Every cocone remains arbitrary, as in the
original statement; colimit choices only occur in the successor theorem's premise.

## Proved and sorry left

Closed: AlgebraicGeometry.openModuleCohomology_directedColimit
(lem-weil-pbc-qs-scheme-cohomology-directed-colimit): 1 of 1 original holes.
No sorry remains in the delivered module. Added holes: none. Split off: none.
This is a proof from existing named declarations, not a claim that all imported
mathematics is now sorry-free. In particular exists_rightDerived_exact_comp_iso is
an existing unproved declaration; the delivery adds no replacement statement for it.
Single-file compilation succeeds without warnings (17.2 seconds after import pruning).
The first dry run printed OK: local compilation and preflight passed except for the
second reading, intentionally reserved for the independent reader; nothing was pushed.
The gate also ran its axiom probe. A final rerun checks the proof-origin metadata edit.

## No longer needed

Removed direct proof imports (no claim that all are globally unreachable):

- Sheaf.Algebra.Homology.ModuleStalkExact
- Sheaf.AlgebraicGeometry.ModuleCechVanishingBasis
- Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic
- Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives
- Sheaf.AlgebraicGeometry.ModuleStalkFilteredColimit
- Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives
- Sheaf.AlgebraicGeometry.SchemeModulesFunctorialInjectiveEmbeddings
- Sheaf.CategoryTheory.ModuleDirectedColimitUnderlyingSets
- Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
- Sheaf.CategoryTheory.SiteCechComplex
- Sheaf.Paper.PQFCohomology
- Sheaf.Topology.PresheafModuleStalkFunctor
- Sheaf.Topology.SheavesDirectedColimitSections

The original DAG proof dependencies no longer used directly by this proof are:

- def-pc-scheme
- pqf-def-cohomology
- def-sp-left-exact-additive
- def-weil-sheaf-of-modules-category
- lem-weil-pbc-scheme-modules-enough-injectives
- lem-weil-pbc-right-derived-universal-delta-functor
- lem-weil-pbc-module-open-restriction-injectives
- lem-weil-pbc-module-restriction-open-immersion-colimits
- lem-weil-pbc-derived-functor-injective-vanishing
- def-weil-pbc-quasi-compact-scheme
- lem-weil-pbc-module-directed-colimit-underlying-sets
- lem-weil-pbc-sheaves-directed-colimit-sections
- lem-weil-pbc-scheme-modules-functorial-injective-embeddings
- def-sp-injective-resolutions
- def-weil-pbc-exact-sequence
- lem-weil-pbc-scheme-modules-coproduct-finite-subsums
- def-weil-pbc-category-colimit
- def-weil-pbc-module-stalk
- lem-weil-pbc-module-stalk-filtered-colimit
- lem-weil-pbc-filtered-colimit-modules-elementwise
- lem-weil-pbc-filtered-colimit-modules-criterion
- lem-weil-pbc-module-stalk-exact
- lem-weil-pbc-filtered-colimit-abelian-groups-exact
- lem-weil-pbc-module-cech-vanishing-basis
- def-sc-zariski-site
- def-weil-pbc-site-cech-complex
- lem-weil-pbc-module-injective-open-cover-cech-acyclic
- def-weil-directed-colimit-abelian-groups

The three Cech/stalk/injective diagram components of the old route have been replaced
by existing general tools. Some remain transitively necessary inside those tools;
the maintainer should measure global pruning from the resulting import closure.
No unit statement or realized unit step has been bypassed: this node is below the
realized statements/steps of sk-thm-p1, whose record was read unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface error was found. The DAG's ten-step plan repeats an
already formalized generic successor argument and a cohomology comparison route.
The existing tools make its module-specific Cech/stalk implementation unnecessary here.
The literature files and unit source markdown are not materialized in this clone;
the unit JSON was read, and the source proof was read at
https://stacks.math.columbia.edu/tag/01FF (lemma-quasi-separated-cohomology-colimit).

The following cross-unit nodes are used as general tools, not as a replacement for
sk-thm-p1's route: lem-sc-topological-filtered-cohomology,
lem-sc-topological-abelian-sections-filtered-colimit,
lem-sc-site-cohomology-right-derived-sections (sk-thm-curveestimate);
lem-sc-injective-module-abelian-acyclic-zariski (sk-prop-cd);
lem-sc-ext-derived-composite (sk-thm-picard-duality);
lem-weil-pbc-right-derived-filtered-colimit-successor (sk-prop-h2).
Their statements give exactly the intermediate preservation, acyclicity and comparison
facts applied in the Lean proof. Any required tool_uses bookkeeping belongs to the
maintainer; this delivery does not modify that field.

## Second reading by Y2

1. Interface and source: PASS. I compared the sole delivered Lean module with the
   repository version using diff, then checked the theorem header through `:= by`
   byte for byte. The signature, universes, namespace, visibility, public imports,
   and all definitions are unchanged. Only private proof imports, the proof
   description, and the theorem body differ. I read
   [Stacks 01FF](https://stacks.math.columbia.edu/tag/01FF): the compact-open basis,
   compact binary intersections, directed system, arbitrary colimit cocone,
   compact open U, and every natural degree are all retained. Both representative
   surjectivity and eventual kernel vanishing use precisely the original maps.
   No change record is needed.

2. Proof and axioms: PASS with existing open dependencies. The delivered module
   compiled without errors or warnings in 16.0 seconds using lcompile.py. A scratch
   copy with `#print axioms AlgebraicGeometry.openModuleCohomology_directedColimit`
   compiled in 16.3 seconds and printed exactly propext, Classical.choice,
   Quot.sound, and sorryAx. The latter is permitted here for existing dependencies:
   in particular exists_rightDerived_exact_comp_iso remains open. The module has
   no sorry, forbidden axiom/unsafe/opaque/extern/implemented_by declaration, new
   definition, or data selected into a definition from an unproved existence claim.
   The existential isomorphism is eliminated only inside a theorem proof.
   The proof is conditional on those existing holes, not an axiom-free completion
   of the whole target import closure.

3. Split statements: PASS; none were added. There are no new modules, declarations,
   nodes, or holes to certify or close. I independently searched with LeanFinder
   for preservation of filtered colimits by higher derived sections of module
   sheaves on compact opens; results concern existence/exactness of colimits and
   condensed modules, not this comparison. A local search for cohomology/colimit
   and rightDerived/colimit found the abelian topological theorem already used
   here and etale/site-change results with different hypotheses and objects.
   No duplicate statement or mere renamed replacement was introduced.

4. Route and pruning: PASS. I read the successor theorem, abelian-sections
   preservation, topological_filtered_cohomology, injective module acyclicity,
   object-cohomology/derived-sections comparison, and exact-composite comparison.
   The base case transports preservation along rightDerivedZeroIsoSelf. The
   successor supplies the exact-sequence ladder; its premise is verified by
   applying abelian cohomology preservation to T(J), whose stage groups vanish,
   and transporting the resulting zero object along the two comparisons.
   I also read [03FD](https://stacks.math.columbia.edu/tag/03FD) and
   [015M](https://stacks.math.columbia.edu/tag/015M): injective modules are acyclic
   as abelian sheaves, and this is exactly the premise needed for the composite
   comparison. No assertion that the colimit itself is injective is made.
   The final concrete-colimit argument compares y and zero at the same index;
   the two arrows become homOfLE by preorder hom subsingletonness. Degree zero,
   the empty open, a noncompact whole scheme, and non-antisymmetric directed
   preorders require no extra hypotheses. The new imports are proof-only and
   each supplies a called theorem, concrete-colimit API, or needed instance.
   The report lists all 28 removed old proof_deps and all 13 removed direct imports;
   these are direct removals, not a claim of global unreachability. I read
   dag/units/sk-thm-p1.json: this node is not a realized unit statement or step,
   and its change does not replace any of the recorded unit-level route.

5. Nodes: PASS. Programmatic JSON comparison found changes only in proof,
   proof_deps, and proof_origin. The proof_deps equal exactly the union of uses
   in the five new proof steps. I matched all seven IDs to their existing Lean
   declarations. The sections, successor, injective-stage vanishing, comparison,
   and final elementwise steps accurately describe the submitted Lean argument.
   No statement, stmt_deps, lean record, source, or unit record changed.

Changes by this second reader: appended this independent review and recorded the
explicit axiom-probe result and existing-hole limitation. No proof repair was
needed; the delivered Lean and node files are unchanged by this reading.
