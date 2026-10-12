## What changed

Replaced the sorry in AlgebraicGeometry.affine_algebra_derived_adjunction_isos with a
complete Lean reduction. The original theorem signature and its public imports are unchanged.
The second reader removed two redundant proof imports and three unnecessary
elaboration options; the unchanged proof compiles without them.
The proof constructs the underived module pullback adjunction using Mathlib's
SheafOfModules.PullbackConstruction.adjunction, obtains underived exactness and
unit/counit isomorphisms, rewrites the cohomology maps using explicit factorization
equations, cancels the unit comparison isomorphism, and applies DerivedCategory.isIso_iff.
Three new modules carry the strictly smaller remaining statements. Updated the original
node's proof, proof_deps and proof_origin to match that assembly.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.affine_algebra_derived_adjunction_isos
(lem-sc-affine-algebra-derived-adjunction-isos). No sorry remains in the item's module.
This is a decomposition, not an unconditional proof: one upper hole closed, three
lower holes added, net minus two holes before closure pruning.

New remaining holes, each in its own module:

- AlgebraicGeometry.affine_algebra_module_adjunction_isos
  (lem-sc-affine-algebra-module-adjunction-isos).
- AlgebraicGeometry.affine_algebra_derived_unit_homology_factorization
  (lem-sc-affine-algebra-derived-unit-homology-factorization).
- AlgebraicGeometry.affine_algebra_derived_counit_homology_factorization
  (lem-sc-affine-algebra-derived-counit-homology-factorization).

Each proof is exactly by sorry, with its source and full natural-language argument in
its docstring and matching node. The new statements isolate underived geometry and
map-compatible cohomology comparisons; none asserts the original derived invertibility
conclusion. The assembly actually uses the equations and underived isomorphisms.
Checked edge cases conceptually: identity affine morphisms, empty schemes, zero modules,
non-surjective affine morphisms, arbitrary integer degrees, and unbounded complexes.
No finiteness, nonempty, surjectivity or boundedness assumption is introduced.
Adjunctions need not be canonical: comparison isomorphisms absorb the unique
adjunction-compatible changes of left adjoints. They are existential proposition
witnesses eliminated only in the proof; no definition chooses arbitrary data.

## No longer needed

Removed redundant proof imports Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
and Mathlib.Algebra.Homology.DerivedCategory.HomologySequence (both already available
through the remaining imports). No original import was removed: the three original public imports are needed by the
unchanged signature. No node or module is globally pruned by this delivery.
The original node no longer directly uses lem-pc-ringed-spaces-derived-adjoint-general,
lem-sc-affine-algebra-derived-adjunction-qcoh, lem-sc-affine-derived-cohomology,
lem-weil-pbc-affine-module-correspondence, def-pc-ringed-spaces-derived-direct-image,
or def-weil-abstract-derived-category as proof dependencies: the first five relevant
arguments now occur below the new nodes, and the last is handled by Mathlib derived
conservativity in the assembly. These are not claimed globally unnecessary.
The separate proof of quasi-coherence preservation is not imported by the item's proof;
it remains useful below the unit factorization. The underived adjunction construction
uses Mathlib directly, so RingedSpaceTensorPullbackUnderived is not needed by the assembly.
No unit-level route has been bypassed; sk-thm-picard-duality.realized contains no binding
for this item. The affine flatness, module correspondence and cohomology route is retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The original dependency statements
supply quasi-coherence and underived equivalence, but do not expose the two equations
identifying derived adjunction maps on cohomology. Those are the missing glue isolated
in the two new factorization modules.

The local compiled library lacks AffineAlgebraDerivedAdjunctionQCoh and
RingedSpaceTensorPullbackUnderived although their sources are present. I did not copy
or restate those existing declarations. The Mathlib underived adjunction construction
allows the final assembly to compile without importing either missing artifact.

The source texts were not installed under literature/ on this machine. Read the primary
source online: https://stacks.math.columbia.edu/tag/0AVW and
https://stacks.math.columbia.edu/tag/01SB. Sources in the node records retain the project's
canonical literature paths. LeanSearch returned Internal Server Error on all three new
statements; recorded as unavailable, with real LeanFinder, Loogle and grep searches.

The affine module correspondence from sk-thm-proper-base-change is used below the new
nodes as the same generic module-equivalence tool already used by the original node.

A traversal of the delivered nodes found an existing downstream DAG cycle:
lem-weil-pbc-sheaf-algebraic-structures-objects and
lem-weil-pbc-sheaf-algebraic-structures-abelian-component cite each other.
It is reached through the affine cohomology dependencies already used by the original
plan. This delivery adds no edge back to its own theorem or its new nodes and does
not change those unrelated nodes.

Validation: all four delivered modules compile without errors or non-sorry warnings;
the delivery tool's axiom probes ran, and the dry run passed all static checks except
the second reading reserved for the next worker.

## New nodes

lem-sc-affine-algebra-module-adjunction-isos: the underived affine algebra pullback
preserves finite limits, and the ordinary adjunction unit and counit are isomorphisms
on quasi-coherent modules. This isolates the stalk localization and tensor-associativity
argument, without any derived invertibility assertion.

lem-sc-affine-algebra-derived-unit-homology-factorization: for one integer degree,
an explicit target isomorphism identifies the derived unit map with the underived unit.
It states an equality of maps and a cohomology comparison, leaving their invertibility
to the assembly and the underived lemma.

lem-sc-affine-algebra-derived-counit-homology-factorization: for one integer degree,
an explicit source isomorphism factors the derived counit map through the ordinary
counit. It states the map-compatible cohomology formula, without derived invertibility.

No change records: no existing definition or statement changes.


## Second reading by A2

1. PASS: Compared all four modules against the repository. Only the item's module
   already existed; its entire theorem signature and docstring remain byte for byte
   unchanged. No existing definition changed, and no change record is required.
   Compared its node JSON: only proof, proof_deps and proof_origin changed.
2. PASS as a decomposition: all four delivered files compile through lcompile.py.
   The item has no sorry; exactly the three named theorems listed above remain sorry.
   There is no new data definition, arbitrary chosen witness, or forbidden declaration.
   The four explicit #print axioms checks show only propext, Classical.choice,
   Quot.sound and sorryAx. The latter remains, so this is not an unconditional proof.
3. PASS: Read all three new statements and their docstring arguments against Stacks
   Tags 0AVW and 01SB. The stalk ring map is a localization even for a non-flat affine
   f: it is g, not f, that is flat. Exact g-pullback commutes with all cohomology;
   affine vanishing plus the unbounded cohomological bound computes Rg-pushforward.
   Unit and counit equations transport through adjunction-compatible uniqueness of
   left adjoints, including noncanonical adjunctions. Identity maps, empty schemes,
   zero modules, non-surjective affine maps and arbitrary integer degrees impose no
   extra assumptions. Each factorization handles one cohomology map, and the ordinary
   lemma contains no derived invertibility assertion: these are strictly lower parts
   of the original argument. No lower hole could be closed in a short proof.
   Repeated searches with different wording: LeanFinder found the general
   CategoryTheory.Adjunction.derived_unit/derived_counit infrastructure; Loogle found
   the existing ordinary pullback construction; Mathlib grep found no geometric
   exactness or quasi-coherent adjunction-isomorphism theorem. Local and upstream rg
   searches found affineDerivedCounit_homology_factorization, but that is a different
   tilde/global-sections adjunction on Spec and does not replace these statements.
4. PASS: The assembly explicitly constructs the ordinary left adjoint, rewrites both
   cohomology maps and uses derived homology conservativity; it does not apply a
   restatement of the item. Checked every old proof dependency against No longer
   needed. Removed two redundant new proof imports, verified by compilation. Kept
   the three original public imports used by the signature. The unit record
   sk-thm-picard-duality has empty realized bindings, so none is bypassed; the affine
   module correspondence, flatness and cohomology route remains below the new nodes.
5. PASS: Every new node has its required source, statement dependencies, proof steps,
   proof origin, recorded searches, split status, creation and blueprint records,
   chapter, unit and Lean record. Every recorded Lean signature matches its module.
   proof_deps equals the union of step uses; the item's three dependencies match the
   three lemmas actually invoked in the assembly. The new nodes do not cite the item.

Changed in this second reading: removed the redundant PullbackContinuous and
HomologySequence proof imports and the three unnecessary backward elaboration options;
updated this report. No statement, definition, mathematical route or remaining hole changed.
Primary sources read: https://stacks.math.columbia.edu/tag/0AVW and
https://stacks.math.columbia.edu/tag/01SB.
