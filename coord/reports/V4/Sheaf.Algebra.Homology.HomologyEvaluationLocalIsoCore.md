## What changed

Replaced the entire sorry in
`CategoryTheory.homologyEvaluation_local_iso_of_roof` by a compiling proof from
exactness of two-step open restriction and two complementary intermediate statements.
The existing theorem's signature, visibility, and docstring are unchanged.

The item proves that the restricted J has homology concentrated in degree zero:
combine `moduleOverFunctor_limits_proof` and `moduleOverFunctor_colimits_proof`
with the over-open equivalence, transport preservation through
`Scheme.Modules.overFunctorEquiv`, compose the two restrictions, and apply
`mapHomologicalComplexHomologyIso` and `map_isZero`.

`FiniteFreeZeroHomologyEvaluation` isolates the finite-free zero-differential
calculation on a general small ringed site. It returns an invertible evaluation
and its two explicit cycle factorization identities. Its proved private helper
`finiteFree_hom_preservesHomology` establishes homology preservation by internal
Hom from a finite-free module, using the existing
`SheafOfModules.finiteFreeInternalHomExact`.

`HomologyEvaluationRoofComparison` isolates restriction and quasi-isomorphism
naturality of evaluation. It assumes an arbitrary model evaluation satisfying
those cycle identities, with no assumption that this evaluation is invertible.
It has no concentration, zero-differential, boundedness, or finite-free hypotheses.
Its proved private helper `homComplex_precomp_homology_isIso` applies the existing
`quasiIso_homComplex_map` to the identity of the K-injective target and a roof arrow.

The main proof obtains the finite-model map and its cycle identities, obtains the
comparison square, proves its right-hand composite is invertible, and uses
`IsIso.of_isIso_comp_right` to cancel the target comparison isomorphism.
This follows the original finite-model/roof route below the unit level. No unit or
chapter record is changed; the unit's realized statement/steps are not bypassed.
All three modules were compiled in import order with lcompile.py. The sandbox also
contains a scratch calculation of exactness; it is outside lean/ and is not delivered.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.homologyEvaluation_local_iso_of_roof`
(node `new-b2-homology-evaluation-local-iso-core`). Its proof now contains no sorry.

Added exactly two public theorem holes, each the entire named theorem proof:

- `CategoryTheory.finiteFreeZero_homologyEvaluation`
  (node `new-v4-finite-free-zero-homology-evaluation`), in
  `Sheaf.Algebra.Homology.FiniteFreeZeroHomologyEvaluation`.
- `CategoryTheory.homologyEvaluation_roof_comparison`
  (node `new-v4-homology-evaluation-roof-comparison`), in
  `Sheaf.Algebra.Homology.HomologyEvaluationRoofComparison`.

This is a decomposition: one original hole closed, two lower holes added, net -1.
It is not a sorry-free mathematical proof. Both new statements are strict parts
of the argument: the finite calculation has no global scheme/roof/evaluation data,
and the comparison theorem has no finite-model hypotheses and never assumes
invertibility of the model evaluation. The item combines them by a genuine Lean
proof. The two private helpers mentioned above have complete proofs and add no holes.
No definitions, axioms, or target statements were added or changed.

## No longer needed

Replaced the new finite-model module's public `Mathlib.Algebra.Homology.QuasiIso`
import with `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`: the
statement needs cycles and homology, but never quasi-isomorphisms.

Removed the item's direct proof imports
`Sheaf.Algebra.Homology.HomComplexRestrictOpen` and
`Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`: they belong to the new
roof-comparison subargument instead. Both remain proof imports there and remain
needed; their nodes `lem-sc-hom-complex-restrict-open` and
`lem-pur-rhom-well-defined` are not pruned from the overall argument.

The redundant direct import of
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` considered
during development was removed; `DerivedHomMayerVietoris` already publicly imports it.
No whole library module or DAG node is claimed globally unnecessary. The original
core node's definition-only proof dependency list is replaced by the dependencies
of the actual Lean reduction. The K-injective and quasi-isomorphism definition nodes
remain statement dependencies, and the roof-comparison node records their uses.

## Where the brief, the DAG or earlier work was wrong

The core node's one proof step invoked a finite-free calculation and a comparison
square, but its proof_deps named only definitions. There was no recorded theorem
for either needed result. Existing finite-free internal-Hom exactness is reusable;
the one-column finite-free Hom homology theorem does not supply evaluation
compatibility and does not cover an arbitrary finite-support source.
The two new statements make the missing subarguments precise without moving the
original statement wholesale into either of them.

Read the Stacks proof of Tag 0BQY and quasi-isomorphism comparison Tag 0A95 online;
the local literature directory on this machine contains the index/list files rather
than the .tex bodies. The new finite-model statement is the general finite-free
calculation implicit in 0BQY, with the full cycle formulas written explicitly.
The comparison uses the fixed projections from 0A8X, not an unspecified bare
isomorphism of Hom objects.

Edge cases checked in the arguments: E=0, rank zero, zero ring, empty opens, and
-n outside the support make the same factor calculations zero-to-zero. The
comparison theorem also allows a noninvertible model evaluation, arbitrary
unbounded E and J, and J not concentrated in degree zero; it is only a naturality
statement. No such extra hypothesis was silently used in that statement.
LeanSearch was attempted for each new statement and returned Internal Server Error;
its unavailability is recorded without an absence verdict. LeanFinder, Loogle,
Mathlib/source grep, the imported modules, and blueprint search supplied no exact
existing theorem for the two new statements. The existing auxiliary exactness
results in DerivedHomMayerVietoris and quasi-isomorphism theorem are used as tools,
not as replacements for any unit's proof route.

## New nodes

`new-v4-finite-free-zero-homology-evaluation` records the general finite-model Hom
calculation with explicit cycle identities and its bounded support/free-term
hypotheses, at
`dag/nodes/sec-picard-framework/new-v4-finite-free-zero-homology-evaluation.json`.
Its Lean module is `Sheaf.Algebra.Homology.FiniteFreeZeroHomologyEvaluation`.
The proved exactness helper reduces the remaining work to finite product
homology and the compatibility of the surviving projection with cycles/classes.

`new-v4-homology-evaluation-roof-comparison` records restriction and roof
naturality, independently of the finite calculation, at
`dag/nodes/sec-picard-framework/new-v4-homology-evaluation-roof-comparison.json`.
Its Lean module is `Sheaf.Algebra.Homology.HomologyEvaluationRoofComparison`.
The proved precomposition helper supplies the roof arrows' Hom-homology
invertibility; the remaining work is assembling the component-compatible
restriction isomorphisms and proving the cycle evaluation square.

Updated the existing core node's proof, proof_deps and proof_origin to match the
Lean proof. No existing interface changed, so no change record or forced
adaptation is needed.

## Second reading by V4

1. **Unchanged interfaces: pass.** Read the three delivered modules in full and
   diffed the core module against the repository. Its complete declaration from
   the docstring through the signature is byte-identical. Only its proof imports
   and proof body changed. The other two modules are new; neither adds a definition.
   The existing core node changes only `proof`, `proof_deps`, and `proof_origin`.
   Read the landed shared-interface change record: the original evaluation
   definitions and their characterization were preserved.
2. **Proof and trust: pass as a decomposition.** Compiled all modules in import
   order through lcompile.py and inspected the complete core proof. Restriction
   exactness follows from the two named preservation theorems and the over-open
   equivalence; the direction of the homology isomorphism in hK is correct.
   Both square isomorphisms point toward the finite model, so cancellation by b.hom
   proves exactly the required restricted IsIso. The core has no sorry; each new
   module has exactly the one public named theorem hole listed above. No axiom,
   unsafe, opaque, extern, implemented_by, hollow definition, or arbitrary witness
   definition is introduced. Scratch copies with #print axioms check the core,
   both split theorems, and both private helpers; only the standard three axioms
   and sorryAx for remaining theorem dependencies are allowed.
3. **Split statements: pass.** Read Stacks Tags 0BQY, 0A8X, 0A95 and 08DL. The
   first statement generalizes the finite-free calculation in 0BQY, rather than
   claiming to be its verbatim theorem. It uses d_E=0 to separate the factors,
   bounded support to make their product finite, finite-freeness for exactness of
   Hom(E^p,-), and hK to retain only p=-n. Its c identities precisely describe the
   induced evaluation, with no additional acyclicity of sections assumption.
   Checked E=0, r=0, zero ring, empty site objects, and -n outside support: the
   construction reduces to the unique zero-to-zero map. For a nonzero one-column
   free E it reduces to the usual finite-product homology map.
   The second statement concerns naturality only: its K-injectivity is used on
   both Hom-precomposition maps; q,p being quasi-isomorphisms gives the homology
   isomorphisms on their evaluation targets. Neither f nor e is assumed invertible.
   The two factorization identities identify classes after locally lifting cycles;
   homology class maps are epis of sheaves, not necessarily surjective on sections.
   Taking identity roofs gives the ordinary evaluation characterization, even
   with unbounded complexes and nonconcentrated K; zero complexes and empty opens
   introduce no extra hypothesis. Neither split simply restates local invertibility.
   Repeated search with the different finite-projective/product formulation in
   LeanFinder, a fully qualified homology-map/IsIso Loogle query, and Mathlib grep.
   Inspected the one-column theorem in SingleSupportedFiniteFreeHomologyIso,
   FiniteProductCohomology, upstream InternalHomFree, and the evaluation modules.
   No existing declaration gives either complete cycle-compatible statement.
   The finite-product theorem is about abelian groups; the one-column theorem
   does not cover multi-column E or the cycle identities. DAG/blueprint searches
   with zero-differential/evaluation and evaluation/roof phrases found no duplicate.
4. **Shortest route and pruning: pass.** The proved finite-free exactness and
   quasi-isomorphism results are reused in the two private helpers. No available
   theorem closes either remaining whole statement in a short specialization.
   The original core definition dependencies remain in its statement closure;
   the direct restriction/quasi-isomorphism imports move to the comparison module,
   rather than being falsely counted as global pruning. All old proof_deps are
   accounted for in the report. Read sk-thm-picard-duality.json: realized.statement
   is empty and its one realized step is empty. No realized node is bypassed or
   unit record changed; the local finite-model/roof subargument is retained.
5. **Nodes and proofs: pass after repair.** Verified each node's Lean statement
   byte-for-byte against its theorem signature, its source, chapter/unit, creation
   and blueprint records, and the proof_deps union. The core node describes the
   exactness, two theorem applications and IsIso cancellation actually written.
   Both new nodes carry complete proof plans and source-backed docstrings. Found
   that the comparison plan needed explicit projection-compatible construction:
   bare existential restriction isomorphisms do not supply evaluation compatibility.
   Expanded its first DAG step and added lem-sc-hom-complex-projections and
   lem-sc-internal-hom-over-equiv as dependencies, with the latter's proof import.

Second-reading changes: narrowed the finite-model homology import; made its factor
complex degree reindexing explicit (avoiding shift-sign ambiguity); expanded the
comparison's docstring and DAG plan to construct product comparisons with fixed
projection equations, and added the natural internal-Hom factor dependency/import.
No existing signature, definition, hole count, or unit route changed.
