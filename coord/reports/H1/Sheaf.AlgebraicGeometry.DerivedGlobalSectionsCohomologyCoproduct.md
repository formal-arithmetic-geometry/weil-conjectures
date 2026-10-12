## What changed

Replaced the sorry in AlgebraicGeometry.derivedGlobalSections_cohomology_coproduct
with a complete proof from the derived-global-sections coproduct step. The proof applies
module homology, identifies the resulting module coproduct with the concrete direct sum,
and checks that its isomorphism is exactly the displayed DirectSum.toAddMonoid map.
The original theorem signature and docstring are unchanged.

Added Sheaf.CategoryTheory.DerivedModuleHomologyCoproduct with a fully proved
AlgebraicGeometry.derivedModuleHomology_coproduct. It reuses the existing generic
exact-colimit homology
comparisons in DerivedAmbientDirectSumsHomology via a private import all, represents
derived coproducts by module complexes using the
existing derivedModuleDirectSums, and transports the colimit along representative
isomorphisms. It works for every integer degree and includes empty sums.

Added Sheaf.AlgebraicGeometry.DerivedGlobalSectionsPreservesCoproducts for the remaining
geometric step of the original plan. Its docstring specifies the affine pushforward,
resolution-composition and restriction-of-scalars argument. These comparisons are not
provided by the existing dependency interfaces as a ready-to-apply theorem.
All three modules compile locally through lcompile.py without warnings.
The dry run with WEIL_SERVER_COMPILE=1 also passed the server compilation checks
for the modules having no sibling delivery imports. The landing-specific
import_prune_check.py now passes for DerivedModuleHomologyCoproduct (exit 0),
confirming the reported duplicate-statement refusal is repaired. deliver3.py
rebases the delivery onto the fetched origin/sheaf-dag; nothing is pushed.

## Proved and sorry left

Closed the item's sole hole:
AlgebraicGeometry.derivedGlobalSections_cohomology_coproduct
(lem-pc-derived-global-sections-cohomology-coproduct).

Added one remaining hole:
AlgebraicGeometry.derivedGlobalSections_preserves_coproducts
(lem-pc-derived-global-sections-preserves-coproducts), in its own new module.
The item has no remaining sorry; this is a decomposition, not a proof free of sorry
in its dependency closure. Net holes closed minus holes added is zero.

The new AlgebraicGeometry.derivedModuleHomology_coproduct
(lem-pc-derived-module-homology-coproduct) is completely
proved without sorry. The two duplicate private helpers are removed; their already
proved counterparts in DerivedAmbientDirectSumsHomology are reused. The module-homology
portion and canonical-map identification
are genuine proof work, rather than splitting bijectivity into injectivity/surjectivity.

## No longer needed

Removed duplicate declarations shortComplexHomologyColimit and
complexHomologyColimit from DerivedModuleHomologyCoproduct. Removed that module's
proof imports Mathlib.Algebra.Homology.HomologicalComplexLimits,
Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence,
Mathlib.Algebra.Homology.ShortComplex.ExactFunctor, and
Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products: the reused helper module
provides these comparisons. Added import all
Sheaf.AlgebraicGeometry.DerivedAmbientDirectSumsHomology only for proofs.

Removed direct proof imports from the item:
Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence,
Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums,
Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh,
Sheaf.AlgebraicGeometry.GlobalDerivedHom,
Sheaf.CategoryTheory.DerivedModuleDirectSums.
They remain needed transitively: the first four under the new geometric step,
and the last under the fully proved module-homology step. The corresponding nodes
lem-pc-affine-qcoh-derived-equivalence,
lem-pc-derived-direct-image-preserves-direct-sums,
lem-pc-derived-direct-image-preserves-qcoh,
def-pc-global-derived-rhom,
def-pc-ringed-spaces-derived-direct-image, and
lem-pc-derived-module-direct-sums are retained in the argument.
No whole module or node is claimed pruned from the targets' closure.
The blueprint unit's realized field is empty; its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

Repair of the landing refusal at f5707b9d1: the first delivery copied two generic
private helpers already proved in DerivedAmbientDirectSumsHomology. Privacy does
not require duplication: Lean module-system import all exposes them to proof bodies
without exporting them or changing any existing interface. Both duplicates are now
removed and the module-homology node records the reused helpers. No library module
was adapted. The previous second reading is removed because it predates this repair.

The original plan correctly describes the mathematical argument, but its existing
statements lack a packaged natural comparison proving that module-valued RΓ carries
the specified coproduct to a derived module coproduct. That interface is the remaining
new geometric node. No existing definition or statement was changed and no forced
adaptation was needed. LeanSearch returned Internal Server Error; it is recorded as
unavailable, not as evidence of no match.

## New nodes

lem-pc-derived-global-sections-preserves-coproducts: the geometric first two steps of
the original plan, before homology, as an ambient derived module colimit. The source
is Stacks Tag 09M1, first paragraph. One named sorry remains here. Empty sums, zero
summands and arbitrary shifts/unbounded complexes are included; scalar restriction
is exact and detects quasi-isomorphisms, so the argument applies to these cases.

lem-pc-derived-module-homology-coproduct: the algebraic homology portion, now fully
proved for all degrees and any ring. Sources are Stacks Tag 07D9 and the direct-sum
calculation of Tag 09M1. Three kinds of search were run and recorded for each new node;
blueprint searches found no matching node. No change records are necessary.


## Second reading by H1

1. I compared the delivered item module with the repository version. The theorem
   `AlgebraicGeometry.derivedGlobalSections_cohomology_coproduct` has the identical
   signature and docstring; only its proof and proof-only imports changed. The two
   new modules and their declarations are recorded by new DAG nodes, so no existing
   declaration was changed accidentally. Verdict: passed.

2. I compiled all three delivered modules with `lcompile.py --all`. The item theorem
   has no `sorry`; the only remaining `sorry` is the named split theorem
   `AlgebraicGeometry.derivedGlobalSections_preserves_coproducts`. The new homology
   theorem is fully proved. No forbidden declaration or hollow definition occurs.
   Verdict: passed.

3. I checked the split statements and their DAG records. The global-sections theorem
   is the geometric comparison required before homology, while the module-homology
   theorem is the strictly lower algebraic calculation used by the item. Both include
   arbitrary and empty coproducts and retain their cited sources and proof sketches;
   neither duplicates an existing public theorem. Verdict: passed.

4. I checked the proof from the top downward. The item first applies the geometric
   coproduct comparison, then the fully proved module-homology comparison, and finally
   identifies the induced map with `DirectSum.toAddMonoid`. The generic homology
   helpers are reused through a private `import all`; duplicate helpers and unused
   direct proof imports were removed. Verdict: passed.

5. I checked the node `proof`, `proof_deps`, `proof_origin`, and the unit route. The
   item still realizes the same Picard-duality unit step, and the new node records list
   exactly the geometric and algebraic dependencies used by the delivered proofs.
   Verdict: passed.

I changed only this report section. No Lean source or DAG correction was needed after
review; the remaining geometric theorem is intentionally split off as documented.
