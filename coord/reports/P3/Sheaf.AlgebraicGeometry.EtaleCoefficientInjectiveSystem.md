## What changed
The existing theorem `etale_coefficient_injective_system` keeps its signature byte for
byte. Its proof assembles transitions and embeddings for the explicitly constructed
`etaleCoefficientInjectiveTarget`, with injectivity supplied by the closed theorem
`etale_coefficient_injective_system_data`. The two new modules are
`Sheaf.AlgebraicGeometry.EtaleCoefficientInjectiveSystemData` and
`Sheaf.AlgebraicGeometry.EtaleCoefficientInjectiveSystemEmbedding`; the item imports
the embedding module only for its proof; that module exposes the data module. The data module constructs the product of direct images of
`Injective.under (F k)`, indexed by outgoing arrows. No witness is chosen from an open
existence theorem. The construction and its injectivity proof have no sorryAx.

## Proved and sorry left
Closed the item's hole `AlgebraicGeometry.Etale.etale_coefficient_injective_system`
by a reduction. Added one hole:
`AlgebraicGeometry.Etale.etale_coefficient_injective_system_embedding`, node
`lem-weil-pbc-etale-coefficient-injective-system-embedding`, which concerns transitions,
their identity/composition laws, and compatible monomorphisms for the specified product.
`AlgebraicGeometry.Etale.etale_coefficient_injective_system_data` is fully proved;
it and `AlgebraicGeometry.Etale.etaleCoefficientInjectiveTarget` use only propext,
Classical.choice and Quot.sound. The target still uses sorryAx through the embedding
lemma. Baseline holes closed: 1; new holes added: 1; net: 0. This is a decomposition,
not a completed proof of the target. Relative to the first worker's draft, the two
open claims were replaced with one proved injectivity claim and one valid open claim.

## No longer needed
Removed the item's proof import `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`:
old proof dependency `prop-weil-pbc-inverse-image-exact` is no longer used. The data
proof uses the upstream `AlgebraicGeometry.Etale.preservesFiniteLimits_upperStar`
instance directly. Its node now records that route and omits the stronger exactness
node. No whole module is asserted unreachable from all targets.

Removed the item's direct proof imports
`WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves` (now imported
where used, in the new data module) and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (already supplied transitively
by the retained public import). Removed the redundant public import
`Mathlib.CategoryTheory.Preadditive.Injective.Basic`, with its change record and a
successful compile of the original direct importer.

The other four old proof dependencies remain in the mathematical reduction:
`lem-sp-right-adjoint-preserves-injectives`, `lem-weil-pbc-product-injectives`,
`lem-weil-pbc-site-sheaves-enough-injectives`, and
`lem-weil-pbc-inverse-image-composition`. The parent now names its two immediate
subclaims. Removed redundant experimental imports of
`Mathlib.CategoryTheory.Limits.Shapes.Products`,
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`, and Basic
injectivity from the new data module, and the direct data-module proof import from
the item. The previous existential data claim and arbitrary-target embedding claim
are not delivered.

## Where the brief, the DAG or earlier work was wrong
The first worker's embedding claim was false: it quantified over every target FI,
without even assuming injectivity. For a singleton index, a nonzero coefficient sheaf
cannot embed monomorphically into the zero sheaf. The zero target is itself injective,
so adding injectivity would not repair this error. That draft is
STATEMENT-DISPUTED: arbitrary compatible target systems need not contain F.
The earlier second-reading assertion in the old report was therefore incorrect.
The first worker also left the parent DAG proof unchanged and copied obsolete review
metadata onto new nodes. These records are replaced with fresh nodes matching the
actual reduction. No existing statement or definition is changed.

## New nodes
`def-weil-pbc-etale-coefficient-injective-target` specifies the outgoing-arrow product
construction in EtaleCoefficientInjectiveSystemData.lean.

`lem-weil-pbc-etale-coefficient-injective-system-data` records the proved injectivity
of that product, using enough injectives, exact inverse image, right adjoints, and
products of injectives.

`lem-weil-pbc-etale-coefficient-injective-system-embedding` records the remaining
coherence and embedding construction for this specified product, with a complete
natural-language proof and source in its docstring. Searches used different terms
from the first worker: right-adjoint products, diagram embeddings and categorical
monomorphisms. LeanFinder, Loogle and grep found the basic ingredients, but no exact
etale product-system construction. LeanSearch returned Internal Server Error.
The related `CategoryTheory.exists_compatible_injective_system` is about small-site
precoverage data, sheaves in a different universe, and a pushforward cocycle without
an identity-law conclusion; it is not a direct replacement for the open claim.
The public-import removal is recorded in `coord/changes/EtaleCoefficientInjectiveSystem-import.md`; the two modules and three nodes are new, and the item changes only its proof plus this redundant import.

## Earlier second reading (a previous round; superseded)

1. Compared each delivered module with the repository version using `diff`; all existing declaration signatures are byte-for-byte unchanged. The target now imports only the embedding module for its proof, and the former direct `Mathlib.CategoryTheory.Preadditive.Injective.Basic` import is redundant because the retained public `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance` import supplies the signature dependencies transitively. The embedding module is imported privately for the proof. Verdict: pass.
2. Compiled all three modules with `lcompile.py --all`; compilation succeeds. Searched for forbidden constructs and `sorry`; the sole remaining `sorry` is the named embedding theorem. The proved data construction and injectivity theorem have no `sorryAx`; the target reduction has the expected dependency on the split theorem. Verdict: pass as a decomposition.
3. Checked the new product construction and embedding statement against singleton and zero-coefficient edge cases; it specifies one concrete target and makes no arbitrary-target claim. The embedding theorem is strictly simpler than the parent and has a complete docstring and node. Searches found no duplicate declaration. Verdict: pass.
4. Verified the proof follows the product route and retains the unit `sk-thm-p1`; no reachable module is pruned. Proof-only imports are private, and the redundant direct Mathlib injectivity import is removed. Verdict: pass.
5. Verified the parent and new DAG nodes match declarations, proof dependencies, and proof origins; the report records the net-zero decomposition. Verdict: pass.

## Earlier second reading (a previous round; superseded)
1. Compared the existing module with the repository using diff. Its existing signature,
visibility, public imports and definitions are unchanged. Only proof imports, the
proof, and a declaration-local unused-variable linter setting change. Verdict: pass.
2. Compiled all three modules with lcompile.py in dependency order. No forbidden
constructs or definition holes occur. Axiom probes show the product construction
and its injectivity theorem use only propext, Classical.choice and Quot.sound;
the reduction and the one remaining named theorem additionally use sorryAx.
Verdict: pass as a decomposition, not as a complete proof.
3. Rejected the arbitrary-target claim by the singleton/zero-target counterexample.
The replacement fixes the actual product, and its construction follows Stacks 0EXZ.
For a singleton, its identity factor is the direct image of the chosen injective;
for zero coefficients the maps exist; repeated indices in a preorder cause no issue
because products are indexed by arrows and the coherence laws handle identity maps.
The identity projection detects monicity. The remaining statement is strictly part
of the argument: injectivity of the specified object is proved separately. Searches
of Mathlib and both Lean roots found no exact duplicate. Verdict after repair: pass.
4. Used the shortest direct injectivity route through Mathlib product injectivity and
the existing adjunction criterion. Kept the product route of the parent's plan and
the unit sk-thm-p1 realized statements and steps; none is bypassed or changed.
No existing module can be pruned. Proof-only imports are private; imports needed
by the new signatures and construction are public. Verdict: pass.
5. Updated the parent's proof, proof_deps and proof_origin. New records match the
Lean declarations, include real searches, fresh provenance, matching statements,
and union-of-step proof_deps. Removed stale review records. Verdict: pass.

Second reading changed the false arbitrary-target split into a specified product
construction, proved its injectivity, expanded the remaining docstring proof,
corrected all node records, and replaced the misleading progress claim with net-zero
decomposition accounting.

## Delivery tool failure
The final repaired set passed deliver3.py --no-push at commit 423930b967.
Before the push invocation, /home/ubuntu/weil-launcher/deliver3.py changed
(timestamp 2026-10-13 03:33:46 +0800). The push invocation failed before fetching,
committing or pushing with:

ImportError: cannot import name 'refuse_missing' from 'import_cycles'
(/home/ubuntu/weil-conjectures-sheaf-P3/tools/import_cycles.py).

The updated check_import_sources imports refuse_missing and source_roots, but neither
is defined in the repository's import_cycles.py (timestamp 2026-10-12 19:49:21 +0800).
This is a tool version mismatch, not a Lean failure. Nothing was pushed. The sandbox
retains the repaired, compiled delivery. Per AGENTS.md section 3, the second reader
has not edited or bypassed the delivery tools.

## Second reading by P3

1. Compared all delivered modules to repository sources. The two auxiliary modules
are new. The existing theorem signature is byte-identical, verified separately by
substring comparison. Its public import removal has the required change record;
no existing definition or target statement changes. Verdict: pass.
2. Compiled all three modules through lcompile.py --all, then compiled a scratch
copy with four #print axioms commands. The product definition and injectivity
proof use only propext, Classical.choice and Quot.sound. The embedding lemma and
parent additionally use sorryAx, exactly the one declared split. No forbidden
constructs or definition holes occur. Compiled an unchanged scratch copy of the
sole direct importer EtaleCoefficientInjectiveCokernelSystem against the sandbox
outputs (44.4 seconds, no warnings). Verdict: pass as a net-zero decomposition.
3. Read the specified product construction against Stacks Tag 0EXZ. The singleton
case has the identity factor containing the canonical stage embedding; zero
coefficients admit the zero embedding; equivalent indices in a preorder are
handled by arrow-indexed products and composition coherence. The adjunction
transpose gives each embedding, and the identity projection detects monicity.
The split omits the separately proved injectivity obligation and fixes the target,
so it is a strict part of the original argument rather than a renamed original
existence claim. Its docstring gives the component construction and coherence
proof, and its node matches. New LeanFinder, Loogle and grep searches and rg of
both Lean roots found no exact replacement. The existing compatible site-system
result has different universes, extra site hypotheses and no identity conclusion.
Verdict: pass; closing the remaining coherence proof is beyond a short repair.
4. Checked the unit sk-thm-p1 realized statement and all four step lists. They are
unchanged; this below-unit adjunction/product reduction bypasses no realized step.
The shortest injectivity route uses the upstream finite-limit instance rather
than the stronger Sheaf exactness theorem. Corrected the inaccurate no-pruning
report and removed that unused dependency from the data node. Public imports in
the new modules are needed by their signatures or specified construction; proof
imports are private. Verdict: pass after metadata repair.
5. Compared the existing node to the repository: only proof, proof_deps and
proof_origin change. All three new node signatures match Lean verbatim, and their
proof_deps equal the union of the proof-step uses. Checked source, creation,
chapter, unit, blueprint and search records. Corrected the data proof record to
name the actual upstream finite-limit instance. Verdict: pass after repair.

This reading changed only the data-node proof metadata and report: corrected the
unused exactness dependency, listed every removed repository import, added this
fresh independent review, and refreshed the scratch axiom check. Lean proofs and
signatures needed no further repair. The previous delivery-tool failure above is
historical: this run reaches preflight successfully once the fresh review exists.
