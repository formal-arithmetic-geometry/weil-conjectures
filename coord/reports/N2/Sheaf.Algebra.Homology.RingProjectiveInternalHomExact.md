## What changed

Proved `SheafOfModules.ringProjectiveInternalHomExact` in
`Sheaf.Algebra.Homology.RingProjectiveInternalHomExact`, without changing its signature.
Added proof-only imports of `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` and
`Mathlib.Algebra.Category.ModuleCat.Projective`.

The proof implements the existing two-step DAG plan. A concrete inverse to the
forgetful functor for the bottom topology gives preservation of finite colimits.
Evaluation is faithful because the discrete site has only one object. Thus evaluation
preserves and reflects exactness; finite limits are already supplied by Mathlib.
The slice also has only one object. Its internal-Hom maps are postcomposition.
Exactness in the middle uses `ShortComplex.Exact.lift`, injectivity uses cancellation
by the evaluated monomorphism, and surjectivity uses `Projective.factorThru` after
converting module projectivity to categorical projectivity. The resulting evaluated
short exact sequence is reflected back to sheaves. All helper constructions and
lemmas are private and fully proved. No objects are chosen from an unproved theorem.

The module compiles locally within the single-file limit, with default heartbeats
and no warnings. The dry run supplies the final compiler and axiom checks.

## Proved and sorry left

Closed the sole original hole: `SheafOfModules.ringProjectiveInternalHomExact`
(node `lem-pc-ring-projective-internal-hom-exact`). Added zero holes, split off zero
statements. No `sorry` remains in the delivered module. This is a proof, not a
decomposition. The proof places no nonzero-ring, finite-rank, or finite-generation
assumptions on the source; the zero ring and zero module are included.

## No longer needed

None of the original imports, nodes, or modules is pruned. Both original definition
nodes remain used. `KFlatTensorQuasiIso` provides `onePointRingSheaf` in the unchanged
signature, so its public import must remain. The attempted extra proof import
`Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono` was removed as unnecessary;
it was absent from the original module. The two new proof imports are required by
the module-level exactness criterion and the projectivity conversion respectively.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The DAG plan is implementable entirely
with the existing definitions and Mathlib. Its `proof`, `proof_deps`, and
`proof_origin` remain accurate, so no node change is needed. The unit's `realized`
record is empty; no unit statement or step is bypassed. The node's cited local
Stacks TeX file is absent on this machine; the proof follows the already recorded
algebraic argument and introduces no source-dependent unresolved assertion.

## Second reading by N2

1. **Unchanged interface — pass.** Read the complete repository and sandbox modules
   and compared them with `diff -u`. Independently extracted the existing theorem's
   text from `theorem ringProjectiveInternalHomExact` through its `:= by`: the
   signatures are byte-for-byte identical. The commutative ring, arbitrary projective
   point value, arbitrary short exact sequence, composite-zero witness, and full
   short-exact conclusion are unchanged. The original docstring and public imports
   are unchanged. The added declarations are private; the two added imports are
   proof-only. There are no changes to existing definitions or other modules.
2. **Proof and constructions — pass.** Independently compiled the delivered module
   using `lcompile.py` (7.5 seconds, no warnings). Compiled a scratch copy containing
   `#print axioms SheafOfModules.ringProjectiveInternalHomExact`: precisely `propext`,
   `Classical.choice`, and `Quot.sound` (6.6 seconds), with no `sorryAx`. Scanned the
   delivered Lean for holes and forbidden declarations/options: none. Read
   `bottomEquivalence`: its inverse constructs the underlying presheaf with the
   proved bottom-topology sheaf condition; the identity unit and counit give an
   actual equivalence. `pointPreimage` constructs its components from the supplied
   linear map, proving naturality from the singleton hom-set, without choosing any
   unproved witness. `slice_unique` uses the discrete singleton objects and arrows.
   In the main proof, evaluation preserves finite limits and colimits and is
   faithful. Exactness at the middle uses `hs.exact.lift` with its explicitly proved
   zero-composite condition; injectivity cancels the evaluated monomorphism;
   surjectivity uses `Projective.factorThru` through the evaluated epimorphism.
   The final reflection proves all three parts of short exactness. Read the
   Mathlib projectivity conversion: despite its name, its hypothesis is exactly
   `Module.Projective R P` and its conclusion is categorical `Projective P`.
3. **Split statements and edge cases — pass.** No new public statement, new node,
   or split-off hole exists, so no split-off searches or repairs are needed.
   Checked that the constructions impose no nonzero-ring, nonzero-source,
   finite-generation, or finite-rank hypothesis: all work over the zero ring,
   for the zero module, and for arbitrary projectives. The original single hole
   is closed and zero holes are added.
4. **Route and pruning — pass.** Read the original node's two-step plan and
   `dag/units/sk-thm-picard-duality.json`: its `realized.statement` and its step
   realization are empty. The proof implements evaluation followed by the
   module lifting argument, without bypassing a realized unit. Independently
   searched LeanFinder for bottom-topology equivalences and singleton evaluation,
   and searched the local sheaf/module code for existing equivalences and exact
   internal Hom results. The returned `CategoryTheory.sheafBotEquivalence` concerns
   category-valued sheaves, not dependent modules over a sheaf of rings; it is not
   a direct replacement for this private module equivalence. Existing finite-free
   internal Hom results do not cover arbitrary projective sources. Read the shared
   `homObj`, `homObjMap`, and `restrictOver` definitions: they give exactly the
   slice morphisms and postcomposition used here. Both old proof dependencies
   remain used; `## No longer needed` is complete. Original public imports supply
   the signature; the added imports supply module exactness and projectivity.
5. **DAG agreement — pass.** Read
   `lem-pc-ring-projective-internal-hom-exact` and both dependency nodes
   `def-weil-sheaf-of-modules-category` and `def-pur-sheaf-hom`. The existing
   `proof`, `proof_deps`, and `proof_origin` describe this same one-object-site
   argument: evaluation and the singleton slice, followed by kernel factorization,
   injectivity, projective lifting, and reflection. No dependency is silently
   dropped and no new unresolved claim needs a node. No node edit is necessary.

Second reading changed only this report, adding the independent review. The Lean
proof required no repair. The scratch axiom check is outside `lean/` and is not
part of the delivery. Final validation is the delivery tool's compile, all-declaration
axiom probe, and preflight.
