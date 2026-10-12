## What changed

Replaced the sorry in `AlgebraicGeometry.zariskiModuleAbelianCohomologyAgree` with a
compiling proof that assembles the positive-degree comparisons and constructs the
normalized degree-zero comparison. The private `zeroEquiv`, `zeroEquiv_apply`,
`zeroEquiv_naturality`, and `zeroIso` are completely proved, using Ext-zero, the
sheafification/free/Yoneda adjunctions, and the right-derived-zero isomorphism.
The public theorem signature is unchanged.

Added `Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural` to realize the natural
comparison already stated by `lem-sc-module-abelian-zariski-cohomology`, and updated
that existing node's Lean record accordingly. Its earlier objectwise declaration
remains unchanged in its old module. No new mathematical node is introduced. The
node's injective-resolution proof and dependencies remain its plan.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.zariskiModuleAbelianCohomologyAgree`.
This is a decomposition, not a complete proof of the comparison theory: one hole is
added, `AlgebraicGeometry.zariskiModuleAbelianCohomologyNatural`, recorded by existing
node `lem-sc-module-abelian-zariski-cohomology`. It asserts natural comparison without
the target's normalization equation. The degree-zero identification and normalization
are proved here without this hole; the new theorem is used only in positive degrees.
There are no holes in the item's module or its private definitions/helpers.

Both delivered modules compile locally. Empty schemes give zero groups; the point
scheme gives the underlying section group in degree zero and zero in positive degrees.
The comparison is valid for arbitrary modules, without quasi-coherence or any
finiteness hypotheses. Its remaining proof must use acyclicity of forgotten injectives,
not preservation of injective objects.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.ModuleAbelianZariskiCohomology`
and `Sheaf.Paper.PQFCohomology` from the item's module. The former's objectwise theorem
is not used; naturality is retained by the new realization of its existing DAG node.
The latter is unnecessary for the degree-zero proof. Its module may still be reached
through the remaining comparison's planned dependencies, so no global pruning is
claimed. Removed `pqf-def-cohomology` from the item's proof dependencies, replacing
that degree-zero use with `def-sc-ringed-space-module-cohomology`. No further nodes
are pruned: the existing natural comparison node and its resolution route remain needed.

## Where the brief, the DAG or earlier work was wrong

The DAG correctly requires a canonical comparison natural in the module, but the
old Lean signature `module_cohomology_iso_underlying_abelian` gives only objectwise
`Nonempty` isomorphisms. Arbitrary choices of those isomorphisms do not establish
naturality. Its docstring also incorrectly says forgetting produces an injective
resolution: the forgotten resolution is exact and consists of abelian-acyclic terms,
not necessarily injective abelian sheaves. The delivery restores the intended natural
statement in the existing node's Lean realization without changing any existing
signature or the node's mathematical statement. The new docstring gives the acyclic
resolution argument; the old source module is left untouched.

The unit `sk-prop-cd` and its realized route are preserved. No unit or chapter is bypassed.

## Second reading by Y3

1. **Visible declarations: pass.** Read the diff against the repository module.
   The existing public theorem signature is byte-for-byte unchanged; its docstring
   and all existing definitions remain unchanged. Added helpers are private, and
   both new imports in the item are proof-only. The new natural comparison replaces
   only the dependency node's Lean realization, preserving its mathematical statement
   and the old objectwise declaration. No change record is needed for an existing
   signature or definition.
2. **Proof and axioms: pass as a decomposition.** Compiled both modules with
   `lcompile.py --all`. In scratch copies, `#print axioms` on `zeroEquiv`,
   `zeroEquiv_apply`, `zeroEquiv_naturality`, and `zeroIso` shows only `propext`,
   `Classical.choice`, and `Quot.sound`. Both public theorems additionally show
   `sorryAx`, as expected from the reported comparison hole and open upstream
   statements. The item has no sorry; the new module has exactly the reported named
   theorem's sorry. No hollow definition or prohibited declaration is present.
   The Ext-zero equivalence evaluates the sheafification unit at the identity
   generator; its naturality is proved by Ext composition. The normalization proof
   cancels this equivalence and then the canonical derived-zero unit.
3. **Remaining statement: pass.** Read Stacks Tag 03FD at
   <https://stacks.math.columbia.edu/tag/03FD> (the cited local TeX is absent on this
   machine). It applies to any ringed site and any module, so the new theorem's
   arbitrary-scheme/module hypotheses are appropriate. The source uses exact
   forgetting and acyclicity of forgotten injectives, precisely the docstring's
   route; it does not require preservation of injectives. Checked zero modules,
   the empty scheme, and a one-point scheme: zero groups, respectively ordinary
   sections in degree zero and vanishing higher cohomology, agree on both sides.
   Renewed LeanFinder, Loogle, and grep searches using derived-global-sections,
   forgetful-functor, and Ext terminology. No existing theorem provides the required
   natural Zariski-module comparison; the existing objectwise theorem cannot supply
   naturality by arbitrary choice. The new hole omits the normalization equation,
   which is proved independently in the item, so this is a genuine reduction, not
   a renamed application of the full target. One hole closed and one added: net zero.
4. **Route and pruning: pass.** The item uses the existing comparison node in positive
   degrees and constructs degree zero directly from Mathlib adjunctions and
   `rightDerivedZeroIsoSelf`. The two removed direct imports and the sole removed
   old proof dependency `pqf-def-cohomology` are all listed above. The replacement
   natural-comparison module retains its node's planned dependency imports because
   that proof remains open. Read `dag/units/sk-prop-cd.json`: its statement, steps,
   and realized fields are untouched; both comparison nodes stay in the same unit,
   and no unit-level route is bypassed. No global pruning is claimed.
5. **DAG: pass.** Compared both node files with the repository. Only permitted fields
   differ: the comparison node's `lean`, and the item's `proof`, `proof_deps`, and
   `proof_origin`. The new theorem signature is recorded verbatim in its existing
   node; its source and full acyclic-resolution proof are documented. The item's
   two proof steps describe exactly the positive-degree choice and independently
   normalized degree-zero construction. There are no new mathematical nodes.

Second reading changed the new module docstring to add its missing blueprint tag
and joined an awkward line break in the new theorem docstring. No proof or
statement needed repair. Scratch axiom probes were removed from the delivery set.
