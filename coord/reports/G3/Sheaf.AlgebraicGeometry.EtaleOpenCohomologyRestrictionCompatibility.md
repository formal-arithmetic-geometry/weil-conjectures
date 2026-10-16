## What changed

Proved `AlgebraicGeometry.etaleCohomologyOverOpenEquiv_restriction` in
`Sheaf.AlgebraicGeometry.EtaleOpenCohomologyRestrictionCompatibility`, preserving its
signature and existing comparison/restriction definitions. The degree-zero proof computes
the sections comparison, and the higher-degree proof uses connecting-map compatibility
and dimension shifting through an injective presentation.

Repair of the maintainer's return: removed the duplicate private
`AlgebraicGeometry.sectionsEquiv_precomp` and replaced its call with
`AlgebraicGeometry.Etale.sectionsEquiv_precomp`, imported from
`Sheaf.AlgebraicGeometry.AbelianRepresentableGeneratorCoherence`. Both existing copies
were private. In that unclaimed module, removed only `private` from the existing proved
lemma; its binders, conclusion, docstring and proof are unchanged. The existing generator
node's `lean.declarations` now includes this helper from its proof step 3.
The item's node records this dependency. No new statement or node is introduced.

Proof-only imports added relative to the original item:
`Sheaf.AlgebraicGeometry.ConstantSectionAdjunctPullback` and
`Sheaf.AlgebraicGeometry.AbelianRepresentableGeneratorCoherence`.
The public comparison import is unchanged. The visibility change is documented in
`coord/changes/sectionsEquiv-precomp-reuse.md`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.etaleCohomologyOverOpenEquiv_restriction`
(node `lem-weil-pbc-etale-open-comparison-restriction`).

All private helpers are proved. No `sorry` remains in either delivered Lean module and no
hole is added. This is a proof, not a decomposition. The imported existing comparison
construction retains its transitive obligations; this delivery does not claim to close
those. The exposed `AlgebraicGeometry.Etale.sectionsEquiv_precomp` was already proved.

## No longer needed

Removed three redundant direct proof imports, whose declarations remain available through
the unchanged public comparison import:

- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective`;
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`;
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`.

Removed the duplicate private `AlgebraicGeometry.sectionsEquiv_precomp`; the existing
proved theorem is reused. No original proof-dependency node or module is pruned from the
target closure. Explicit comparison of whole injective-resolution section complexes is
unnecessary: connecting-map compatibility and induction prove the canonical statement.
`EtaleOpenSectionPullback`, `EtaleOpenFreeSheafUnitCoherence`, and
`EtaleResolutionSectionCanonicalOpenToOpenCycle` are not direct imports of the item;
the repaired proof uses generator coherence for the common sections identity.

## Where the brief, the DAG or earlier work was wrong

The previous delivery duplicated the sections-precomposition identity. The returned
`import_prune_check.py` finding is correct: the statements are the same, with no difference
hidden in variables or open namespaces. The repair exposes and reuses the existing lemma
rather than proving it again. The old second-reading section described the unrepaired
version and has been removed so that a new independent reading can assess this repair.

No mathematical error was found in the main statement. Existing section-unit theorems for
literal `X.Opens` do not apply directly to arbitrary presentations `j : U ⟶ X` and
`k : V ⟶ U`; the proof retains the arbitrary-immersion unit calculation. The unit record
`sk-prop-cd` has no realized statement or step at this node, and no unit route is changed.

The delivery tool's documented `WEIL_DELIVERY_CACHE_DISABLE=1` fallback is retained for
validation because the previous session observed cache lookup restarts as the base
advanced. It performs full scans; no compile, axiom or preflight check is skipped.

## Second reading by G3

1. **Statements and signatures.** Compared both delivered modules and both node files with the
repository versions. The target theorem and all existing declarations retain their signatures;
the only visibility change is the declared exposure of the already proved
`AlgebraicGeometry.Etale.sectionsEquiv_precomp`. Verdict: unchanged statements, with the
visibility adaptation documented in `coord/changes/sectionsEquiv-precomp-reuse.md`.

2. **Proof and axioms.** Compiled the two sandbox modules with `lcompile.py --all`; both compile
without errors. The item has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by`, and the adapted helper remains proved. Verdict: the target proof is complete;
no new hole or hollow definition was introduced.

3. **New statements and reuse.** No new theorem statement or node was added. The duplicate
private sections-precomposition lemma was removed and the existing proved theorem is reused;
its declaration is recorded in the generator-coherence node. Verdict: no duplicate split-off
statement remains, and the reused identity is exactly the needed strength.

4. **Pruning and imports.** Checked the proof imports against the declarations used and the
node `proof_deps`. The three redundant direct imports removed from the item are available through
the unchanged public comparison import; the two added proof imports are used. Verdict: imports
are minimal for this proof, and the listed no-longer-needed material is complete.

5. **DAG and route.** Compared the item and generator-coherence nodes with the Lean proof,
including `proof`, `proof_deps`, `proof_origin`, and the helper declaration record. The unit
route is unchanged and no realized unit step is bypassed. Verdict: DAG and Lean agree; the
specified comparison is proved by degree zero plus connecting-map compatibility and induction.

Changed after this reading: added this review record only; no Lean proof or statement was
changed.
