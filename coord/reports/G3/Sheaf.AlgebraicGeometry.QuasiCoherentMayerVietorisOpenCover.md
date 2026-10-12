## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.QuasiCoherentMayerVietorisOpenCover` with a proof of
`AlgebraicGeometry.Scheme.quasiCoherent_mayerVietoris_openCover` from
`AlgebraicGeometry.RingedSpace.module_mayerVietoris`, applied to
`W.toScheme.toRingedSpace`. Evaluate its natural-transformation connecting maps at
quasi-coherent modules. The initial injection and all three exactness positions are
its corresponding conclusions. Module naturality is the symmetric naturality
identity of the connecting natural transformation; restriction compatibility is
obtained by evaluating its cover-restriction identity at the module.

The signature, docstring, visibility, and imports are unchanged. The existing DAG
plan is followed exactly, so no node update is required. The unit's route is kept.
Compiled the sandbox module successfully through `lcompile.py`.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.quasiCoherent_mayerVietoris_openCover`
(node `lem-sc-mayer-vietoris-open-cover`). No sorry remains in the delivered module.
No holes added or split off. This is a proof from the existing named ringed-space
Mayer–Vietoris theorem, not a proof of its remaining transitive dependencies.

## No longer needed

None. The sole proof import `Sheaf.Topology.ModuleMayerVietoris` is used.
The public imports `Sheaf.AlgebraicGeometry.Coherent`,
`Sheaf.Topology.OpenModuleCohomology`, and `Mathlib.Algebra.Exact.Basic` supply
notions appearing in the unchanged statement. The sole planned proof dependency,
`lem-sc-mayer-vietoris-ringed-space`, is used; no planned node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The named ringed-space theorem is
already implemented in the current repository and exactly supplies the required
sequence and cover naturality. Naturality in the module is encoded by its
connecting maps being natural transformations.

Searches via leanfinder, loogle, and grep found Mathlib's generic site
Mayer–Vietoris primitives, which do not provide a shorter matching specialization.
The literature files at the node's recorded local paths are absent on this machine;
the existing node and module docstrings provide the specialization plan used here.

## Second reading by G3

1. **Interface and accidental changes.** Compared the delivered module byte-for-byte against the repository version. The theorem signature, docstring, visibility, and imports are unchanged; only the `by` proof replacing the sole `sorry` differs. Verdict: pass.

2. **Compilation and proof status.** Compiled the module with `lcompile.py`; it succeeds without errors or warnings. The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. It specializes `module_mayerVietoris` to `W.toScheme.toRingedSpace`, evaluates the connecting natural transformation at quasi-coherent modules, uses its injectivity/exactness fields, and derives restriction compatibility by natural-transformation equality followed by evaluation. Verdict: pass.

3. **Statement and proof dependencies.** The target statement is unchanged and exactly the scheme specialization of the ringed-space theorem: all displayed maps, exactness clauses, module naturality, and cover restriction are supplied with the same open-set expressions. The proof uses the recorded dependency `lem-sc-mayer-vietoris-ringed-space` through `module_mayerVietoris`; no new statement or split-off theorem was added. Verdict: pass.

4. **Pruning and imports.** The proof-only import `Sheaf.Topology.ModuleMayerVietoris` is used directly. The three public imports remain necessary for notions in the unchanged public statement (coherent modules, open-module cohomology, and exactness). No old proof dependency or module is unused, so no pruning is recorded. Verdict: pass.

5. **Unit route and DAG agreement.** The unit route is preserved: this node remains the scheme specialization of the ringed-space Mayer–Vietoris node. The node's `proof`, `proof_deps`, and `proof_origin` agree with the written proof, and the unit's `realized` route is unchanged. Verdict: pass.

Changed in this second reading: appended this review record only; no Lean or DAG repair was needed.
