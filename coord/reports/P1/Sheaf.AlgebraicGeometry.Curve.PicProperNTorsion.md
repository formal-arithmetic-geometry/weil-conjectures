## What changed

Kept the signature of `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion` unchanged and
proved its conjunction from three strict component statements. The second reader proved
`pic_proper_ntorsion_coker` using the existing Picard decomposition and the divisibility
component: cast the integer coordinate modulo n, identify its kernel with the nth-power
image, and use Mathlib's first isomorphism theorem. No definition or existing signature changed.

The three component modules are new. All their proof imports are plain `import`.
Removed the original proof-plan imports from the main module, which now needs only the
three component modules. Removed unused plan imports from the completed cokernel module.
Removed the unused public `Mathlib.GroupTheory.QuotientGroup.Basic` import from the
new torsion and divisibility modules (the main module's existing public imports stay unchanged).
Expanded both remaining open theorems' docstrings into complete natural-language proofs,
made new node statements self-contained, and synchronized all four nodes with the final route.

## Proved and sorry left

Two of four delivered theorem bodies are proved:
- `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion`: conjunction introduction.
- `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker`: decomposition, divisibility,
  and the first isomorphism theorem.

Two named theorems remain `sorry`:
- `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_torsion`, node
  `lem-sc-pic-proper-ntorsion-torsion`.
- `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_div`, node
  `lem-sc-pic-proper-ntorsion-div`.

The completed proofs also rely on open upstream declarations, notably the existing
Picard decomposition. Thus this is a reduction, not an axiom-free closure of the target.

## No longer needed

Removed these proof imports from the main module (and from the completed cokernel module
except `PicardDecomposition`):
- `Sheaf.AlgebraicGeometry.Curve.PicardDecomposition`
- `Sheaf.AlgebraicGeometry.Curve.ProperProjective`
- `Sheaf.AlgebraicGeometry.SmoothProjectiveCurve`
- `Sheaf.AlgebraicGeometry.Variety`
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Final`
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian`
- `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch`
- `WeilConjectures.AlgebraicGeometry.DensePoints`
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`
- `WeilConjectures.AlgebraicGeometry.Picard.Jacobian`
- `WeilConjectures.AlgebraicGeometry.Regular`

Every old main-node proof dependency is replaced as a direct dependency by the three
component nodes:
- `def-sc-curves`
- `lem-sc-proper-dim-one-projective`
- `lem-sc-smooth-regular`
- `lem-weil-pbc-finite-type-over-noetherian`
- `def-pc-curve`
- `def-pc-smooth-projective-curve`
- `lem-pc-rational-points-dense`
- `prop-pc-xk-integral`
- `lem-sc-pic-proper-decomposition`
- `def-sc-pic0`
- `def-sc-jacobian`
- `thm-sc-jacobian-representability`
- `thm-av-final`
- `def-sc-genus`
- `lem-pc-genus-agrees-sc`
- `def-sc-mult-n`

These old nodes are still needed transitively by the open components' mathematical plans;
no whole module or mathematical dependency is claimed globally pruned. The cokernel
node now directly uses only `lem-sc-pic-proper-decomposition` and
`lem-sc-pic-proper-ntorsion-div`; its Jacobian work is delegated to divisibility.

## Where the brief, the DAG or earlier work was wrong

The first delivery left all three geometric conclusions open and merely assembled their
conjunction. Its split-theorem docstrings were too terse to hand over, its new node
statements referred to unspecified "same" hypotheses, and it omitted the updated main
node. Its assertion that the DAG argument is unnecessarily long was unsupported:
the geometry is still needed by the remaining open components. The second reader closed
the cokernel component and repaired the documentation and records.

## New nodes

`lem-sc-pic-proper-ntorsion-torsion` is the strict torsion conjunct. Its proof plan retains
projectivity, integrality, Jacobian representability, genus comparison, the Picard
splitting, and the abelian-variety torsion computation. It remains open.

`lem-sc-pic-proper-ntorsion-div` is the strict degree-zero divisibility conjunct. Its plan
uses the geometry to identify Pic⁰ with Jacobian points, then transports the existing
abelian-variety divisibility theorem. It remains open.

`lem-sc-pic-proper-ntorsion-coker` is the strict cokernel conjunct. It is now proved from
the original Picard decomposition and the divisibility component, with the group-theoretic
calculation formalized directly. No change record is needed: no existing interface changed.

## Second reading by P1

1. **Interfaces:** compared the main module with the repository version by `diff`.
   Its existing theorem signature is byte-for-byte identical. No definition, target, or
   other existing declaration changed. New modules contain only new component theorems.
   Verdict: pass after repair.

2. **Proof checking:** all four files compile with `lcompile.py --all`.
   Printed axioms for all four declarations in a scratch copy: each uses only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` from the named open components or
   existing open dependencies. The only two delivered `sorry`s are the named torsion
   and divisibility theorems. There is no hollow definition or forbidden declaration.
   Verdict: pass as a partial reduction.

3. **Split statements:** inspected all three strict conjuncts against the main signature.
   The same assumptions imply the standard Picard conclusions; n=0 is excluded by the
   nonzero cast, n=1 gives trivial torsion/cokernel and the root L itself, and genus-zero
   torsion is trivial. The dimension-one assumption excludes Spec k and the empty curve.
   Read existing decomposition, Jacobian, and abelian-variety declarations. Searched with
   different LeanFinder and Loogle queries, local `rg`, and the launcher search tools;
   no duplicate geometric theorem was found. LeanSearch was unavailable and is recorded
   as such. Replaced skeletal proof docstrings with full arguments and repaired the nodes.
   Verdict: pass after repair; two true strict components remain open.

4. **Route and pruning:** found and formalized a shorter route for the cokernel using
   Mathlib's first isomorphism theorem, rather than leaving it split. Removed redundant
   main and cokernel proof imports, and listed every replaced direct dependency above.
   Checked `dag/units/sk-thm-curveestimate.json`: its `realized.statement` remains
   `thm-sc-proper-cohomology`, and this proof retains the Picard/Jacobian route below it.
   Verdict: pass after repair.

5. **DAG:** added the updated main node, synchronized its three direct proof dependencies,
   replaced the cokernel node's route with its actual two dependencies, expanded the open
   component plans, and checked all new Lean records against their theorem signatures.
   New records have the required stage-3 fields and proof_deps equal the union of uses.
   Verdict: pass after repair.

Changed: closed the cokernel split, expanded the two remaining proof docstrings and all
node records, added the main node update, and pruned unused main/cokernel proof imports.
