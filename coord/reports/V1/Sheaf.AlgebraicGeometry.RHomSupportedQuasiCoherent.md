## What changed

The original theorem `AlgebraicGeometry.rhom_supported_quasiCoherent` now assembles
three strictly smaller components, in three separate new modules:
`RHomSupportedQuasiCoherentPseudoPart`, `RHomSupportedQuasiCoherentPerfectPart`, and
`RHomSupportedQuasiCoherentSupportPart`. Its original signature and docstring are
preserved byte for byte. Public imports of the existing module are unchanged.

The second reader proved support preservation by exact restriction, detection of
zero by derived cohomology, the restriction isomorphism, and an explicit zero
K-injective complex. Three private proved helpers show that internal Hom of sheaves,
Hom complexes, and derived internal Hom into zero are zero. The new support theorem
needs neither quasi-coherence nor a pseudo-coherent/perfect case assumption.
No definition or existing statement changed, and no change record is needed.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.rhom_supported_quasiCoherent`
(node `lem-sc-rhom-supported-qcoherent`). Its proof is an assembly, not an independent
axiom-free proof of the mathematical theorem.

Additional component proved: `AlgebraicGeometry.rhom_supported_quasiCoherent_support_part`
(node `lem-sc-rhom-supported-qcoherent-support-part`). It depends on the existing
open theorem `CategoryTheory.derivedInternalHom_restrict_open`.

Holes added and still open:
- `AlgebraicGeometry.rhom_supported_quasiCoherent_pseudo_part`
  (node `lem-sc-rhom-supported-qcoherent-pseudo-part`).
- `AlgebraicGeometry.rhom_supported_quasiCoherent_perfect_part`
  (node `lem-sc-rhom-supported-qcoherent-perfect-part`).

Each remaining hole is a public named theorem with an explicit source and full
natural-language argument. There is no hole in a definition or in a partial proof.
This is a decomposition: one original hole closed and two lower holes added,
a syntactic net of -1. This report claims no positive ledger progress or full
axiom-free proof of the target. The support hole of the first worker's proposal
was closed by the second reader and is not added by the final delivery.

## No longer needed

The original module's five plain imports are removed from that module:
`Sheaf.AlgebraicGeometry.AffinePseudoCoherentRHomQuasiCoherent`,
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`,
`Sheaf.AlgebraicGeometry.DerivedCategory`,
`Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh`, and
`Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison`.
The affine and perfect proof dependencies now belong to the relevant new components;
the derived-category declarations remain available through unchanged public imports.
Three plain imports of the new component modules replace them.

All eight old proof dependencies are replaced as direct dependencies of the assembly:
`def-pur-pseudo-coherent-complex`, `def-pc-derived-category`,
`lem-pc-affine-qcoh-derived-equivalence`, `lem-sc-derived-internal-hom-restrict-open`,
`lem-sc-affine-pseudo-coherent-rhom-qcoherent`, `def-pc-perfect-complex`,
`lem-pc-perfect-rhom-tensor-comparison`, and `lem-pc-derived-pullback-tensor-qcoh`.
They remain needed through component proofs or statement definitions. Thus no old
node or module is globally pruned. Proof-only restriction and tensor/affine imports
in new modules are plain imports, not public imports.

## Where the brief, the DAG or earlier work was wrong

The first proposal put three new declarations inside the existing module, displaced
its docstring, used ordinary comments instead of theorem docstrings, provided generic
rather than component-specific node proofs, and recorded insufficient statement and
proof dependencies. Its report called the conjunction assembly a proof without
reporting the one-closed/three-added decomposition. These issues are repaired.
Actual second-reader searches replaced the earlier generic search records.

The affine and perfect components still require implementation of the local-to-global
and model-comparison argument; no immediate Mathlib or upstream theorem supplies them.
The original unit `sk-thm-picard-duality` and its `realized` fields are unchanged:
the item is below that unit and is not a realized unit statement or step. The existing
finite-duality ancestor and proper-flat support route remain in force.

## New nodes

`lem-sc-rhom-supported-qcoherent-pseudo-part` carries the affine/local argument for
quasi-coherence and local lower bounds. It does not claim a uniform global bound.
Its declaration is in `Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPart`.

`lem-sc-rhom-supported-qcoherent-perfect-part` carries just the perfect-source
quasi-coherence argument using the dual and derived tensor, for arbitrary L with
quasi-coherent cohomology. Its declaration is in
`Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart`.

`lem-sc-rhom-supported-qcoherent-support-part` carries the proved support argument,
without unnecessary case hypotheses. Its declaration is in
`Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentSupportPart`.
No change records or forced adaptations are included.

## Second reading by V1

1. Compared the delivered item against the read-only repository using diff and an
   exact textual signature comparison. The existing declaration's signature is
   byte-for-byte identical, including whitespace before `:=`; its original docstring
   is restored to that declaration. No definitions or existing public imports changed.
   Read the DerivedInternalHomImports change record: it leaves the used API unchanged.
2. Compiled each module through lcompile in import order. The two listed named
   component theorems are the only source sorries. No axiom, unsafe, opaque, extern,
   implemented_by, or hollow definition was introduced. The support helpers construct
   the zero complex directly; its K-injectivity is proved by the reflexive zero homotopy.
   The Hom-complex data are obtained from the existing proved product-characterization
   theorem, which determines the complex up to the required isomorphism. Explicit #print axioms on scratch copies of all four public theorems showed
   exactly propext, Classical.choice, Quot.sound, and sorryAx. The delivery tool also
   ran its exhaustive axiom probe on each module.
3. Read Stacks perfect.tex, lemma-quasi-coherence-internal-hom (0A6H), statements
   (1),(2) and proof, and lemma-map-from-pseudo-coherent-to-complex-with-support
   (0A9C), proof's first paragraph. Pseudo-coherence, quasi-coherence, the existential
   global bound on L, local bounds on RHom, and the unbounded perfect case match those
   places. The support argument is valid without either case assumption. Tested the
   empty scheme, empty/full closed subsets, zero second argument, and degree shifts:
   support is vacuous on the empty complement; on T empty it follows from zero L;
   pseudo-coherent model upper bound b and target lower bound a give a-b; arbitrary
   shifts change the local bound, and non-quasi-compact X does not give a uniform bound.
   Ran LeanSearch (HTTP 500, recorded as unavailable), LeanFinder, Loogle and grep with the recorded distinct queries, searched
   lean/Sheaf, lean/WeilConjectures, the upstream checkout, DAG nodes and blueprint
   units. No duplicate independent theorem was found; PseudoCoherentRHomQuasiCoherent
   uses this item and cannot be used back without a cycle.
4. Read the original dependency modules and unit record. Kept the original affine
   and perfect routes in the two open components. Support now follows a shorter,
   complete argument using the existing restriction theorem and zero-complex model.
   New imports are separated according to statement versus proof use; all old direct
   dependencies removed from the assembly are listed above, with their continuing
   component/definition use. No unit is bypassed and no global module is pruned.
5. Checked each node's Lean declaration and verbatim signature, source, component
   proof, and proof-dependency union. The main node names exactly the three component
   declarations used by its conjunction proof. New nodes are self-contained, in the
   item's chapter/unit, have real search records, and retain the finite-duality
   blueprint ancestor. Their statements are proper portions of the argument, not
   alternative names for the full target.

Changes by this reading: moved each new statement to its own module, restored the
original docstring and exact signature, wrote full theorem docstrings and node proof
records, corrected dependencies and actual searches, minimized imports, proved the
support component and removed its unnecessary case hypothesis, and corrected the
report to count the decomposition honestly.
