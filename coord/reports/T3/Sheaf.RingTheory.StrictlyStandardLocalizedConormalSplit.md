## What changed

Proved `Algebra.Presentation.strictlyStandard_localized_conormal_split` in
`Sheaf.RingTheory.StrictlyStandardLocalizedConormalSplit` with its signature unchanged.
Retained the existing proof-only import of
`Sheaf.LinearAlgebra.Matrix.LeftInverseMinors` and added the proof-only import
`Mathlib.LinearAlgebra.Matrix.ToLin`. The proof constructs the initial-relation map E,
proves it surjective by ideal-span and tensor induction, converts the scalar Jacobian
left inverse into g D E = id after localization, and checks E g D = id on preimages.
Updated the node proof and dependencies to match. No definitions or interfaces changed.
The standard basis constructions cover c = 0 and zero localizations without extra assumptions.

## Proved and sorry left

Closed: `Algebra.Presentation.strictlyStandard_localized_conormal_split` (one of one
original holes). Added holes: none. Remaining holes in delivered Lean modules: none.
This is a proof, not a decomposition. The existing scalar matrix lemma is used as stated;
its dependencies remain the library's responsibility. The local compile passes without
warnings and stays within the 60-second file limit. The dependent span argument uses a
local transparency option and a documented heartbeat limit; no kernel checks are disabled.

## No longer needed

Pruned `lem-weil-pbc-localization-module-tensor` from this node's proof dependencies:
the proof works directly with A_a tensor I/I^2 and uses pure-tensor induction, without
transporting through a separate localized-module isomorphism. Its Mathlib match is
`IsLocalizedModule.isBaseChange`; there is no Sheaf module to remove.
No original public imports were removed. The exploratory proof-only import of
`Mathlib.LinearAlgebra.TensorProduct.Tower` was removed before delivery.
The polynomial differential basis and matrix-left-inverse-minors nodes remain needed.
No module is claimed globally unreachable, since other callers may use it.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect found. The final DAG step unnecessarily proposed
constructing an inverse equivalence of E: surjectivity of E already suffices to verify
E g D = id. The local literature checkout lacks smoothing.tex, so the source was read
at [Stacks 07CA](https://stacks.math.columbia.edu/tag/07CA) and
[Stacks 07ET](https://stacks.math.columbia.edu/tag/07ET). These give exactly the generation
and scalar-left-inverse argument used here. No new sourced holes were introduced.

## Second reading by T3

1. **Visible interfaces: pass.** Compared the complete delivered module with the
   repository module using `diff`, and separately checked the theorem signature
   byte for byte. The rings, universes, presentation, bound `hc`, minor formula
   (including its transposed index order), remaining-relation condition, and
   localized left-inverse conclusion are identical. There are no other declarations,
   new definitions, change records, or adapted modules. All original public imports
   stay; `Matrix.ToLin` is a new ordinary proof-only import.
2. **Proof: pass.** Read every proof block and compiled the delivered file locally
   with `lcompile.py`: exit 0, no warnings, 47.3 seconds. The ideal-span induction
   uses the polynomial-ring action and then its quotient A-action correctly.
   The relation decomposition kills exactly the kernel square; multiplication by
   the unit image of a puts every relation class into range E. Cotangent-span and
   tensor induction then give surjectivity. The matrix of D E is computed in the
   base-changed polynomial basis; determinant transposition matches `hminor`.
   The equation B M = a id is mapped to the localization and rescaled, and the
   final identity is checked on preimages under E. No forbidden declarations,
   sorry, data definitions, or kernel-check bypasses occur in the delivered file.
   A scratch copy with `#print axioms` compiled in 45.0 seconds: the theorem
   and `Matrix.scalar_left_inverse_maximal_minors` both use exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. Thus the delivered hole is
   closed relative to the existing matrix dependency, whose transitive proof
   remains open; this is not an axiom-free closure of the entire dependency tree.
   The selected matrix B occurs only inside this existential theorem's proof;
   no public data are defined by choosing an arbitrary witness.
3. **Split-off statements: pass, none.** No new statements, nodes, or holes are
   introduced. Checked c = 0, m = 0 (forcing c = 0), and a = 0 / the zero
   localization: the span argument still gives surjectivity, empty matrix identities
   remain valid, and localization makes the image of a a unit even in the zero ring.
4. **Route and pruning: pass.** Read the first paragraph of
   [Stacks 07CA](https://stacks.math.columbia.edu/tag/07CA) and the matrix statement
   [Stacks 07ET](https://stacks.math.columbia.edu/tag/07ET). They give precisely the
   generation and scalar-left-inverse steps implemented here. Independently searched
   LeanFinder for a splitting from a surjective generator map and searched the
   library and Mathlib cotangent/smoothness files. Mathlib's `cotangentCompAwaySec`
   splits the added localization relation, and its submersive-presentation results
   require different presentation data; neither replaces this argument for the
   specified original conormal map. The last three-line preimage argument already
   avoids building an inverse equivalence. Read `dag/units/sk-thm-p1.json` and its
   `realized` fields: neither this auxiliary node nor the pruned localization-tensor
   node realizes a unit step, and every unit step remains intact. The only removed
   old proof dependency is `lem-weil-pbc-localization-module-tensor`; it has a
   Mathlib match rather than a Sheaf module, so no module is claimed pruned.
5. **DAG: pass.** Compared the old and delivered node. Only `proof`, `proof_deps`,
   and `proof_origin` change. The first step retains the polynomial differential
   basis and matrix-minors nodes, exactly as used by the Lean proof. The other
   steps give the actual ideal-span/tensor induction and preimage calculation;
   their elementary status is appropriate. The statement, statement dependencies,
   Lean record, source, chapter, unit, and all other node fields are unchanged.

Second-reading changes: corrected the report's claim that the already-existing
matrix-minors import was added, and corrected the pruned node's Mathlib match to
`IsLocalizedModule.isBaseChange`. No Lean proof or node repair was necessary.
