## What changed

Proved `AlgebraicGeometry.Scheme.dim_eq_topologicalKrullDim` using Mathlib's
`topologicalKrullDim`, `Order.krullDim_eq_of_orderIso`,
`Order.krullDim_eq_iSup_coheight`, and `ringKrullDim_stalk_eq_coheight`.
Added `Mathlib.AlgebraicGeometry.Properties` as the proof import. The definition
of `Scheme.dim` is unchanged.

## Proved and sorry left

The theorem `Scheme.dim_eq_topologicalKrullDim` is proved. No sorries remain in
this module.

## No longer needed

The old proof dependencies `lem-weil-pbc-irreducible-closure` and
`def-weil-irreducible-components` are no longer directly needed: the Mathlib
order isomorphism packages the irreducible-closure construction. The dependencies
`lem-sc-scheme-stalk-dimension-generalization-chains`, `lem-sc-scheme-sober`, and
`def-kun-topological-krull-dimension` remain used through their Mathlib matches.
No import present in the repository's current module was removed. The earlier
candidate `WeilConjectures.Mathlib.Topology.KrullDimension` import was tested and
omitted; it is already absent from the repository version being reviewed.

## Where the brief, the DAG or earlier work was wrong

The DAG's three-step chain correspondence is unnecessarily fine for this module;
Mathlib already provides the exact order-theoretic comparison and the stalk/coheight
identity.

## Earlier second reading (a previous round; superseded)

Pending the required independent second reading; the proof compiles and preserves the stated theorem signature.

## Second reading by V1

1. Compared the complete module against the repository version. Every existing
   declaration signature, definition body, and docstring is byte-for-byte
   unchanged. The only Lean changes are replacing the comparison theorem's
   `sorry` with its proof and adding the plain proof import
   `Mathlib.AlgebraicGeometry.Properties`. No change record is needed.
2. Compiled the module locally through `lcompile.py`, with no errors or warnings.
   Scanned for forbidden declarations and `sorry`: none remain. A scratch-copy
   `#print axioms AlgebraicGeometry.Scheme.dim_eq_topologicalKrullDim` reports
   exactly `propext`, `Classical.choice`, and `Quot.sound`. The three definitions
   retain their original data and contain no postponed proofs.
3. There are no new or split-off statements or nodes. Read the Mathlib stalk
   theorem (Properties, Stacks 02IZ), the sober order isomorphism, and the
   supremum-of-coheights theorem. They apply to arbitrary schemes; the latter
   explicitly handles an empty type. Spec of a field gives dimension zero, and
   empty schemes give bottom on both sides. No nonemptiness or finiteness
   hypothesis is introduced.
4. Read the complete proof top downward and searched the project and source
   library for the stalk/coheight and dimension comparison declarations. The
   direct Mathlib composition is a short complete route; no additional Sheaf
   helper is needed. All four public imports support existing definitions or
   the theorem signature; Properties is a plain proof import. The unit
   `sk-def-av-jacobian` has no proof steps and its `realized` fields are empty;
   this subsidiary comparison does not replace a unit statement or step.
   Corrected the pruning list: sober and stalk dimension remain used via their
   Mathlib matches; only the irreducible-closure and component nodes are pruned.
5. The delivered node had retained the obsolete three-step chain proof and
   all old dependencies. Replaced `proof`, `proof_deps`, and `proof_origin` with
   the actual order-isomorphism, coheight-supremum, and stalk-equality route.
   Every other node field, including its statement and Lean signature, stays
   unchanged. No new-node checks are applicable.

Second reading changed only the DAG proof metadata and corrected the report's
pruning claims. The Lean proof was sound and is unchanged.
