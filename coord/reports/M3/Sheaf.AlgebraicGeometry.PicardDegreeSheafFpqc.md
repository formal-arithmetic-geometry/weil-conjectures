## What changed

The target module now proves the sheaf condition by reducing `IsSheaf` to existence and uniqueness of amalgamations over each fpqc sieve. Two proof-only helper modules state those two descent obligations and are imported by the target.

## Proved and sorry left

Closed hole: `AlgebraicGeometry.isSheaf_fpqc_sheafify_picardDegree`. Added holes:
`AlgebraicGeometry.exists_amalgamation_fpqc_sheafify_picardDegree`
(node `lem-pd-degree-picard-sheaf-fpqc-existence`) and
`AlgebraicGeometry.unique_amalgamation_fpqc_sheafify_picardDegree`
(node `lem-pd-degree-picard-sheaf-fpqc-uniqueness`). The target proof applies these two helpers.
This is a decomposition of one hole into two strictly smaller obligations, with net holes
closed minus added equal to -1; it is not a completed proof free of `sorryAx`.

## No longer needed

Removed direct target proof imports: `WeilConjectures.AlgebraicGeometry.DensePoints`,
`WeilConjectures.AlgebraicGeometry.Descent`, `WeilConjectures.AlgebraicGeometry.Picard.Defs`,
and `WeilConjectures.AlgebraicGeometry.Picard.RationalPoint`. These are retained as plain proof
imports in each helper, so no geometric module is pruned from the import closure.

The original direct target `proof_deps` were `lem-pc-fpqc-descent`, `lem-pc-rational-hyp`,
`thm-pc-pic-split`, `lem-pd-degree-locally-constant`, and `lem-pc-dense-separable-points`.
The reduction directly uses none of them; its dependencies are now the two helpers. All five
original nodes remain needed in the helper plans (the degree node in existence).
Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The original node bundled existence and uniqueness into one long proof step. The Lean reduction makes both obligations explicit, while preserving the target statement unchanged.

## New nodes

`lem-pd-degree-picard-sheaf-fpqc-existence` and `lem-pd-degree-picard-sheaf-fpqc-uniqueness` are strict subclaims of the target's amalgamation criterion, with sources and proof plans recorded in their DAG files.

## Earlier second reading (a previous round; superseded)

The target proof compiles in the sandbox. The two added declarations are strict existence and uniqueness subclaims, and the target applies them through the standard `isSheaf_iff_isSheaf_of_type` criterion without changing its signature.

## Second reading by M3

1. **Signatures and statement preservation.** Compared the delivered target with the repository
   version. The target theorem signature is byte-for-byte unchanged. The two added helper
   statements are strict existence and uniqueness parts of the standard amalgamation criterion;
   neither changes the target or weakens an existing declaration. Verdict: pass.
2. **Proof and axioms.** Compiled all three sandbox modules with `lcompile.py --all`. The target
   proof is complete; the only remaining `sorry`s are the two explicitly named helper theorems,
   each documented and represented by a split DAG node. No definitions, axioms, unsafe or opaque
   declarations were added. A scratch-copy `#print axioms` probe on all three declarations shows
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. Verdict: pass subject to
   the two recorded split holes.
3. **New statements and prior art.** Checked the helper declarations against the existing
   library and the generic `isSheaf_iff_isSheaf_of_type` criterion. The helpers state only the
   existence and uniqueness obligations required by the target and are not duplicate library
   declarations. Fresh Lean Finder, Loogle, and Mathlib grep searches found generic criteria
   but no geometric result closing these obligations; LeanSearch returned an Internal Server
   Error, recorded as unavailable. For the identity covering sieve, both
   claims reduce to restriction along the identity. For an empty test scheme the normalized
   Picard functor is a singleton and the degree condition is vacuous; arbitrary integers `d`
   cause no failure. The proof works over imperfect fields using a finite separable point and
   requires no rational point over the original field. Verdict: pass.
4. **Pruning and imports.** The target now imports the helpers only for its proof. The original
   geometric proof imports were moved as plain proof imports to both helper modules, where their
   planned descent proofs need them. The degree base-change node is
   retained in the existence plan; no module has been pruned. Verdict: pass.
5. **DAG and unit route.** Verified that the target node's `proof` and `proof_deps` name the two
   helper nodes, and that each helper node records its exact Lean declaration, source, proof plan,
   and split status. Read `dag/units/sk-prop-jacobian-descent.json`; its `realized` arrays
   are empty, and this delivery changes no unit statement or step. The original geometric
   descent route is retained inside the helper plans. Verdict: pass.

Changed the two helper import lists to retain the four original proof-only descent imports,
expanded both proof docstrings, removed circular wording from the uniqueness node plan, retained
the degree base-change node in the existence plan, corrected the pruning and hole accounting,
and added this second-reading record. No Lean statement or proof body changed.
