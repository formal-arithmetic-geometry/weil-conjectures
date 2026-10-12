## What changed

Added two proof-only split-off modules. `localization_cone_construction` supplies the
finite-free cone, distinguished triangle, global pseudo-coherence, and lowered vanishing.
`localization_cone_local` supplies the local pseudo-coherence conclusion. The target theorem
combines these two intermediate results without changing its signature.

## Proved and sorry left

`DerivedCategory.isMPseudoCoherent_localization_cone_step` is proved. The two strictly
smaller intermediate theorems remain as named `sorry`s:
`DerivedCategory.localization_cone_construction` and
`DerivedCategory.localization_cone_local`.

## No longer needed

None. All original proof imports remain needed by the split-off statements or target.

## Where the brief, the DAG or earlier work was wrong

The imported proof plan spans construction and local pseudo-coherence in one theorem. The
Lean proof exposes those as two independently stated substeps so the target proof is a real
combination rather than a renamed copy of the target hole.

## New nodes

`lem-pc-m-pseudo-coherent-localization-cone-construction`
`lem-pc-m-pseudo-coherent-localization-cone-local`

## Earlier second reading (a previous round; superseded)

The target signature is unchanged and the target proof combines two strictly smaller
statements. All three sandbox modules compile with `lcompile.py`; the only remaining sorries
are the two named intermediate theorems, each documented and represented by a new node.

## Second reading by E3

1. The target and existing declaration signatures were compared byte for byte with the repository; the target signature is unchanged. The two split-off declarations are strict reductions: one constructs the triangle and global properties, and the other derives only the localized conclusion.
2. All three sandbox modules compile with `lcompile.py`; no forbidden declarations occur. The target has no `sorry`; only the two explicitly named split-off theorems retain `sorry`, each with a source docstring and DAG node.
3. The split-off statements were checked against their Lean signatures and corrected in the DAG to describe strictly smaller interfaces. They are needed for the target combination and introduce no duplicate library theorem.
4. The target proof follows the construction then local pseudo-coherence route, preserving the unit's cone-step route. No imports were removed because every existing import is used by a split-off declaration or the target.
5. The DAG `lean`, `proof`, `proof_deps`, and `proof_origin` fields agree with the delivered declarations; the corrected node prose now matches the decomposition.

Changed the two new node descriptions and proof dependency lists; no Lean proof text was changed during second reading.
