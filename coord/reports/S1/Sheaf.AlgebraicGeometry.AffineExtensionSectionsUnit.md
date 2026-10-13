## What changed

Replaced the sorry in AlgebraicGeometry.exists_affineExtensionSectionsUnit by a complete
Lean reduction. The comparison is the transpose of the normalized pullback unit. Its
naturality is proved from both adjunction naturality lemmas, unit naturality, and r's
naturality. Invertibility transports along an actual affine model isomorphism; the
adjunction inverse-law proves the required unit equation with the original signature.

Added AffineQCohComplexModel, whose theorem exists_affineQCohComplexModel is proved from
AffineQCohDerivedEquivalenceCore and the source module K-flat resolution theorem.
Added AffineExtensionSectionsModelMate for the remaining computation on K-flat models.
Updated the parent proof route and supplied the two new node records.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.exists_affineExtensionSectionsUnit
(lem-pc-affine-extension-sections-unit), from one strictly smaller model computation.
Also proved AlgebraicGeometry.exists_affineQCohComplexModel
(lem-pc-affine-qcoh-complex-model), with no new hole.

One new hole remains: AlgebraicGeometry.affineExtensionSections_model_mate_isIso
(lem-pc-affine-extension-sections-model-mate). It concerns only an explicit termwise
tilde of a K-flat module complex, not an arbitrary quasi-coherent derived object. It
has no existential choice of comparison and contains neither model construction nor
transport to arbitrary Q. The item itself has zero sorries. This is a decomposition:
one old hole closed, one new hole added, net zero holes; not an unconditional proof.

The zero complex gives a map between zero objects, hence an isomorphism. For the
identity ring map the mate is the usual affine unit comparison. K-flatness, rather
than flatness of g or boundedness of M, is what computes the general pullback. The
new statements add none of these latter assumptions.

All three delivered modules compile via lcompile.py. No signature or definition of
an existing declaration is changed. No forced adaptation is needed.

## No longer needed

Removed direct proof imports AffineQCohDerivedEquivalence and
AffineDerivedPullbackTensorTilde from AffineExtensionSectionsUnit; their model-level
uses are retained in AffineExtensionSectionsModelMate. AffineQCohComplexModel uses
AffineQCohDerivedEquivalenceCore instead of the shift-normalized affine equivalence.
No original dependency module is globally pruned: the pending model computation
still needs both original plan dependencies. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The affine pullback computation
alone does not encode normalized unit compatibility; that remains the model-mate
item. The planned representation and the transport to arbitrary Q are now actual
Lean proofs. The advertised repository literature source was absent locally; its
Stacks perfect.tex source was read from the upstream source into the sandbox's
scratchpad. LeanSearch returned Internal Server Error; the other searches worked.

## New nodes

lem-pc-affine-qcoh-complex-model records the proved K-flat representative construction
from Tag 06Z0 and the existing source resolution theorem. Its new module is
Sheaf.AlgebraicGeometry.AffineQCohComplexModel. The ordinary Gamma-ring representative
already in AffineModuleComplexRepresentative is not the same interface: here the
complex uses the specified original ring and is K-flat.

lem-pc-affine-extension-sections-model-mate records invertibility of the normalized
unit transpose on K-flat tilde models, with the affine resolution argument of Tags
06Z0, 08DV, 08DW and 0AA7 in its docstring and node. Its new module is
Sheaf.AlgebraicGeometry.AffineExtensionSectionsModelMate. Three search kinds and
blueprint-wide searches are recorded. No change record is required.

## Second reading by S1

1. I compared the delivered `AffineExtensionSectionsUnit.lean` with the repository version. Existing declaration signatures are unchanged byte for byte; only proof imports and proof bodies changed. The two added modules and node records are new declarations.

2. I compiled all three delivered modules with `lcompile.py --all`; they compile cleanly. The only remaining `sorry` is the named split theorem `AlgebraicGeometry.affineExtensionSections_model_mate_isIso`, and no definition contains `sorry`.

3. The split statements are strictly smaller than the parent: the model-mate theorem fixes a K-flat tilde model, while the complex-model theorem supplies that representative. Their statements match their Lean declarations and node records, and the model-mate docstring records the source and proof obligation. No duplicate declaration was found in the library.

4. The parent proof follows the planned route through the affine K-flat model, naturality transport, and the model-mate theorem. The unit route remains realized; no original plan dependency was bypassed. The removed direct imports are replaced by the new model-level imports, as recorded above.

5. The DAG `proof`, `proof_deps`, and `proof_origin` fields agree with the proof bodies. The new nodes contain source, blueprint, search, creation, and Lean records required for a stage-3 split. No statement or definition change record is needed.

I changed only the proof/imports and added the two model modules, their node records, and this second-reading report section; no existing interface was altered.
