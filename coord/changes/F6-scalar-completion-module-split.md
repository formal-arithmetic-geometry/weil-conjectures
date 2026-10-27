# Scalar completion normalization module split

The item `Sheaf.Paper.CompactSupportScalarProjectionIdentification` exceeded the
60-second compile limit after its scalar-completion hole was proved. Its scalar
normalization component is moved to the new module
`Sheaf.Paper.CompactSupportScalarCompletionNormalization`, publicly imported by
the item. The item also imports all of it to reuse the proved private reflector,
unit and naturality helpers needed by the remaining proper/open proofs.

The public names `WeilConjectures.PurScalarProjection.scalarCompletion_existsUnique`
and `WeilConjectures.PurScalarProjection.scalarCompletion` keep exactly their
original signatures. The definition body is unchanged. `scalarTensorCompleted`
and its tensor helpers stay in the item. The first theorem is now proved from
the fully proved scalar-unit existence comparison and the actual completion
reflector. Its original scalar naturality proof is unchanged. The normalization
node carries these two moved Lean attachments; the parent gains only the resulting
structural statement dependency. The parent theorem statement and its definitions
retain their original meaning. The larger integral coefficient-comparison theorem
is not a dependency of the new node; all new nodes have no path back to the parent.

No other existing module or node is changed. A direct-importer search for the
item module found no current Lean importers; its DAG parents are retained.
No source-library declaration is changed. All new modules are fully proved,
and the four other original holes remain in the item.
