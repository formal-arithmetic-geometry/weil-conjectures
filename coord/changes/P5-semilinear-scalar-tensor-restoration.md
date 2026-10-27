# Restore the representative-normalized scalar tensor comparison

The returned delivery `84edc36ad6a` was based before batch rollback
`a62c78b1fa2`, which removed `Sheaf.Paper.SemilinearScalarTensor` and its node.
The current source has no quarantine copy or rework row for this item, and its
module claim is already held by P5. Restore the retained item under its original
path with the original declaration and node attachment. Its source was compared
byte-for-byte with the returned commit before the timing repair.

The restored theorem is
`WeilConjectures.SemilinearSections.semilinearScalarTensor`. Its statement,
universes, visibility and original public import are unchanged. The proof closes
the original hole without adding holes or changing any public definition. The
private ordinary normalization proof now composes explicit section equalities
to avoid repeatedly rewriting the nested comparison. No other module is changed.

No currently existing consumer needs adaptation: the restored declaration has
its original interface. The node retains its statement and Lean attachment, with
the proof plan and dependencies from the delivered proof. No node is withdrawn,
no quarantine archive is deleted, and no source-library declaration is changed.
