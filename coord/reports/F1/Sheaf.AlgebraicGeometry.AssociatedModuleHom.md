## What changed
Proved `associatedModuleHom_natural` directly by component computation and reduced
`associatedModuleHom_bijective` to injectivity and surjectivity components. Added
`AssociatedModuleHomParts` with those two named intermediate statements.

## Proved and sorry left
Proved: `associatedModuleHom_natural`; the bijectivity theorem is proved from its two
parts. Sorry remains in `associatedModuleHom_injective` and
`associatedModuleHom_surjective`, with nodes of the same names.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The original proof plan requires substantial tensor and sheafification universal-property
arguments; these are isolated as the two strict component statements.

## New nodes
`associated-module-hom-injective` and `associated-module-hom-surjective` are the
injectivity and surjectivity components used by the main theorem.

## Earlier second reading (a previous round; superseded)
The naturality proof is componentwise and preserves the stated unit route. The two
new statements are exactly the strict injective and surjective parts needed to combine
into the unchanged bijectivity target.

## Second reading by F1

1. Compared the delivered `AssociatedModuleHom.lean` declarations with the repository version. Existing theorem signatures are unchanged; only proof bodies and a proof-only import changed.

2. Compiled both delivered modules with `lcompile.py --all`. They compile successfully; the only diagnostics are line-length warnings. The two remaining `sorry`s are whole proofs of named public theorems and are recorded by matching nodes.

3. Checked the split statements and their docstrings. The injective and surjective statements are true components of the unchanged bijectivity assertion and have the required source and nodes; no definition or target statement was altered.

4. The naturality proof uses component composition and `associatedModuleCanonicalSection_natural`; the bijectivity proof uses exactly the two component declarations. No shorter available library route was found, and no prior proof dependency was removed.

5. The associated-module unit route is retained: the original theorem remains the item and the two component nodes are used only to close its proof. The delivered DAG records agree with the declarations and their remaining proof dependencies.

Changed during second reading: added this review record; no Lean declarations or DAG nodes required repair.
