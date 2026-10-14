## What changed
Proved `ModuleCat.exists_derivedExtension_ringEquiv_raw_counit` by decomposing the argument into two strictly simpler intermediate transport and compatibility theorems. Added imports for the two intermediate modules.

## Proved and sorry left
The target theorem is proved. The intermediate declarations `ModuleCat.exists_raw_transport` and `ModuleCat.raw_compatibility` remain `sorry`, each with its own DAG node.

## No longer needed
No planned proof dependencies were removed; the base model import remains required for all signatures.

## Where the brief, the DAG or earlier work was wrong
The original node bundled localization transport and the counit calculation into one theorem. Splitting these strictly separate steps was required to express the proof in Lean within the available interfaces.

## New nodes
`lem-pc-derived-extension-ring-equiv-raw-transport` and `lem-pc-derived-extension-ring-equiv-raw-compatibility` are new intermediate theorem nodes, with modules under `lean/Sheaf/Algebra/Homology/`.

## Earlier second reading (a previous round; superseded)
A second worker should check that the decomposition preserves the original target statement and that both intermediate statements are strictly simpler and true.

## Second reading by E1

1. Compared the delivered target module with the repository version. The target signature is byte for byte unchanged; only proof imports and proof text changed. The two added modules contain new intermediate declarations with explicit signatures.
2. Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds with no warnings. The target proof has no `sorry`; the two named intermediate declarations retain their documented `sorry`s and no definition contains `sorry`.
3. Reviewed the decomposition. The original compatibility statement quantified over an arbitrary `a`, which was too strong: composing a valid `a` with a nontrivial automorphism need not preserve the counit equation. I changed it to assert existence of a compatible `a`. I also removed the unused `a` and `True` from the transport statement. These are strictly simpler, true reductions and the target now obtains `E,q` first and then a compatible `a`.
4. The proof uses the two intermediate declarations and the node proof dependencies are updated accordingly. No imports were removable; the base model remains needed for all signatures. The unit route remains through the raw transport and compatibility steps.
5. The DAG Lean statements now match the declarations, and the target node records both intermediate proof dependencies. No target or existing declaration signature was changed.

Changed: corrected `raw_compatibility` to existential compatibility, simplified `exists_raw_transport`, updated their node statements and the target proof metadata, and shortened a long line.

