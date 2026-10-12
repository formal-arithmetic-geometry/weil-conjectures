## What changed
Added a proof-only import of `PerfectComplexClassesSmallGluingCore` and proved the
public gluing theorem by introducing the quantified open immersion and applying the
core fixed-immersion result. Added the core theorem as a separately stated
intermediate result.

## Proved and sorry left
The wrapper theorem `perfectComplex_classesSmallOnOpen_union` is proved. The new
intermediate theorem `perfectComplex_classesSmallOnOpen_union_core` remains `sorry`;
it captures the Mayer--Vietoris, skeleton, and K-injective smallness argument.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The full Mayer--Vietoris argument is too large for the wrapper, so it was split into
a fixed-open intermediate theorem while preserving the exact target statement.

## New nodes
`new-perfect-classes-small-gluing-core`: fixed-open core smallness theorem in
`lean/Sheaf/AlgebraicGeometry/PerfectComplexClassesSmallGluingCore.lean`.

## Earlier second reading (a previous round; superseded)
The wrapper preserves the target statement exactly; the new core theorem is a strict intermediate reduction and retains the unit route through Mayer--Vietoris.

## Second reading by C3
1. Compared the delivered wrapper with the repository version. The theorem signature is byte-for-byte unchanged; only its proof and the proof-only core import changed. Verdict: pass.
2. Compiled all three sandbox modules with `lcompile.py --all`. They compile without errors. The wrapper has no `sorry`; the only remaining hole is the named core theorem, and it is recorded by node `new-perfect-classes-small-gluing-core`. No forbidden declarations or hollow definitions were added. Verdict: pass.
3. Checked the split statement. The core fixes an arbitrary open immersion and concludes exactly the skeleton smallness needed by the wrapper, so it is a strict reduction rather than a restatement. Its docstring gives the Mayer--Vietoris, K-injective, and uniqueness argument, and its node records the source and proof route. Verdict: pass.
4. Checked the proof route and pruning. The wrapper introduces the quantified immersion and delegates to the fixed-immersion core; the Mayer--Vietoris route required by the unit is retained. No old import is unused in the delivered wrapper, and no prior proof dependency was removed. Verdict: pass.
5. Checked the DAG records against the Lean declarations. The item node points to the wrapper proof and the new core node; the core node points to the core declaration and records its split status. The unit route remains through the gluing step. Verdict: pass.

Changed only the report during this second reading; no Lean statement or proof was altered.
