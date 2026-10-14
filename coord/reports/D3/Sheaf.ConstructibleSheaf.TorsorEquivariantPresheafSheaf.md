## What changed

No Lean declarations required changes. The assigned module is an empty compatibility
module whose public import exposes the retained theorem
`AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf` from
`Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf`. The module compiles
unchanged with `lcompile.py`.

## Proved and sorry left

Zero holes closed and zero holes added. The assigned module contains no declarations
or `sorry`s. The retained theorem was already proved in its dependency and is not
claimed as part of this delivery.

## No longer needed

No imports, nodes, or modules were removed. The sole public compatibility import is
still required to expose the historical module path.

## Where the brief, the DAG or earlier work was wrong

The dispatch brief describes a module still containing `sorry`, but the current
module is declaration-free and its implementation was already moved to
`TorsorEquivariantModuleIsSheaf` by an earlier landed repair. The queue entry is
therefore stale relative to the current library.

## Earlier second reading (a previous round; superseded)

The compatibility module remains declaration-free and compiles successfully. Its
sole public import exposes the retained theorem with the unchanged statement, and
no unit route or dependency is altered.

## Second reading by D3

1. Compared the delivered module with the repository version. The module is a
   declaration-free compatibility import; its public interface and imported theorem
   are unchanged. Verdict: pass.
2. Compiled the module with `lcompile.py`; there are no declarations or `sorry`s in
   this module, and no new statements were introduced. Verdict: pass.
3. Checked the retained theorem and its source module; no split-off statements or
   new nodes are part of this delivery. Verdict: pass.
4. The compatibility import is still required for the historical module path, and
   no proof dependency can be pruned from this module. Verdict: pass.
5. The DAG node remains realized by `TorsorEquivariantModuleIsSheaf`; the unit route
   and dependency metadata are unchanged. Verdict: pass.

Added one documentation sentence to the compatibility module; declarations,
signatures, imports, and proofs remain unchanged.
