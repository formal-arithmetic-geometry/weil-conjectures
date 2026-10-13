## What changed

The original signature of `AlgebraicGeometry.Etale.isIso_rawModuleAbelianHomMap` is
unchanged. Its proof combines independent injectivity and surjectivity statements
and applies `ConcreteCategory.isIso_iff_bijective`. Both new imports are proof-only.
The existing DAG node now records these two actual proof dependencies.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Etale.isIso_rawModuleAbelianHomMap`.
Added two holes:
- `AlgebraicGeometry.Etale.rawModuleAbelianHomMap_injective`, node
  `lem-sbc-raw-module-abelian-hom-map-injective` (class detection by boundaries).
- `AlgebraicGeometry.Etale.rawModuleAbelianHomMap_surjective`, node
  `lem-sbc-raw-module-abelian-hom-map-surjective` (class lifting by cocycles).

This is a decomposition, not a completed cohomology comparison: one hole closed,
two added, net minus one. Each lower statement has only one of the two required
properties, and its proof describes the corresponding direction of the resolution
argument. All three files compile with lcompile.py --all.

## No longer needed

No original import or dependency is pruned. The original acyclicity node remains
needed through both new nodes. The statement import RawModuleAbelianHomMap stays.
The attempted general Ext dimension-shifting helper and its derived transport were
removed from the sandbox delivery; they are not new library dependencies.
No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The single prose step conceals the substantial normalization of the explicit map
on the common section complex. The original acyclicity declaration also uses
SheafOfModules over a lifted Type-u ring, whereas the raw comparison permits
ModuleCat coefficients in Type-(u+1); a direct application needs the existing
constant-ring equivalence and the larger-universe acyclicity argument as in
ModuleAbelianDerivedDirectImageComparison. No interfaces were changed.

An initial bijectivity-only helper would have been a repackaging of the original
hole, so it was removed. Only the two distinct directions remain. The independent
reader should particularly check normalization of the canonical pullbackIso/freeMap
in each lower proof, and whether this decomposition is sufficiently substantive.

## New nodes

`lem-sbc-raw-module-abelian-hom-map-injective` records detection of zero classes by
lifting boundaries in the common section complex. Its module is
Sheaf.AlgebraicGeometry.RawModuleAbelianHomMapInjective.

`lem-sbc-raw-module-abelian-hom-map-surjective` records lifting an abelian class via
a section cocycle in the forgotten injective module resolution. Its module is
Sheaf.AlgebraicGeometry.RawModuleAbelianHomMapSurjective.

No change records are needed: all existing signatures and visibility are unchanged.

## Second reading by W3

1. The delivered module preserves the original theorem signature byte for byte and its proof compiles. Verdict: pass.
2. The two added statements are the injective and surjective halves of the original bijectivity claim; each is strictly weaker, true by the cited Tag 03FD acyclic-resolution argument, and carries a source and complete proof sketch. Verdict: pass.
3. The proof uses `ConcreteCategory.isIso_iff_bijective` and the two component statements, with proof-only imports. No shorter existing declaration was found in the library or Mathlib searches. Verdict: pass.
4. The existing unit route is retained: the comparison remains the realized isomorphism node, while the split lower nodes expose the two substantive class arguments. Verdict: pass.
5. The DAG proof and `proof_deps` agree with the Lean proof; new node metadata, Lean declarations, and report entries agree. Verdict: pass.

Changed only the report by recording this independent second reading. No Lean repair was necessary.
