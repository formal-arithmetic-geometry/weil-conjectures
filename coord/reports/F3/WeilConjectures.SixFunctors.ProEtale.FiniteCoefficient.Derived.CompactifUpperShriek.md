## What changed

Withdrew the legacy declarations from
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifUpperShriek`.
The path remains an empty importable module so existing import indexes continue to compile.

Change record: `coord/changes/proetale-compactif-upper-shriek-withdrawal.md`.

## Proved and sorry left

No theorem remains. The removed proper-pushforward left-adjoint assertion is marked
`STATEMENT-DISPUTED` because proper pro-etale pushforward need not preserve coproducts.

## No longer needed

The legacy compactification upper-shriek definitions and their Brown-representability route.

## Where the brief, the DAG or earlier work was wrong

The blueprint assumes a proper pro-etale derived pushforward is a left adjoint. The ambient
abelian-variety counterexample in `WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts`
shows this is false. The earlier withdrawal via `deleted.txt` also attempted to edit the aggregate
index; retaining an empty module avoids changing that index.

## Earlier second reading (a previous round; superseded)

Pending independent reader.

## New nodes

None.

## Second reading by F3

1. I compared the delivered module with the repository version. The delivery intentionally
   removes the legacy declarations and records that interface change in
   `coord/changes/proetale-compactif-upper-shriek-withdrawal.md`; the remaining module is
   byte-for-byte independent of those declarations and retains its import path.

2. I compiled the module with `lcompile.py`; it has no errors, `sorry`, axioms, unsafe
   declarations, or hollow definitions. The empty module also compiles when imported by the
   active `Derived.UpperShriek` module.

3. No statement was split off and no new node was added. The removed proper-pushforward
   left-adjoint assertion is explicitly marked `STATEMENT-DISPUTED` in the module and change
   record; the ambient abelian-variety counterexample is the stated reason.

4. The active route is preserved through `Derived.UpperShriek`; the withdrawn legacy route is
   no longer reachable. The two former public imports were removed because the delivered
   module has no declarations needing them.

5. The change record documents the altered interface and its downstream users. The module
   retains a valid importable path, and the delivery introduces no DAG node or proof
   dependency requiring synchronization.

Changed the module by removing its obsolete declarations and unused imports, and retained the
withdrawal change record. No theorem holes remain in the delivered module.
