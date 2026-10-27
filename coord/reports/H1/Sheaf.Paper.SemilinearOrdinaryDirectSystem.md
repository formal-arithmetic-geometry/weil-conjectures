## What changed

Updated `Sheaf.Paper.SemilinearOrdinaryDirectSystem` by decomposing the existence proof into two strictly smaller public statements: `ordinaryDirectSystem_core_exists` for the componentwise direct image core and `ordinaryDirectSystem_homData_exists` for the restricted Hom data. The original theorem now combines these two data structures by a real constructor proof. Added the corresponding DAG nodes and updated the parent node's proof dependencies.

## Proved and sorry left

The original `ordinaryDirectSystem_exists` hole is closed by assembling the two split data structures. Two strictly simpler holes remain: `ordinaryDirectSystem_core_exists` (node `lem-coef-ordinary-direct-system-core`) and `ordinaryDirectSystem_homData_exists` (node `lem-coef-ordinary-direct-system-hom-data`). No definitions contain `sorry`.

## No longer needed

None. The parent proof uses both split statements and retains the existing dependency route.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the componentwise reassembly and the compatible-family Hom restriction into one statement, although the latter depends only on an already assembled core. The route was therefore split into the two independent construction steps above; no mathematical statement was weakened.

## New nodes

`lem-coef-ordinary-direct-system-core` records the componentwise direct-image reassembly. `lem-coef-ordinary-direct-system-hom-data` records restriction of the product levelwise Hom equivalences to compatible strict-system maps.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
