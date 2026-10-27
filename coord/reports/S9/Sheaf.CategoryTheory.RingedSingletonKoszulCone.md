## What changed

Added and proved the private `doubleConeHom` and `doubleConeIso` helpers. These
identify a two-term negative complex with the mapping cone of the map between
degree-zero single complexes, including zero-degree and unsupported-degree cases.
The public theorem remains open with its original `sorry`.

## Proved and sorry left

The two private two-term cone helpers are proved. `CategoryTheory.ringedSingletonKoszulCone`
remains the one original `sorry`; no new sorry declarations were added.

## No longer needed

No proof-only imports were retained. The attempted route through the negative
Koszul duality and tensor-cone comparison was not completed.

## Where the brief, the DAG or earlier work was wrong

The DAG plan is mathematically consistent. The available declarations do not
expose enough component formulas for the arbitrary-`P` projection and successor
identities to be discharged in this session. The two-term cone comparison itself
is independently established in this file.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
