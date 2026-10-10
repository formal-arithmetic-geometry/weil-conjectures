# lem-weil-pbc-flat-tor-ideal-criterion

Worker split, 2026-10-10.

## Files

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-tor-ideal-criterion.json`: split the item along Stacks 00M5 into the kernel identity and the two implications.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-tor-symmetry.json`: new unsplit statement of Stacks 00M3. LeanSearch, LeanFinder, and Mathlib source grep found no Tor symmetry declaration; Mathlib's `Tor.lean` explicitly says its `Tor` and `Tor'` are not yet identified.

## Attachments

None. Searches by both node IDs and by the Tor/flatness notions in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration stating either node exactly. The source's flat-complex Tor criterion is a different assertion.

## Source and dependencies

The item statement agrees with Algebra 00M5 (flatness iff first Tor with all ideal quotients vanishes). Step 1 spells out the kernel calculation in Remark 00M6 using the existing first-variable exact sequence and the new Tor symmetry node; steps 2 and 3 use the existing flat-tensor-exact and finitely-generated-ideal flatness leaves. The new node states Algebra 00M3 with naturality in both module arguments. For the zero and unit ideals the tensor maps are respectively `0 -> C` and the identity of `C`, so the criterion behaves correctly at both edges.

## Blueprint

The item serves the flat-module injectivity input along the chain from step 4 of `lem-weil-pbc-normal-constant-generic` (09Z5). Searches over the whole imported blueprint for `flat Tor`, `Tor groups`, and `00M3`, plus the DAG search for Tor symmetry, found no exact pre-existing node for the new prerequisite.

## Open work

`lem-weil-pbc-tor-symmetry` remains unsplit, as required for a one-level split. No source or statement disagreement was found.

## Review by E1

I read Stacks Algebra 00M3 (lemma-tor-left-right), 00M5 (lemma-characterize-flat), and Remark 00M6. The unchanged item is exactly the equivalence of 00M5(1) and (4). The new 00M3 node states natural Tor symmetry over a commutative ring for every degree and two modules, matching the source hypothesis by hypothesis. It is statement-only, with no proof or proof dependencies. DAG, whole-blueprint, slopmaster2 and Mathlib searches found no exact existing node or declaration; the available Mathlib Tor file explicitly leaves the Tor/Tor' identification open.

Step 1 applies the cited first-variable Tor exact sequence to 0 -> I -> R -> R/I -> 0 with N=C. Its stated low-degree sequence includes Tor_1(R,C), which vanishes because R has the rank-one free resolution given by the cited Tor definition. Exactness identifies Tor_1(R/I,C) with the kernel of I tensor C -> C, and the new 00M3 node changes the order to Tor_1(C,R/I). Step 2 uses the cited flat-tensor-exact statement to make that kernel zero. Step 3 uses the cited finitely-generated-ideal criterion; all ideals vanishing certainly covers its finite ideals. At I=0 and I=R the maps are respectively 0 -> C and R tensor C -> C, so no extra assumption appears. The cited definition node covers flat modules as well as flat ring maps. The three steps give the proof rather than moving the equivalence into a new node, and I found no A-E defect requiring worker repair.
