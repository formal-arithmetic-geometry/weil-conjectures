## What changed

Proved `CategoryTheory.openOver_internalHom_cycle_homology_squares` directly, with its
signature and existing declarations unchanged. Added proof-only imports of
`Sheaf.Paper.DerivedHomMayerVietoris` and
`WeilConjectures.Mathlib.Algebra.Homology.SingleHomology`.

The proof establishes finite-limit and finite-colimit preservation of the composite
restriction, uses the inverse `ShortComplex.mapCyclesIso` and `mapHomologyIso`
comparisons, and proves their inclusion and quotient compatibility. It constructs all
four internal-Hom isomorphisms explicitly using `homObjMap`, proves their inverse laws,
and derives the four squares from the supplied naturality equation. This follows the
existing node's two-step plan and preserves the unit route. A local composition lemma
specializes the existing internal-Hom API to avoid repeated inference of the open site.

## Proved and sorry left

Closed one original hole:
`CategoryTheory.openOver_internalHom_cycle_homology_squares`
(node `new-t4-open-over-internal-hom-cycle-homology-squares`).
No holes added; no `sorry` remains in the delivered module. This is a proof, not a
decomposition. The delivery adds no definitions or statements.

## No longer needed

No original import was removed; no existing DAG node or library module is pruned.
The unlanded sandbox helper modules `OpenOverInternalHomCycleHomologyComparisons`
and `OpenOverInternalHomCycleHomologyNaturality` and their proposed nodes were discarded.
Neither is needed by the direct proof, and neither is included in this delivery.

## Where the brief, the DAG or earlier work was wrong

The retained earlier sandbox attempt's naturality theorem quantified over arbitrary
comparison isomorphisms without any compatibility hypotheses. That statement is false:
independently changing one comparison by a nontrivial scalar automorphism changes a
side of a square. Merely knowing the four objects are isomorphic does not supply the
four equations. The earlier second-reading claim that these were true strict
intermediates was therefore incorrect and has been removed. The replacement proof
uses the canonical exact-functor comparisons and proves their compatibility.

The existing node's plan is usable without modification. Searches found the needed
exact-functor API and the existing `homologyπ_mapHomologyIso_hom` compatibility lemma;
no new intermediate statement is necessary.

## Second reading by J3

1. Compared the delivered module against the repository version. The theorem signature and all existing declarations are unchanged; only two proof-only imports, a scoped heartbeat option, and the proof body differ.

2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The proof uses only the exact-functor comparison API and the supplied naturality hypothesis; no new declarations were added.

3. Checked the split-off node and searches. No new statements or nodes are delivered, so there are no additional truth or strength concerns and no duplicate Mathlib/upstream declaration.

4. Reviewed the proof route and imports. The direct proof follows the existing node plan through exact restriction, cycle/homology comparison isomorphisms, and internal-Hom naturality. The two added imports are used by the proof; no old import or proof dependency is removable.

5. Checked DAG agreement and the unit route. The node's declaration, proof description, and dependencies match the Lean proof, and the unit's realized route is retained.

Changed during second reading: repaired the heartbeat option placement so it is scoped to the theorem and does not produce a linter warning; retained the explanatory proof comment as a regular comment immediately before the scoped declaration.
