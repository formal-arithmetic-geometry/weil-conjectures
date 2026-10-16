## What changed

Replaced the first worker's degree-one/successor induction with the source's actual reduction:
`AffineComparisonInjectiveVanishingAux.lean` takes a cocycle, descends it to an étale covering,
applies the existing `CategoryTheory.injective_sheaf_cech_acyclic`, obtains a primitive, and
maps that primitive back using the chain-map identity. The original theorem's entire signature
and its four public imports are byte-for-byte unchanged. No existing definition changed and no
change record or forced adaptation is needed.

Added `Sheaf.AlgebraicGeometry.AffineComparisonCechCocycleDescent` with the remaining geometric
obligation, `AlgebraicGeometry.ProEtale.exists_etale_cech_cocycle_lift`. It applies to arbitrary
abelian étale sheaves and asserts descent of a cocycle and a map of complexes, without asserting
any exactness or existence of a primitive. Its source is Tag 099U condition (3), before the final
application of injectivity. The proof-only dependency imports retain the geometry needed for the
unfinished descent, including section continuity, finite étale descent and fibre-product limits.

Removed the unlanded H1 and Shift modules and their two unlanded nodes from this sandbox.

## Proved and sorry left

Closed the original local hole in
`AlgebraicGeometry.ProEtale.exactAt_cechComplex_comparisonUpperStar_of_injective`
(node `lem-cbc-abelian-affine-comparison-vanishing-aux`).

Added one hole:
`AlgebraicGeometry.ProEtale.exists_etale_cech_cocycle_lift`
(node `lem-cbc-affine-comparison-cech-cocycle-descent`). Its proof is exactly `by sorry` and its
docstring contains its source and the full two-stage finite-cocycle descent argument.

This is a **decomposition**, not a completed proof of the import closure: one original hole
closed and one new hole added, net zero. The first worker had added two holes while closing one;
the second reading removed both of those and replaced them with the single geometric obligation.
The rejected declarations were
`AlgebraicGeometry.ProEtale.exactAt_cechComplex_comparisonUpperStar_of_injective_h1` and
`AlgebraicGeometry.ProEtale.exactAt_cechComplex_comparisonUpperStar_of_injective_succ`.
No hole is added inside a definition, no data definition is added, and no axiom is introduced.
The ledger, after landing, determines any actual closure/import-pruning figures.

## No longer needed

Every old direct `proof_deps` entry is accounted for here. A retained dependency below the new
geometric lemma is not claimed as a globally pruned module.

| Old dependency | Disposition |
|---|---|
| `lem-cbc-comparison-pullback-sections` | retained in the geometric descent plan |
| `def-weil-pbc-site-comparison-morphism` | retained in the geometric descent plan |
| `def-weil-pbc-sites-and-cohomology` | retained in the geometric descent plan |
| `lem-weil-pbc-etale-cohomology-limit-of-schemes` | retained in the geometric descent plan |
| `lem-weil-pbc-affine-scheme-qcqs` | retained in the geometric descent plan |
| `lem-weil-pbc-filtered-colimit-abelian-groups-exact` | not used: finite representatives and eventual zero replace the homology-colimit theorem |
| `def-weil-pbc-site-cech-complex` | retained in the geometric descent plan |
| `def-weil-pbc-ind-etale-basis` | retained in the geometric descent plan |
| `lem-weil-pbc-ind-etale-stability` | retained in the geometric descent plan |
| `def-weil-pbc-ind-etale-algebra` | retained in the geometric descent plan |
| `lem-weil-pbc-filtered-category-directed-cofinal` | retained in the geometric descent plan |
| `lem-kun-fibre-product-limits` | retained in the geometric descent plan |
| `lem-weil-pbc-limit-affine-transition` | retained in the geometric descent plan |
| `lem-weil-pbc-affine-etale-site-colimit` | retained in the geometric descent plan |
| `def-weil-pbc-etale-site` | retained in the geometric descent plan |
| `lem-weil-pbc-etale-composition-cancellation` | retained in the geometric descent plan |
| `lem-weil-pbc-etale-base-change-finite-limits` | retained in the geometric descent plan |
| `lem-weil-pbc-etale-base-change-continuous` | retained in the geometric descent plan |
| `lem-weil-pbc-injective-sheaf-cech-acyclic` | retained and applied directly in the target proof |

The target removes these old direct proof-only imports:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes`
- `Sheaf.RingTheory.IndEtaleStability`
- `Sheaf.CategoryTheory.ExistsDirectedReindexing`
- `Sheaf.AlgebraicGeometry.FibreProductLimit`
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`
- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement`
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.RingTheory.IndPrincipalZariski`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`
- `WeilConjectures.CategoryTheory.SiteCechComplex`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The geometric ones remain reachable through the descent module and its imports.
`Sheaf.CategoryTheory.InjectiveSheafCechAcyclic` remains a direct proof import because the target
actually applies its declaration. No whole-library module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's new nodes had empty statement/proof dependency lists while their proofs in
words hid essentially the entire Tag 099U argument. The claimed dimension shift did not perform
a dimension shift: its docstring repeated the same filtered-colimit descent as degree one, and
its module comment suggested a cokernel argument without providing the required changed
coefficient sheaf or sectionwise exact sequence. Neither splitting into degrees nor compiling
that induction supplied the missing geometric reduction.

The repair follows Tag 099U's two reductions explicitly in the remaining geometric node, and
uses the already proved, recorded injective étale Čech theorem for the final algebraic step.
`EtaleLimitFiniteCechComplexColimit` was also inspected: it handles a covering on a specified
scheme inverse system with a compatible coefficient system, but does not directly supply this
comparison cocycle lift for a family of affine ind-étale objects. The first geometric reduction
and the comparison/categorical-product bridge still require formalization.

## New nodes

`lem-cbc-affine-comparison-cech-cocycle-descent` is the geometric part of Tag 099U condition (3).
It differs from the original auxiliary exactness node and the affine cohomology-vanishing nodes
with the same tag: coefficients are arbitrary, and the conclusion supplies a cocycle at an
étale stage and a morphism of complexes, with no vanishing or primitive assertion. It separates
the finite descent/continuity work from the independently proved injective-sheaf argument.
LeanFinder returned scheme-section and finite-type map descent lemmas; Loogle returned only
injective-resolution ExactAt lemmas; source grep found no comparison cocycle descent theorem.
LeanSearch returned Internal Server Error and is recorded as unavailable. Queries and results
are recorded by msearch.py in searches.jsonl and copied into the node. Local searches also
covered lean/Sheaf, lean/WeilConjectures and the existing DAG. There is no new change record.

## Second reading by D3

1. **Interfaces.** Compared the original module with the sandbox using diff and checked the
   original theorem header byte-for-byte. The affine base, original-site injectivity, affine
   ind-étale target, finite family, every nonempty repeated intersection, covering sieve and
   positive degree are unchanged. The public imports and declaration visibility are unchanged.
   Only the target's proof-only imports and proof changed; the second delivered module is new.
2. **Proof.** Read the original induction and rejected its unsupported dimension-shift story.
   The repaired proof applies the cocycle-descent result to the actual cocycle, applies
   `injective_sheaf_cech_acyclic` to J on Y_et and the actual returned covering, converts its
   vanishing homology to a primitive, and evaluates `φ.comm` to map that primitive back.
   The only new direct sorry is the named descent theorem. Both modules compile locally;
   axiom checks permit only propext, Classical.choice, Quot.sound and sorryAx from open inputs.
3. **New statement.** Read Tag 099U condition (3), the two finite Čech limit reductions, together
   with 01ZM, 01ZN and 07RP for finite étale descent. The descent theorem requires no
   injectivity and asserts neither exactness nor a primitive, so it is a proper geometric part
   of the argument, not a renaming of the original theorem. Checked n=0 (choose the empty
   étale object and its empty covering; every group is zero), n=1 (ordinary repeated products),
   empty Y or V, the zero sheaf, q=0 and repeated indices. ULift(Fin n) changes only the
   universe of the finite index, so the existing categorical Čech theorem applies. Finite
   products, finite common stages and eventual-zero arguments use precisely the finiteness
   and affine hypotheses stated. The theorem's witness is obtained inside a proof, and no
   arbitrary existence witness is installed as a data definition.
4. **Route and pruning.** Used the existing injective-sheaf theorem instead of introducing
   degree lemmas. Read dag/units/sk-prop-sf-comparison.json: its realized statement/step arrays
   are empty, and this repair stays inside the same affine comparison node and retains the
   two finite-limit reductions. Every old proof dependency is accounted for above. Removed
   imports are proof-only and geometry still needed by the open lemma remains in its plan.
5. **DAG.** The original node now records descent, injective étale Čech acyclicity, then the
   evaluated chain-map equation. Its proof_deps is exactly those two nodes. The new node has
   the full geometric proof, the union of its cited dependencies, source, actual search
   records, provenance, blueprint origin, matching universe-sized Lean signature and the
   original chapter/unit. No existing node statement or other owned field was changed.

Changes made by this reader: removed the two unsupported degree lemmas and their nodes;
replaced the induction by the actual cocycle-to-primitive reduction; introduced one explicit
geometric descent obligation; restored the used injective-sheaf proof import; repaired the
DAG, search records, pruning accounting and the misleading proof/closure count in this report.
