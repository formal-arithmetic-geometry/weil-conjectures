## What changed

Reduced `AlgebraicGeometry.ProEtale.sncFiniteFibreClassification_scalarReduction` to two
strictly smaller finite-coefficient statements. Its signature and the other two public
signatures are unchanged. The classifier-existence and pointed-refinement bodies remain
open; this is a partial module delivery.

The item proves the module-valued sheafification/stalk comparison directly using the
geometric point and Mathlib's point/skyscraper interface, for arbitrary unital rings.
It combines this with preservation of colimits by the supplied coefficient left adjoint
to construct the canonical isomorphism and prove its equation on every neighbourhood
coprojection. It then constructs the scalar-unit sheaf map, proves its stalk formula,
applies normalized semilinear naturality, and uses the adjunction hom-equivalence to
prove equivariance of the comparison. The remaining lemmas do not assume that comparison.
No data are chosen in a definition from an unproved existence theorem.

Validation: lcompile.py compiled the two new modules in 40.6 and 41.4 seconds,
and the final item in 7.3 seconds, all within the 60-second per-file limit. The
final delivery performs the independent mechanical compile and axiom probe. The three
kinds of Mathlib search are in searches.jsonl. LeanSearch found only generic module and
sheaf operations; Loogle and grep found no exact match. The existing normalized finite
splitting operations were read before adding the two interface-specific statements.
Sources read: ILO IX 2.1, printed pp.133-134 (including its lattice/root quotient
presentation), Bhatt-Scholze 5.1.4-5.1.5 and 7.4.3, and the current blueprint's
ctf-stability direct-image proof, paragraph (3). No unit or chapter route changes.

## Proved and sorry left

One of the item's three original hole bodies is replaced by a complete assembling
proof: `AlgebraicGeometry.ProEtale.sncFiniteFibreClassification_scalarReduction`.
Two new holes are added. This is a decomposition, not a completed proof of scalar
reduction: net textual holes in this packet go from three to four.

The four remaining holes, with their nodes, are:

- `AlgebraicGeometry.ProEtale.nonempty_sncFiniteFibreClassification`:
  `lem-sfb-snc-tame-finite-fibre-classification` (original, unchanged).
- `AlgebraicGeometry.ProEtale.sncFiniteFibreClassification_refinement`:
  `lem-sfb-snc-tame-finite-fibre-classification` (original, unchanged).
- `AlgebraicGeometry.ProEtale.sncFiniteTame_scalarExtension`:
  `lem-sfb-snc-finite-tame-scalar-extension` (new).
- `AlgebraicGeometry.ProEtale.sncFiniteModuleStalkAction_natural`:
  `lem-sfb-snc-finite-module-stalk-naturality` (new).

The scalar-closure lemma asserts only membership in the original-chart essential
image. It supplies no stalk comparison or actions. The naturality lemma applies to any
two tame module sheaves and any semilinear sheaf map with its germ map; it assumes no
scalar-extension functor, comparison isomorphism, finite coefficient rings or geometric
finite-type hypotheses. The actual comparison and the adjunction argument combining
them are proved in the item. Both holes have self-contained source/proof docstrings
and separate modules/nodes. Empty parameters, the zero ring and the zero module were
checked in the natural-language arguments; a module has one zero element, so its
underlying fibre is never empty.

## No longer needed

No mathematical node or module is withdrawn. In particular the original proof plans
and dependencies of the two unfilled assertions are retained. The following private
proof imports have no use in the delivered assembling proof and are removed from the
item (their possible use by future proofs or other consumers is not withdrawn):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`
- `WeilConjectures.Mathlib.RingTheory.Henselian`
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`
- `Sheaf.FieldTheory.TameRootsProduct`
- `Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech`
- `Sheaf.AlgebraicGeometry.SNCTameRootEtaleExtension`
- `Sheaf.AlgebraicGeometry.SNCUniversalResidualCharts`
- `WeilConjectures.AlgebraicGeometry.NilpotentBaseChangeIdempotents`
- `WeilConjectures.AlgebraicGeometry.DescendFinite`
- `WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent`
- `WeilConjectures.RingTheory.IntegralOverHenselianPair`
- `Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover`
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence`
- `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale`

The public imports are unchanged. The new proof imports are the two split modules,
Mathlib's point constructor and skyscraper adjunction, colimit preservation by
adjoints, and the existing weakly-etale geometric-point section lemma. No existing
shared definition or interface is changed and no consumer adaptation is needed.

## Where the brief, the DAG or earlier work was wrong

The operations node concerns the full category of sheaves that become finite constant
on the tower. `Q.finiteTame` instead asks for an original-chart finite tame model.
Consequently its scalar-closure conclusion cannot be obtained by treating these
predicates as definitionally equal. The new closure lemma records the missing return
to the original chart: finite inertia orbits are Gamma_n/K, and K is stable under
cyclotomic scalar units, so the root-torsor quotient descends over B. The quotient
presentation is the one on ILO p.133. This is an interface gap, not a changed statement
or a claimed counterexample. The semilinear stalk lemma records the other missing
specialization, from the classifier's actual finite labels to linear module stalks.

A dependency audit found an existing distant cycle through `lem-sp-grothendieck-edge-maps`,
already reachable from the original parent; this delivery does not change those nodes.
Neither new lemma depends back on the parent classification node.

The inherited blueprint ancestor is null; blueprint_refs.py ancestor confirms this.
The new nodes preserve that null ancestor and inherit the precise parent creation
chain. Searches for normalized finite splittings and semilinear statements in the
whole blueprint found no duplicate of either new assertion. No second agent was
started, as required by the dispatcher brief.

## New nodes

`lem-sfb-snc-finite-tame-scalar-extension`, module
`Sheaf.AlgebraicGeometry.SNCFiniteTameScalarExtension`, isolates the geometric closure
step of scalar reduction. Its proof records finite root models, residual splitting,
finite normalized inertia descent, finiteness after scalar extension, the invariant
stabilizer quotient over the original chart, and comparison by effective descent.

`lem-sfb-snc-finite-module-stalk-naturality`, module
`Sheaf.AlgebraicGeometry.SNCFiniteModuleStalkNaturality`, isolates linearity and
semilinear naturality of normalized monodromy on actual module stalks. Its proof uses
the label/stalk bijection, the existing finite-operation argument, and the naturality
of the underlying finite-set fibre map. It is independent of scalar extension.

The parent node gains the scalar-reduction assembly step and its two dependencies;
its other proof steps remain. No change records are needed: existing public
signatures, definitions, instances and public imports are unchanged.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
