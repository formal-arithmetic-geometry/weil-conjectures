## Worker report

Repair of returned immutable head `7c47c71b54d7`, group Q15, stage 2.
The returned point was that `def-sfb-strict-birational-law` had already been created on
sheaf-dag by another delivery. The retained sandbox was compared with the current node
records and their full source modules. Removed the duplicate definition-node JSON and
its duplicate StrictBirationalLaw.lean from this packet. The item now imports the landed
`Sheaf.AlgebraicGeometry.StrictBirationalLaw` and uses
`AlgebraicGeometry.RelativeBirational.StrictLaw`, with the relative-map API from
`Sheaf.AlgebraicGeometry.RelativeBirationalMaps`. No published definition is changed.
Both existing definition nodes are added to the item's stmt_deps. There are no new nodes
or dependency repairs in this delivery. The original natural-language statement and all
proof steps and dependencies are unchanged.

The item module is `Sheaf.AlgebraicGeometry.StrictLawCompleteSquareGroup`; its declaration is
`AlgebraicGeometry.RelativeBirational.StrictLaw.existsUnique_group_of_complete_square`.
It contains exactly one theorem, with `sorry` as its proof, and no definitions.

Every hypothesis and clause is rendered as follows:

- `A : Type u`, `[CommRing A]`, `[IsNoetherianRing A]` give the Noetherian commutative ring.
  `[IsStrictlyHenselianLocalRing A]` gives the henselian local ring and separably closed
  residue field using the existing upstream class. Normality is `hA`, exactly the normal
  ring dependency's inline form: for every prime p, both `IsDomain (Localization.AtPrime p)`
  and `IsIntegrallyClosed (Localization.AtPrime p)`.
- `Z : Over (Spec (CommRingCat.of A))` fixes S=Spec A and the structure morphism Z.hom.
  `[Smooth Z.hom]`, `[IsSeparated Z.hom]`, `[LocallyOfFiniteType Z.hom]` and
  `[QuasiCompact Z.hom]` are smoothness, the closed-immersion diagonal, and finite type.
  `hfibres` says every scheme-theoretic fibre is nonempty.
- `RelativeBirational.FibrewiseDense p U` is density of the inverse image of U under
  `p.fiberι s` for every s. It is the published meaning of S-dense, not just total density.
- `n : RelativeBirational.StrictLaw Z` is the existing strict-law representative.
  `n.mul : RelativeBirational.PartialMap (RelativeBirational.square Z) Z` includes an
  S-dense open domain D, the multiplication morphism D→Z, and its equation over S.
  Its `associative` field is the existing `Associative` predicate: an S-dense open of Z³
  carries both iterated products and equality of their morphisms, exactly rational
  associativity. The six projection-density fields give density of D,V,W in every fibre
  of both projections. `leftIso`, `rightIso` and their four coordinate equations are
  precisely the specified charts (x,y)↦(x,n(x,y)) and (x,y)↦(n(x,y),y).
- `hsection : Nonempty (Over.mk (𝟙 S) ⟶ Z)` is Z(S)≠∅, a section over S.
  `U : Z.left.Opens` and `hU : RelativeBirational.FibrewiseDense Z.hom U` give U.
- `square` is a relative partial map on `RelativeBirational.square Z`; `hsquare` identifies
  its domain exactly with the intersection of inverse images of U under the two
  projections, i.e. all of U×_S U. Its S-morphism condition and fibrewise density are fields
  of this published PartialMap, so no separate hover hypothesis is needed. `hn` is
  `n.mul.Agrees square`, namely agreement on a common S-dense open. It does not require
  U² to lie in the arbitrarily chosen strictness domain D.
- `∃! G : GrpObj Z, ...` gives the unique group-object structure on the fixed S-scheme.
  `MonObj.mul`, `GrpObj.inv`, and `MonObj.one` are the requested μ, ι and e.
  The five axioms `mul_assoc`, `one_mul`, `mul_one`, `left_inv`, `right_inv` are precisely
  the associativity, unit and inverse diagrams in Over S. This is the dependency's
  existing general group-object notion, applied over S rather than restricted to a field.
- The conclusion's predicate says there is an open H of Z², fibrewise dense over S,
  with H≤n.mul.domain, where the restriction of n.mul.hom equals H.ι followed by μ.
  This is exactly common-open agreement with the everywhere-defined multiplication,
  spelling out published PartialMap.Agrees to avoid constructing an extra partial map.
  Uniqueness is equality of the complete GrpObj structure, including all three arrows.

`RelativeBirational.square Z` uses the second projection for its structure map while
Mathlib's tensor product in Over S uses the first. Their underlying schemes are both the
same chosen `pullback Z.hom Z.hom`. The pullback condition equates the two structure maps;
our equations compare only morphisms on that same underlying scheme. No transport, extra
hypothesis, chosen arbitrary comparison, or duplicate product definition is introduced.

Recorded dependencies used (source declarations and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: Scheme, its Hom, Spec and Spec.map.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded scheme-product,
  fibre and induced-section conventions (Limits.pullback, fst, snd, Scheme.Hom.fiber).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: Smooth.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: LocallyOfFiniteType; QuasiCompact
  is supplied by its imports and gives the other finite-type condition.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: IsClosedImmersion, via the
  IsSeparated diagonal definition in Morphisms.Separated.
- `Mathlib.CategoryTheory.Monoidal.Grp`: GrpObj and MonObj.
- `Mathlib.RingTheory.Noetherian.Defs`: IsNoetherianRing.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: IsIntegrallyClosed, with
  IsDomain and Localization.AtPrime as specified by the normal-ring node.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: IsStrictlyHenselianLocalRing.
- `Sheaf.AlgebraicGeometry.RelativeBirationalMaps`: FibrewiseDense, PartialMap,
  PartialMap.Agrees, the existing relative-map notions.
- `Sheaf.AlgebraicGeometry.StrictBirationalLaw`: square, Associative, StrictLaw.

The proof dependency `Sheaf.AlgebraicGeometry.StrictLawTranslationEmbedding` has landed
since the returned head and is now imported non-publicly. Its full signature and docstring
were read. The other two proof dependencies (graph-charts and relative-rational-flat-
regularity) still have no recorded Lean modules; no fictitious imports are added. The
item theorem's docstring retains the entire five-step proof plan and names all three.

Edge cases: nonempty fibres and a section exclude empty Z. Empty U cannot be fibrewise
dense in these nonempty fibres. No connectedness, irreducibility, dimension, characteristic,
commutativity, field or DVR restriction is imposed. U=Z is allowed. Disconnected and
zero-dimensional group schemes are allowed. Equalities and associativity are scheme
morphism equalities, retaining nilpotents and all test schemes. The ring, base, schemes,
products and residue-field fibres use universe u without an extra size equality. Every
variable and universe is explicitly bound. No local instance, notation, hidden data,
extra regularity assumption or total-space-only equality is used.

Searches from the original delivery are retained in searches.jsonl: LeanFinder on completion
found smoothness and elliptic-curve/group-pullback results, no completion theorem; Loogle's
initial guessed RationalMap name failed and the corrected Scheme.PartialMap query found
only absolute partial maps; LeanSearch and LeanFinder on relative laws found absolute
rational-map interfaces; Mathlib grep for StrictBirational|RelativeRational|BirationalLaw|
FibrewiseDense returned no hits then. Library and DAG searches originally found no definition.
The repair now finds the landed Q131 definitions, which supersede those negative results.
The current item has no Lean record, so its completion theorem still needs stating.
No new searches or new mathematical definitions are required for this interface rebind.
The BLR source and latest blueprint were read in the original pass; no source or
natural-language statement is changed. There is no STATEMENT-DISPUTED finding.

## Second reading by Q15

A separate self-review pass re-read the current published StrictLaw and relative-map modules,
the current item node and the repaired theorem, without starting another agent (forbidden
by the dispatcher brief). This is not a claim of independent authorship; the maintainer
provides the independent review. The returned point is repaired by removing the conflicting
node and module, citing both published nodes, and changing every affected binder and
predicate to their API. Checked that associative now uses the published common-dense-open
notion and that no duplicate definition survives. The relative PartialMap already carries
its over-base equation. The conclusion still gives one and only one full group structure
extending the rational law, and its agreement predicate still uses fibrewise density.
The item node is refreshed from current main with only lean and added stmt_deps changed.
