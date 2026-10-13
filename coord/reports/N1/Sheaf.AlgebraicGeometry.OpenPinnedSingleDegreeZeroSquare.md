## What changed

Replaced the original degree-zero square hole with a source isomorphism constructed
from existing pinned pullback composition, exact open-pullback, explicit direct-image
restriction, and Mathlib's `mapDerivedCategorySingleFunctor`. Proved the target assembly
by restricting the cartesian square with `Scheme.Hom.isPullback_resLE`, applying the
existing bare base-change calculation, moving the final tensor counit through the
natural direct-image comparison, applying the explicit coefficient/counit square,
using proved base-change naturality, and transporting the restricted apex to the
chosen pullback. The original theorem pairs these source and target isomorphisms.

Added four modules: OpenPinnedSingleDegreeZeroSource (constructed data and proved
component formula), OpenPinnedSingleDegreeZeroCounit (one residual counit square),
OpenPinnedSingleDegreeZeroApex (one residual isomorphic-apex transport), and
OpenPinnedSingleDegreeZeroTarget (proved assembly and a proved private naturality helper).
No existing signatures, definitions, public imports or visibility changed.
The second reader removed the redundant direct source import from the original module
and replaced the new target module's BaseChangeConventions import with the narrower
Mathlib.AlgebraicGeometry.Pullbacks import required by its statement.

## Proved and sorry left

Closed `AlgebraicGeometry.open_pinned_single_degree_zero_square` (one original hole).
The delivery is a decomposition, not a closed axiom-free proof: two strictly smaller
holes are added. The existing imported bare-mate calculation remains a downstream item.

The only delivery-added sorries are:

- `AlgebraicGeometry.open_pinned_single_degree_zero_counit_square`, node
  `lem-pc-open-pinned-single-degree-zero-counit`: the pinned tensor counit under
  open restriction, without any base-change map or direct image.
- `AlgebraicGeometry.open_pinned_single_degree_zero_apex`, node
  `lem-pc-open-pinned-single-degree-zero-apex`: changing the apex of a commutative
  square by an isomorphism, without any open-restriction geometry.

The source construction, its component formula, the target assembly, and its
private base-change naturality and categorical composition helpers have complete
Lean proofs. There is no sorry in any definition or private helper. No arbitrary witness is used to define data:
source data are explicitly constructed, and the two residual existence results
are only eliminated inside theorem proofs.

## No longer needed

Removed these five direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`;
- `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`;
- `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`;
- `Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`;
- `Sheaf.AlgebraicGeometry.ModuleBaseChangeSquareRestrictionCommutes`.

The replacement construction still uses pinned composition and open restriction
exactness through the existing constructed comparison modules; those mathematical
ingredients are retained. The nonempty direct-image and universe-transport lemmas
are replaced by explicit same-universe comparison data. The original node's direct
proof edges to `lem-pc-restrict-derived-direct-image-open`,
`lem-pc-derived-pullback-open-restriction-universes`,
`lem-weil-pbc-module-square-restriction-commutes`, and
`lem-weil-pbc-open-immersion-module-pullback-restriction` are no longer used in this
assembly. All nine old direct proof dependencies are replaced at the original node. In addition
to the four retired edges above, the old direct edges to
`def-pc-derived-base-change-map`, `def-pc-derived-open-restriction-maps`,
`def-pc-fibre-product`, `lem-pc-ringed-spaces-derived-pullback-composition`, and
`lem-sc-derived-open-restriction-adjunction-exact` are removed from that node;
their ingredients remain used through the source/target constructions and their
dependencies. Thus these five nodes are not globally obsolete.

The second reading additionally removed the redundant original direct import
`Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroSource` (exported by Target),
and replaced `Sheaf.AlgebraicGeometry.BaseChangeConventions` in the new Target
module with `Mathlib.AlgebraicGeometry.Pullbacks`, which supplies the HasPullback
instance required in the public statement. This is local import pruning; no claim is made that other
targets cease to reach any module. The original public imports remain identical.

## Where the brief, the DAG or earlier work was wrong

The original plan's dependency statements supply existence of restriction
isomorphisms but do not state their compatibility with the pinned counit. Arbitrary
isomorphisms cannot be substituted into that compatibility equation: automorphisms
can twist one side. The delivery constructs the source and uses the existing
explicit direct-image comparison; its new counit square fixes the constructed
pullback restriction coefficient comparison and asserts existence of a compatible tensor
comparison, rather than compatibility for arbitrary choices.

The existing fixed-counit and all-degree pinned-square modules import this item,
so importing those equivalent results here would create a cycle. The existing
bare calculation can be imported without a cycle and is reused. Its existing
sorry is intentional stage-3 dependency work, not an obstacle.

The local literature checkout does not contain the cited Stacks TeX files; the
public Stacks pages 08HY, 08DW and 08IB were read. Sources for the new residual
proofs are the inherited argument and the pinned construction of
[Stacks 08HY](https://stacks.math.columbia.edu/tag/08HY), with open-pullback locality
in [Stacks 08DW](https://stacks.math.columbia.edu/tag/08DW).

## New nodes

`def-pc-open-pinned-single-degree-zero-source` records the real source construction
and its component formula; it adds no hole.

`lem-pc-open-pinned-single-degree-zero-counit` isolates the restriction identity for
the pinned tensor counit, before direct image or base change; it adds one hole.

`lem-pc-open-pinned-single-degree-zero-apex` isolates invariance under an apex
isomorphism, for arbitrary commutative squares; it adds one hole.

`lem-pc-open-pinned-single-degree-zero-target` records the proved combination of
these ingredients with the existing bare mate calculation, single restriction,
base-change naturality and pullback geometry; it adds no hole.

All four nodes are in the original chapter and unit. The unit's realized route is
unchanged. No change record or forced adaptation is needed.

## Second reading by N1

1. **Existing interface: PASS.** Compared the original module with the repository
   using `diff -u`: the theorem header, binders, conclusion, docstring, namespace,
   visibility and four public imports are byte for byte unchanged. Only proof
   imports and the proof body differ. The four other modules are new. No existing
   definition, target or consumer module changes; no change record is required.
2. **Proof and data: PASS.** Read all five modules and the upstream constructions.
   Local compilation succeeds for each. The only textual sorries are the two
   named public residual theorems listed above. No forbidden declaration or
   hollow definition occurs. The source is composed explicitly from existing
   canonical comparisons. Its selected composition is pinned by a left-derived
   lift equation; the counit is the same existing pinned counit used by the
   original statement. The residual existential witnesses are eliminated only
   in proposition proofs, never used to define public data. Axiom checks allow
   only `propext`, `Classical.choice`, `Quot.sound` and imported/residual `sorryAx`.
   A scratch module importing the five local outputs ran `#print axioms` on all
   seven public declarations: the source construction, its component formula,
   and the explicit single counit use only the three standard axioms. The two
   residual theorems, target assembly and original square also use `sorryAx`.
   The complete-file delivery probe checks private helpers as well.
3. **Residual statements: PASS.** Counit restriction fixes the coefficient map
   and allows a compatible target comparison; it does not assert compatibility
   for arbitrary twisted comparisons. Underived tensor composition and exact
   open restriction construct that comparison, and the left-derived counit
   factorization proves its identity. Empty opens and the zero module cause no
   exception. For apex transport, pullback along an isomorphism is an exact
   equivalence; tensor composition identifies the coefficient modules and its
   right adjoint identifies their direct images. Composition coherence and the
   pinned adjunction transpose identify the maps. Identity and nontrivial apex
   automorphisms both obey this argument, without cartesianness or flatness.
   Both lemmas are strictly parts of the original argument. The target assembly
   has a real proof from them and the existing bare calculation, rather than
   moving the original hole to an equivalent sorry.

   Independent searches used leanfinder for left-derived counit compatibility
   and for isomorphic-vertex mate transport, loogle for `leftDerivedUnique`,
   and grep/rg for tensor counit, apex and base-change naturality. Mathlib has
   factorization and adjunction identities, not either complete residual theorem.
   The proved `exists_derivedBaseChange_source_iso` is relevant to apex transport,
   but requires a coefficient compatibility equation and gives objectwise
   comparisons, not the natural single-module comparison required here. Closing
   that gap needs an additional counit-composition calculation, so neither hole
   was closed in a few-minute review. The Stacks sources were re-read:
   [08HY](https://stacks.math.columbia.edu/tag/08HY) supplies the mate definition;
   [08DW](https://stacks.math.columbia.edu/tag/08DW) records open locality. The
   cited [08IB](https://stacks.math.columbia.edu/tag/08IB) is contextual base-change
   material, not a license to assume Tor independence or quasi-coherence here.
4. **Route and pruning: PASS after repair.** The source factors are the existing
   explicit open pullback/direct-image comparisons and exact single restriction.
   The target uses the bare calculation, naturality and the two genuine remaining
   steps. The five removed old imports and all nine replaced direct DAG edges
   are now accounted for above. Removed the redundant direct source import and narrowed the target
   geometry import to Mathlib Pullbacks; omitting it entirely correctly fails
   synthesis of the HasPullback instance in the public statement. No claim
   of a globally unreachable module is made. The unit record is unchanged; this
   item is below the unit's realized statement/steps and does not bypass them.
5. **DAG agreement: PASS after repair.** Read all five node records against the
   Lean constructions, theorem statements and proof references. The original
   node's new two-edge route matches its proof. Added the missing base-change
   definition and pullback-composition edges used by the target's naturality
   helper; added the source signature's pinned-single dependency. Restored all
   primary Lean statement records to verbatim multiline headers and added explicit
   dependency citations to the new nodes' natural-language statements. New nodes have
   source, proof, dependency union, searches, provenance, blueprint ancestry,
   chapter/unit and Lean records. No unit or chapter record is edited.

Second-reading changes: removed a redundant import and narrowed another, completed the pruning
account and dependency metadata, restored verbatim Lean records and recorded
this review. The delivery closes one original hole and adds two residual holes:
net -1 by raw hole count before any global closure pruning; it is a decomposition,
not an axiom-free proof or a claim of positive ledger progress.

Preflight initially caught a truncated counit signature record at its internal
`let K :=`; the record was repaired to include the full unchanged theorem header.
