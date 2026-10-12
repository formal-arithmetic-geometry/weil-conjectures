## What changed

Proved `AlgebraicGeometry.Scheme.pullback_finite_locally_constant` in
`Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant`, with its statement unchanged.
Four private, fully proved helpers establish the underlying-set restriction comparison,
preservation of underlying-set constancy, the pulled-back trivializing cover, and invariance
of finite local constancy under isomorphism. The main proof supplies `upperStarComp` and
transports finite stalks through `upperStarCompSheafFiberIso` and `Point.sheafFiberCompIso`.
No definition, public signature, or target changed. Updated the item's DAG proof and dependencies.

Proof imports now use `EtaleInverseImageAbelianLift` and
`WeilConjectures.ConstructibleSheaf.Pullback`, plus the existing flat-functor and
AB5-for-types modules. The source library's `overSheafEquivFunctorObjOverIso` is reused;
its abelian local-constancy theorem is not applied to a hypothesis about underlying sets.
Generic `Sheaf.isConstant_sheafPullback` handles constant values in `Type (u+1)` directly.

Read Stacks Tags [095A](https://stacks.math.columbia.edu/tag/095A),
[093R](https://stacks.math.columbia.edu/tag/093R), and
[03Q1](https://stacks.math.columbia.edu/tag/03Q1) online because this clone does not contain
the literature source files. The unit record `sk-prop-sf-cbc` has empty realized statement
and steps lists, and its route is unchanged. Search through launcher LeanFinder, Loogle,
and grep found no ready set-valued theorem; source-library search supplied the restriction
and generic constant-pullback APIs used here.

## Proved and sorry left

Proved the sole original sorry:
`AlgebraicGeometry.Scheme.pullback_finite_locally_constant`
(node `lem-weil-pbc-pullback-finite-locally-constant`).
There are no sorries in the delivered Lean file and no new theorem with sorry.
The proof uses the already recorded `etaleInverseImageAbelianLift`
(node `lem-weil-pbc-etale-inverse-image-abelian-lift`); its existing deferred proof
remains outside this delivery. This is a stage-3 proof from existing dependencies,
not a claim that the target's entire axiom closure is now closed.
The four private helpers are proved without deferred steps.

Local compilation after the final import pruning passed cleanly (approximately 2.5 seconds).
The delivery dry run checks the server compilation and the axiom preflight.

## No longer needed

Removed these original direct imports:
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`:
  replaced by its abelian lift, with set-pullback left exactness proved using existing
  instances. The ring lift and its unit/operation statements are not needed by this proof.
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf`:
  replaced by the proved generic constant-sheaf pullback comparison. Its canonical-section
  equations, existence and uniqueness modules, set inverse-image composition-unit theorem,
  representability and coproduct-base-change route are not needed here.
- `Sheaf.Paper.InverseImageStalkGerm`:
  only the source-library stalk isomorphism is needed, without the germ equation.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` and
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  redundant direct imports; the needed restriction and composition API remains available
  through `WeilConjectures.ConstructibleSheaf.Pullback`.

Pruned from this node's proof dependencies:
`lem-weil-pbc-etale-inverse-image-algebraic-structures`,
`lem-weil-pbc-sets-etale-inverse-image-constant-sheaf`, and
`lem-weil-pbc-inverse-image-stalk-germ`.
The ring-lift branch (`lem-weil-pbc-etale-inverse-image-ring-lift`, module
`Sheaf.AlgebraicGeometry.EtaleInverseImageRingLift`) is consequently unnecessary here.
The constant comparison's modules
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheafExists`,
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheafUnique`,
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`,
`Sheaf.AlgebraicGeometry.Sites.InverseImageRepresentable`, and
`Sheaf.Paper.SetsEtaleInverseImageConstantBaseChange` are unnecessary for this proof.
These are statements about this proof's needs, not assertions that other target branches
no longer use those modules. The original restriction, covering-base-change and
composition nodes remain needed.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect hypothesis was found. Two planned lemmas include
unneeded stronger clauses: the constant-set comparison includes canonical sections and
uniqueness, and the stalk lemma includes germ compatibility. The proof uses only
constancy and the stalk isomorphism. The constant-set theorem also presents constants
as ULifts of `Type u`, whereas the locally constant predicate permits values in
`Type (u+1)`; the generic constant-sheaf API avoids any unjustified shrinking assumption.

The source abelian-valued locally constant theorem alone does not accept the item's
underlying-set hypothesis. The delivered restriction and constancy helpers keep that
hypothesis unchanged. Empty schemes/covers and empty constants require no special
choices; the same cover and fiber-functor arguments apply, and no nonemptiness or
connectedness hypothesis is introduced.

The newer `EtaleInverseImageAbelianLiftHom` module was absent from the local green cache.
It was not copied or restated: the available `EtaleInverseImageAbelianLift` supplies the
same needed comparison. No tool was changed or bypassed.

## Second reading by P2

1. **Visible statements unchanged — pass.** Read the complete delivered module and its
   repository diff. The sole existing theorem signature is byte-for-byte identical,
   confirmed by a direct string comparison. No existing definition is changed, no public
   import is added or removed, and all new helpers are private proved theorems. The DAG
   diff changes only `proof`, `proof_deps`, and `proof_origin`; no change record is needed.
2. **Proof and axioms — pass as a reduction over existing open dependencies.** Local
   compilation is clean. The delivered module contains no sorry or prohibited declaration.
   A scratch copy prints axioms for all four helpers and the main theorem: the restriction
   and isomorphism-invariance helpers use only `propext`, `Classical.choice`, `Quot.sound`;
   the constant-pullback helper, local-pullback helper and main theorem additionally inherit
   `sorryAx` through the existing abelian inverse-image comparison. Thus the item's own
   sorry is discharged, but its full axiom closure is not yet closed. The repository now
   expresses the abelian comparison through its hom and operations dependencies; none of
   these existing deferred dependencies is introduced or modified by this delivery.
3. **Split statements and small cases — pass.** No statements are split off and no new
   open theorem or DAG node is introduced. Checked all private helper statements against
   the definitions: restriction is compared as set sheaves, constancy is preserved for
   values in `Type (u+1)`, and finiteness is transported in the correct direction.
   Empty schemes and empty covers require no inhabitant; the stalk argument quantifies
   over every geometric point and introduces no extra hypothesis. Independently searched
   LeanFinder for inverse images of constant set sheaves, Loogle for the generic
   constant-pullback API, launcher grep, and repository `rg` for the set-valued predicate.
   No applicable existing theorem replaces this proof. The source's abelian-valued
   locally constant theorem has different hypotheses and cannot directly be applied.
4. **Shortest route, imports and pruning — pass.** The proof uses the existing
   restriction comparison and generic constant-sheaf pullback, rather than restating
   those comparisons. Each proof-only import supplies an API or instance used here:
   the abelian comparison, set AB5, flat Kan extension, and restriction/stalk comparisons.
   `EtaleSheaves` remains the sole public import, as needed by the signature. Compared
   old and new `proof_deps`: all three removed nodes are explicitly listed under
   `No longer needed`. The unit `sk-prop-sf-cbc` has empty `realized.statement` and
   `realized.steps`; no realized route is bypassed or changed.
5. **DAG agreement — pass.** Read each new proof step and the referenced dependency
   records. Their union is exactly `proof_deps`. Composition, restriction/site equivalence,
   finite-limit preservation, the abelian comparison, cover base change, and stalk
   comparison correspond to the Lean argument; `proof_origin` describes this route.

Second reading changed only this report: recorded independent signature, compilation,
axiom, search, edge-case, import, pruning and DAG checks, and clarified the inherited
open axiom closure. No mathematical or Lean repair was necessary.
