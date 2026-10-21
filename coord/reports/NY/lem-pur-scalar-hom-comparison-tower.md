## Worker report

Item: lem-pur-scalar-hom-comparison-tower. Group NY, stage 2.

The module Sheaf.Algebra.Homology.ScalarHomComparisonTower states
CategoryTheory.scalarHomComparisonTower with a single postponed proof. It defines
no objects and copies no comparison construction. The statement and proof fields
of the DAG node are unchanged. The landed normalized scalar-data dependency is
retained. A new existing-definition node records the evaluation-defined map and replaces the unused coefficient-system
theorem dependency. There are no dependency-module repairs or statement corrections.

Sources read: literature/stacks-project/sites-cohomology.tex,
lemma-pullback-tensor-product (07A4), lines 3684 onward; equation-internal-hom,
lines 8835–8850; lemma-internal-hom (08J9), lines 8896–8931. The coefficient tower
and identity claims are the formal calculations in the item's seven proof steps,
not extra tower statements attributed to Stacks. The theorem docstring records
all seven steps, including the tensor-tower rearrangement and endpoint transports.

Hypothesis and clause correspondence:

- A site small relative to modules is `{C : Type c} [Category.{v} C]` and
  `{J : GrothendieckTopology C}` with module/coefficient universe `max c v r`.
  `HasSheafify`, `WEqualsLocallyBijective`, and `HasSheafCompose` are the existing
  general-site interfaces. They impose no geometric property on the site.
- Ring sheaves are `Sheaf J CommRingCat.{max c v r}`. Every occurrence of `a : R ⟶ S`
  and `b : S ⟶ V` is the actual given sheaf morphism; `a ≫ b` is the composite.
- The ordinary unbounded categories are `DerivedCategory (scalarModules J R)`
  with the explicitly chosen localization universe `w`; there is no bounded or
  complete subcategory. The simultaneous `HasDerivedCategory` binder and
  `ScalarHomModels.{c,v,r,w} J` follow the exact existing coherence interface.
  The former is a size/choice interface, not a hypothesis on a coefficient map.
- `M.closed R` is the existing closed structure on the exact bifunctor
  `derivedInternalHomOfUniverses J R`. Its tensor model is `M.model R`.
  `(M.scalar a).derived` is a universal left-derived scalar extension whose
  ordinary objects/maps are the sheafified scalar tensor and whose K-flat
  comparison is invertible, as required by `ScalarDerivedPair`.
- `μ a : ScalarHomTensorComparison M a` retains the pure-generator chain formula,
  K-flat preservation and representative normalization, not an arbitrary isomorphism.
  `(μ a).iso` points from extension of tensor to tensor of extensions.
- `scalarHomExtensionComp M a b` is exactly the canonical unit-normalized
  balanced scalar associator `T_b T_a ≅ T_(ba)`, not an independently supplied map.
  `scalarHomExtensionId M R` is the scalar multiplication unitor.
- `htower` and `hid` reproduce the two actual tensor equations of
  `scalarHomTensorCoherence`. They are explicit assumptions, as in this item.
  They make no assumption about internal-Hom invertibility.
- Every occurrence of `c` is the existing `coefficientBaseChangeHom`, with
  arguments `(M.closed R) (M.closed S) (M.scalar a).derived (μ a).iso P Q`.
  Reading its body gives precisely the closed transpose of `μ.inv` followed
  by the image of evaluation. The recorded closed interface and the source
  equation use evaluation `H(P,Q) tensor P → Q`. The node permits using symmetry:
  in its displayed convention `P tensor H(P,Q) → Q` is this evaluation preceded
  by the signed symmetry. The canonical normalized scalar tensor comparison
  commutes with that symmetry (on total pure tensors both swaps have the same
  Koszul sign). Therefore the two transposes define the same map. We use the
  existing definition directly, without creating a second P-left comparison.
- The first conjunct quantifies over every coefficient map and every
  `f : P' ⟶ P`, `g : Q ⟶ Q'`. `Prod.mkHom f.op g` is contravariance in P and
  covariance in Q. Its square is `T_a(H_R(f,g)) ≫ c_(P',Q') =
  c_(P,Q) ≫ H_S(T_a f,T_a g)`. Instantiating at a, b and a ≫ b gives all three
  naturality assertions in the node.
- The second conjunct is exactly `T_b(c_a) ≫ c_b ≫
  H_V(alpha_P inverse, alpha_Q) = alpha_(H_R(P,Q)) ≫ c_(ba)`.
  The first endpoint is `((scalarHomExtensionComp M a b).inv.app P).op`;
  the second is `((scalarHomExtensionComp M a b).hom.app Q)`.
  Thus both arrows have source `T_b T_a H_R(P,Q)` and target
  `H_V(T_(ba) P,T_(ba) Q)`, with the first Hom argument reversed correctly.
- The third conjunct is `c_id ≫ H_R(u_P inverse,u_Q) = u_(H_R(P,Q))`.
  This is identity after identifying `T_id` with identity by scalar multiplication;
  it is not the ill-typed claim that an untransported comparison is literally identity.
- There are no flatness, finite-free, perfectness, boundedness, completeness or
  isomorphism assumptions on P, Q or any Hom comparison. Both input complexes
  range over the whole ordinary derived categories.

Dependency declarations read and used:

- Sheaf.CategoryTheory.SiteCoveringAxioms:
  CategoryTheory.Precoverage.IsSiteForCoverings, plus its imported Mathlib
  GrothendieckTopology interface for the topology of a site.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules;
  the inherited Mathlib category is SheafOfModules, not a new category.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory,
  HasDerivedCategory, and the localization functor Q.
- Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses:
  CategoryTheory.derivedInternalHomOfUniverses and its defining K-injective lift.
- Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal:
  CategoryTheory.ringedDerived_closed_symmetric_monoidal; imported for the
  proof's closed structure and signed symmetry, not assumed as a new axiom.
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel:
  SheafOfModules.DerivedChangeOfRingsCochainModel and
  SheafOfModules.nonempty_derivedChangeOfRingsCochainModel; this is the universal
  derived pair underlying the normalized scalar interface.
- Sheaf.Algebra.Homology.ScalarHomTensorCoherence:
  CategoryTheory.scalarHomTensorCoherence, whose two tensor equations are
  the statement's explicitly assumed htower and hid.
- Sheaf.Algebra.Homology.ScalarInternalHomData (added landed dependency
  def-sfb-scalar-hom-comparison-data): SheafOfModules.scalarModules,
  SheafOfModules.ScalarDerivedPair, CategoryTheory.ScalarHomModels,
  CategoryTheory.ScalarHomTensorComparison, CategoryTheory.scalarHomExtensionComp,
  CategoryTheory.scalarHomExtensionId. Their full normalization fields and the
  directions of the two scalar isomorphisms were read.
- Sheaf.Paper.CoefDerivedSystemEvaluationCalculus (new existing-definition dependency
  def-pur-coefficient-base-change-hom):
  WeilConjectures.coefficientBaseChangeHom, whose generic signature and full
  evaluation-transpose body were read. The coefficient-system theorem itself
  is not invoked or specialized; only its existing generic map is reused.
  The new definition node depends only on def-coef-ringed-tensor-hom-model,
  and its dependency closure does not reach this item (checked again during repair).

Edge cases checked mathematically before and after drafting: P=0 or Q=0 gives
maps between the corresponding zero internal Homs; either identity leg retains
both alpha endpoints; the all-identity tower reduces to the scalar unitor formula.
For Z → F_2 → F_2, the statement still makes no claim that the Hom map is an
isomorphism, so it does not implicitly require flatness. No nonempty-site or
nonzero-ring hypothesis excludes an empty site or zero coefficient ring.
The independent c, v, r and w binders retain site objects/arrows and module sizes.

Searches made:

- msearch.py leanfinder, query: "Evaluation defined scalar extension internal Hom
  comparison respects coefficient towers and identity". Eight hits:
  ModuleCat.ihom_ev_app; ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.evalAt_apply;
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.evalAt;
  ModuleCat.homEquiv_extendScalarsId;
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply;
  ModuleCat.homEquiv_extendScalarsComp;
  ModuleCat.ExtendRestrictScalarsAdj.homEquiv;
  ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction_hom_apply.
  None is the ring-sheaf derived Hom comparison tower statement.
- msearch.py loogle, query:
  "CategoryTheory.MonoidalClosedFunctor.comparison,
  CategoryTheory.Functor.LaxMonoidal.ihomComparison". Zero hits; unknown identifier
  CategoryTheory.MonoidalClosedFunctor.comparison.
- msearch.py grep, query `ihomComparison|closed.*[Cc]omparison|comparison.*comp`
  in CategoryTheory/Monoidal/Closed: nine hits in Functor.lean and Ideal.lean.
  The comparison is Cartesian exponential comparison, not this tensor-Hom theorem.
- rg in lean/WeilConjectures and lean/Sheaf for the item id,
  scalarHomComparison and scalar.*Hom.*[Tt]ower found no existing item theorem;
  ScalarInternalHomTowerCoherence is the different restriction-side adjunction map.
- Further rg in both project roots for scalar/Hom comparisons located
  IntegralOperationsScalarComparisons.scalarHomOrdinary, which reuses the
  existing generic coefficientBaseChangeHom. Read that generic definition and
  reused it here. The completed and finite-free specializations do not state
  this arbitrary ring-sheaf coefficient tower result.
- DAG text search found lem-coef-monoidal-square-hom-transport. Its hypothesis is
  a square of strong symmetric monoidal functors and a monoidal square isomorphism;
  it is not this theorem under just the specified tensor equations. No existing
  declaration exactly states the item. The existing declaration-name searches
  found no CategoryTheory.scalarHomComparisonTower before this delivery.

Original delivery validation (before this metadata-only repair): scompile.py compiled the delivered file separately as
Sheaf.Stage2.Sandbox0 (9.8 seconds) and as its final library module (9.5 seconds),
with no warnings or errors. All variables and universes are explicitly bound,
all Lean lines are at most 100 characters, and the only sorry is the theorem proof.
No statement dispute or source error was found.

## Second reading by NY

The dispatcher forbids starting other agents, so this is the author's second pass;
the maintainer supplies the independent review. I reread the unchanged node, the
new signature, coefficientBaseChangeHom's body, the ScalarHomTensorComparison
normalization, and the canonical extension composition/identity definitions.
The correspondence above covers each hypothesis and clause. In particular, I
checked that a ≫ b denotes R → V, that the first endpoint uses alpha inverse
before op, that the final endpoint uses alpha forward, and that the identity
conclusion equals u_H rather than an untransported identity. I also compared the
H tensor P evaluation convention against the source and the node's allowed
symmetry convention: no new comparison definition is needed. No mismatch was
found and no theorem statement or dependency interface was changed in this pass.


## New nodes

`def-pur-coefficient-base-change-hom` records the existing explicit definition
`WeilConjectures.coefficientBaseChangeHom` in
`Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, with `existing: true` and no new
module. The categories A and B, bifunctors HA/HB, closed structures SA/SB, functor F,
natural tensor isomorphism μ, and objects P/Q are exactly its binders. Its codomain
is HB(FP,FQ), and its body is SB.transpose applied to μ.inv at (HA(P,Q),P), followed
by F.map of SA.evaluation. Thus the definition has real data and does not use the
coefficient-system existence theorem or any `.choose`. Its source is Stacks 08J9,
equation-internal-hom, applied to the evaluation-transpose construction already
spelled out in the item. The closed-structure dependency is
`def-coef-ringed-tensor-hom-model`, whose recorded declaration list includes
`CoefficientClosedStructure` and its tensor, evaluation and transpose.

Repair searches: LeanSearch queried “The internal Hom base change map for a tensor
compatible functor is defined by transposing its image of evaluation”; its eight
hits concern linear-map base change and ihom evaluation. LeanFinder queried
“Transpose of inverse tensor comparison followed by functor applied to evaluation
defines internal Hom comparison”; its eight hits concern Cartesian exponential
comparison. Mathlib grep for `coefficientBaseChangeHom|ihomComparison|closedIhom`
in CategoryTheory/Monoidal/Closed returned five groupoid functor-category hits.
Project rg found the exact definition at CoefDerivedSystemEvaluationCalculus:195
and its consumers, with no upstream WeilConjectures definition. DAG rg found the
coefficient-system theorem helper list and references in specialized arrow-node
search/review records, but no definition node for this generic map.
`tools/blueprint_refs.py search coefficientBaseChangeHom` returned zero matches.
The exact search outputs are retained in the new node's mathlib_searches.

## Return L repaired

The return for immutable head e85e0a80dc1b requested a definition node instead of
citing `lem-coef-derived-system-evaluation-calculus` merely for a plain definition.
The new node above supplies that record. The item now cites it in stmt_deps in
place of the theorem. The theorem is absent from proof_deps, because none of its
conclusions is needed. The Lean module, including its statement and docstrings,
is byte-for-byte retained. The item's source, mathematical statement, proof and
proof_deps are unchanged from the shared base. The delivery wrapper rebases the
packet on the current main branch.

Second reading of the repair by NY: I matched every binder and the full explicit
body of coefficientBaseChangeHom with the new node, read CoefficientClosedStructure
and its tensor/evaluation/transpose definitions, and rechecked that the item uses
only this map. Zero inputs, identity functors with identity tensor comparison,
and noninvertible Hom comparison maps are allowed. Site and category universes
are unchanged. The original theorem's naturality/tower/unit correspondence and
edge-case analysis above remain applicable. No mathematical statement changed.

Repair validation: structural self-check passed (the new node has exactly the
required fields; all mathematical item fields and the theorem signature are
unchanged; the new dependency has no cycle, with 208 reachable dependencies).
The new lean.statement is verbatim from the current server source read through
scompile.py --source. The initial prescribed dry run failed before Lean
elaboration because a Mathlib tensor-product object file was missing. The
explicit scompile.py retry on the repaired packet also failed before elaboration:
Mathlib/Algebra/Category/Ring/Basic.olean is missing. Both server confirmations
say “Live published library is unavailable”. Two subsequent dry runs on the
repaired packet also failed before compiling the submitted theorem. The first
encountered a 60-second timeout in the upstream HomComplexSectionsCochains
overlay; server confirmation then failed on a missing tensor-product object
file. The final retry failed identically in local overlay and server confirmation:
`Sheaf/Paper/CoefficientHomRepresentativeEvaluation.lean:6:0` cannot import
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic` because
`/home/ubuntu/weil-conjectures-sheaf/lean/.lake/build/lib/lean/WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean`
does not exist. This is a published-library/tool infrastructure failure, outside
the read-only worker permissions. The repaired packet is retained; no push was
attempted because the required dry run did not pass.

## Retained-packet retry, 2026-10-21

The prescribed initial deliver2.py --no-push retry and a separate scompile.py
retry both fail before elaborating the submitted module. Their local overlay
and server confirmations independently report that the published object file
WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean does not exist,
while compiling the upstream CoefficientHomRepresentativeEvaluation overlay.
No launcher script, upstream module or published library was modified.
The saved definition-node repair is retained. The self-check again verified
that the existing definition signature and delivered theorem signature match
their lean.statement records verbatim, and the item mathematical statement,
proof and proof_deps match the current shared checkout. Refreshed only stale
lean_audit metadata from that checkout so the packet carries no unrelated
metadata delta; the delivery differences remain lean and stmt_deps.
The theorem still has one whole-proof sorry and satisfies the line-width rule.
The missing published object file prevents the required clean compile and push.

The retained packet was inspected on this retry: the requested definition node
`def-pur-coefficient-base-change-hom` is present and replaces
`lem-coef-derived-system-evaluation-calculus` in the item's statement dependencies;
the unused theorem is not in proof dependencies. The theorem module is retained.
Two prescribed `deliver2.py --no-push` attempts and a direct `scompile.py` attempt
failed before elaboration, both locally and in server confirmation. The first
reported missing published
`WeilConjectures/Mathlib/SetTheory/Cardinal/HasCardinalLT.olean`; the direct compile
and final dry run reported missing published
`WeilConjectures/SixFunctors/Etale/Derived/Hom.olean` while importing
`Sheaf.Algebra.Homology.ScalarInternalHomData`. Each failure occurred in about
0.4–0.5 seconds, not a server-busy timeout. No compiler diagnostic concerns the
submitted theorem. The published build is read-only and launcher tools may not
be patched, so no push was attempted. Packet retained for the next retry.


## Retained-packet retry: upstream overlay errors, 2026-10-21

The prescribed first action, deliver2.py NY lem-pur-scalar-hom-comparison-tower
--no-push, was run on the saved repaired packet. It progressed past the former
missing-object failures but failed before elaborating any submitted theorem in
upstream overlay Sheaf.CategoryTheory.RingedSiteDualityMaps, snapshot
95fe8449bb0472d0fb5c47544aef5f199bafc802ac4938eb2ebb3f54e7f22318.
The errors are type mismatches at 795:4 (Eq.trans of hβ and hγ versus the
composite with homComplexπ) and 828:4 (ringedSiteBidualDegree_eval versus the
coefficientHomComponent formula). A separate prescribed scompile.py call on
ScalarHomComparisonTower.lean returned the same two errors (27.5 s recorded).
This is neither a server-busy timeout nor a diagnostic in the delivered file.

The existing definition's required import closure reaches that upstream module:
CoefDerivedSystemEvaluationCalculus -> RingedInternalHomShiftOfUniverses ->
RingedSiteDualityMaps. A smaller import cannot expose coefficientBaseChangeHom,
which is declared in CoefDerivedSystemEvaluationCalculus; duplicating or replacing
that canonical definition is not the requested repair. The live upstream source,
published library and launcher scripts were not modified.

The required self-check was repeated: item fields differ from the shared base
only in lean and stmt_deps; mathematical statement, proof and proof_deps are
unchanged. The module's theorem signature and the existing definition signature
match their lean.statement records verbatim. The new definition node has exactly
the required fields, is absent from the current shared DAG, has no dependency
cycle (209 reachable nodes in the current checkout), and is cited by the item.
The unused coefficient-system theorem occurs in neither stmt_deps nor proof_deps.
The theorem module remains unchanged, with one whole-proof sorry and maximum
line width 90. All saved repair work is retained pending a working upstream build.

The final deliver2.py --no-push retry returned the identical upstream overlay
type mismatches at RingedSiteDualityMaps.lean:795:4 and :828:4. Thus two dry
runs and one direct compile fail before the packet is checked; nothing was pushed.


## Retained-packet final retry, 2026-10-21

On the next dispatched retry, the prescribed initial dry run and a separate
scompile.py invocation again failed in the unchanged upstream overlay snapshot
95fe8449bb0472d0fb5c47544aef5f199bafc802ac4938eb2ebb3f54e7f22318,
at RingedSiteDualityMaps.lean:795:4 and :828:4. Both diagnostics are the
same type mismatches recorded above, before checking this submission. Searches
confirmed that coefficientBaseChangeHom is declared only in
CoefDerivedSystemEvaluationCalculus; a narrower import cannot provide that exact
existing declaration. scompile.py --source read its current live declaration
and explicit transpose body successfully, confirming the saved binding.

The required repair remains intact: def-pur-coefficient-base-change-hom owns the
existing definition record and replaces the unused coefficient-system theorem
in stmt_deps. Repeated self-checks found only lean/stmt_deps differences from
the shared item's node; statement, proof and proof_deps are unchanged. Both
signature records are verbatim, the Lean module has one sorry and maximum line
width 90, and the new node's 209-node dependency closure is acyclic and does
not reach the item. No live source, published artifact or launcher tool was
modified. A final dry-run retry is recorded below.

The final dry run failed with the identical two upstream type mismatches
at RingedSiteDualityMaps.lean:795:4 and :828:4 (27.5 s cached compile result).
Two dry runs and a direct compile were tried on this retry; no push occurred.


## Dispatched retained-packet retry, 2026-10-21

The prescribed initial dry run and direct scompile.py check both failed before
elaborating this delivery, in upstream RingedSiteDualityMaps.lean:795:4 and
:828:4, with the same two type mismatches as the preceding attempt. This retry
used overlay snapshot
fcf3d81923f39a93f40790da657d1c7172b3a0564784c7d1d9117dd13b53e8fb
(the wrapper records 21.7 seconds). This is a compiler error, not a busy-server
no-answer timeout. The required existing coefficientBaseChangeHom declaration
is still defined in CoefDerivedSystemEvaluationCalculus, which imports
RingedInternalHomShiftOfUniverses and thereby RingedSiteDualityMaps. An import
change cannot expose that exact declaration while omitting its import closure.
Read-only upstream sources and launcher tools were not changed.

The self-check against the current shared node passes: the only differing fields
are lean and stmt_deps; mathematical statement, proof and proof_deps are identical.
The new existing-definition node has exactly the required fields and remains
absent from the shared DAG. Its signature matches the current defining source
verbatim. Its 208-node dependency closure does not reach this item. The item
cites that definition and does not cite the unused coefficient-system theorem
in either dependency list. The retained theorem signature matches its record,
has one whole-proof sorry, and has maximum line width 90. The reviewed Lean
statement is unchanged. A final dry run follows this report update.

The final dry run returned the identical upstream type mismatches at 795:4 and
828:4. Two dry runs and one direct compile failed before checking the submission;
no push was made, and the repaired packet remains in this sandbox.


## Current dispatched repair retry, 2026-10-21

Inspected the saved report and packet before running the prescribed initial
deliver2.py --no-push. It failed before checking the submitted module in
read-only upstream RingedSiteDualityMaps.lean:795:4 and :828:4. A separate
scompile.py invocation on ScalarHomComparisonTower.lean returned the same
two type mismatches, using snapshot
fcf3d81923f39a93f40790da657d1c7172b3a0564784c7d1d9117dd13b53e8fb
(21.7 seconds recorded). This is not an exit-124 busy-server timeout.

Repeated the required self-check against the current shared checkout: only lean
and stmt_deps differ on the item; statement, proof and proof_deps are identical.
The existing-definition node requested by return L is present, cited in place
of the unused theorem, and absent from the shared DAG. Its 209-node dependency
closure does not reach the item. Both lean.statement records match the source
signatures verbatim. The unchanged theorem module has one whole-proof sorry
and maximum line width 90. The explicit coefficientBaseChangeHom body remains
the closed transpose of inverse tensor comparison followed by F(evaluation).
Its defining module's import closure reaches the failing upstream module;
a smaller import cannot supply that exact existing declaration. No upstream
source, published library or launcher script was modified. The repaired packet
is retained, with a final prescribed dry-run retry pending below.

The final dry run failed with the identical upstream type mismatches at
RingedSiteDualityMaps.lean:795:4 and :828:4. Two dry runs and one direct compile
failed before checking the submission. Nothing was pushed.


## Saved-packet repair retry, 2026-10-21

Inspected the saved packet and ran the prescribed initial deliver2.py --no-push.
It failed in read-only upstream RingedSiteDualityMaps.lean:795:4 and :828:4,
before checking the submitted theorem. A direct scompile.py check reproduced
the same two type mismatches in snapshot
fcf3d81923f39a93f40790da657d1c7172b3a0564784c7d1d9117dd13b53e8fb
(21.7 s recorded). This is not a busy-server no-answer timeout.

The required repair remains present: def-pur-coefficient-base-change-hom records
the existing explicit definition, and the item cites it rather than the unused
coefficient-system theorem. The self-check against the current shared base passes:
only lean and stmt_deps differ; statement, proof and proof_deps are unchanged.
The two added dependencies relative to that base are the already landed
def-sfb-scalar-hom-comparison-data and the requested new definition node.
Both signature records are verbatim; the theorem has one whole-proof sorry and
maximum line width 90. The new node has exactly the prescribed fields and an
acyclic 208-node dependency closure that does not reach this item.
scompile.py --source successfully read the current defining module. Project
search confirms that only CoefDerivedSystemEvaluationCalculus declares the
required map; its import closure reaches the failing upstream module, so a
smaller import cannot provide this exact existing declaration. No live source,
published artifact or launcher tool was modified. A final dry run follows.

The final dry run reproduced those identical upstream errors at 795:4 and
828:4. Two dry runs and one direct compile failed before checking this delivery.
No push occurred; the repaired packet is retained.


## Saved-packet retry: current upstream snapshot, 2026-10-21

Read the retained packet, return L at immutable head e85e0a80dc1b, and the
current shared declaration. The initial prescribed deliver2.py --no-push and
a direct scompile.py both failed before checking the submission in upstream
RingedSiteDualityMaps.lean:795:4 and :829:4, with the same two type mismatches
in snapshot 287b690c0bcd7907f8b7e91c04b4ebf395dd0110aa188cf7fe3c3bca4815fe1f.
The first error concerns composing the component projections; the second
concerns the bidual evaluation formula. These are upstream elaboration errors,
not busy-server timeouts or errors in the retained delivery.

Self-check against the current shared base: only lean and stmt_deps differ;
statement, proof and proof_deps are unchanged. The definition-node repair
requested in L remains present, cites the existing coefficientBaseChangeHom,
and replaces the unused theorem dependency. Both signature records are
verbatim from their source files. The theorem has exactly one whole-proof
sorry, maximum line width 90, and SHA256
e57831001285aafddff34238c39f8c8b93f12286bdeff500d1f0d2706ceb45d1.
The new node has exactly the required fields; its 209-node dependency closure
does not reach this item. No Lean statement, live source, published artifact
or launcher tool was modified. The required final dry run follows.

The final prescribed dry run again failed before checking the submission,
with identical upstream type mismatches at RingedSiteDualityMaps.lean:795:4
and :829:4, now in snapshot
bc318d2a0270494173b21eed0f04664fba269497e861bc47c95cbfa5787b052d
(48.3 s recorded). Two dry runs and one direct compile were attempted.
Nothing was pushed; the repaired packet is retained.

## Final repair retry: 2026-10-21

After waiting for the prior overlay timeout, the prescribed `deliver2.py --no-push`
retry reached upstream snapshot `fcf3d81923f39a93f40790da657d1c7172b3a0564784c7d1d9117dd13b53e8fb`
and failed before checking either submitted file at
`Sheaf/CategoryTheory/RingedSiteDualityMaps.lean:795:4` and `:828:4`.
The required direct `scompile.py` invocation reproduced exactly these two type
mismatches. The final `deliver2.py` push attempt also returned `COMPILE FAILED on
the server, nothing pushed` with the same diagnostics. These errors are in the
read-only upstream overlay and are unrelated to this packet; no source, library
artifact, or launcher script was modified.


## Dispatched saved-packet verification, 2026-10-21

The prescribed initial deliver2.py --no-push and a separate scompile.py
invocation both failed before checking this delivery in read-only upstream
RingedSiteDualityMaps.lean:795:4 and :828:4, overlay snapshot
fcf3d81923f39a93f40790da657d1c7172b3a0564784c7d1d9117dd13b53e8fb.
The first mismatch is the component-projection composition equation; the second
is the bidual evaluation equation. These are the same upstream errors as the
previous attempt, not a server-busy no-answer timeout.

Self-check against the current shared checkout passed: only lean and stmt_deps
differ on the item; its statement, proof and proof_deps are unchanged. Return L's
existing-definition node is present and cited, and the unused coefficient-system
theorem occurs in neither dependency list. Both signature records are verbatim
from their source files. The theorem file retains SHA256
e57831001285aafddff34238c39f8c8b93f12286bdeff500d1f0d2706ceb45d1,
one whole-proof sorry, and maximum line width 90. The new node is absent from
the shared DAG and its full statement/proof dependency closure is acyclic
and does not reach the item.

Project search confirms coefficientBaseChangeHom is declared only in
CoefDerivedSystemEvaluationCalculus. That module imports
RingedInternalHomShiftOfUniverses, which imports RingedSiteDualityMaps. A narrower
import cannot supply the reviewed existing declaration. The canonical definition
and reviewed theorem remain intact; no upstream source, published library or
launcher script was modified. A final prescribed dry run follows.

The final dry run reproduced the identical upstream errors at 795:4 and
828:4. Two dry runs and one direct compile failed before checking this packet.
The full new-node dependency closure contains 209 nodes. Nothing was pushed;
the repaired packet remains in the sandbox.


## Successful saved-packet verification, 2026-10-21

The prescribed initial deliver2.py --no-push now passes: dry-run commit
ac9cf376123 passed server preflight and all per-file compilation checks.
This supersedes the upstream-build failures recorded in the earlier retries.
The saved repair requested by return L is retained without changing the reviewed
Lean theorem: def-pur-coefficient-base-change-hom owns the existing explicit
coefficientBaseChangeHom definition, and replaces the unused coefficient-system
theorem in stmt_deps. That theorem is absent from proof_deps as well.

The final self-check against the current shared base found changes only to lean
and stmt_deps. The mathematical statement, proof and proof_deps are unchanged.
Both signature records are verbatim. The theorem retains SHA256
e57831001285aafddff34238c39f8c8b93f12286bdeff500d1f0d2706ceb45d1,
one whole-proof sorry and maximum line width 90. The new definition node has
exactly the prescribed fields, is absent from the shared DAG, and its 209-node
statement/proof dependency closure is acyclic and does not reach the item.
Reread the actual definition body, CoefficientClosedStructure's tensor,
evaluation and transpose, the canonical scalar extension comparisons, and
Stacks equation-internal-hom, lemma-internal-hom and
lemma-pullback-tensor-product. The definition is the explicit transpose of
inverse tensor comparison followed by the functor's image of evaluation.
No new mismatch was found. No live source or launcher tool was modified.
