## What changed

Restored the assigned source from the quarantine path named by `coord/rework.tsv`.
Replaced the whole-proof hole of `AlgebraicGeometry.ProEtale.spTwists_commonCover`
by a reduction using `Scheme.tateTwist_finite_locallyFree`. Its covering, compatible
root sections and normalized isomorphisms are retained. The finite coefficient clause
is proved from the degree-one finite signed-line clause, with the quotient scalar map
identified by its uniqueness. Two lemmas on a single prescribed slice supply the
remaining integral/rational and algebraic-closure clauses.

Moved the existing constructions and already proved transition theorems verbatim to
`Sheaf.Paper.ProEtaleTateTwistLevels` and `Sheaf.Paper.ProEtaleTateTwistConstructions`,
publicly re-exported by the item, to allow those two lemma statements without an import cycle. Every old public import, name,
signature, data body and exported attribute is retained. The already complete proof of
`spTwists_locallyFree` is unchanged. Updated the physical module/file attachments for
the moved declarations and the common-cover node's actual proof dependency route.
Change record: `coord/changes/P4-proetale-tate-constructions-extraction.md`.

Validation: all five delivery modules compiled together in dependency order through
`lcompile.py`. The only warnings in that output came from the server's unpublished
`SfP1ChartExchange` dependency overlay, not these files. The actual moved declaration
and proof bodies were also compared byte-for-byte to the quarantine archive. The
seven direct importers listed in the change record also compiled unchanged against
the extracted modules. Their temporary source copies were removed from this delivery.
The compiler returned exit code zero for both validation runs.

## Proved and sorry left

Original item: one hole. Closed that whole-proof hole by a decomposition, not a complete
proof of its transitive argument: `AlgebraicGeometry.ProEtale.spTwists_commonCover`
(node `lem-route-sp-twists-common-cover`). Its common-cover selection, root identities,
finite coefficient clause and assembly are complete Lean proofs.

The item and both extracted construction files contain zero direct holes. Two new holes remain,
each the entire proof of a named public theorem in its own new module:

- `AlgebraicGeometry.ProEtale.spIntegralRationalRootBasis`, node
  `lem-sp-integral-rational-root-basis`: on one prescribed slice with normalized
  compatible roots, identify the integral inverse limit and its rational extension
  with their respective coefficient units, for one finite intermediate field.
- `AlgebraicGeometry.ProEtale.spQbarRootBasis`, node `lem-sp-qbar-root-basis`:
  on that kind of prescribed slice, identify the specified field colimit twist
  with its coefficient unit, respecting the prescribed colimit action.

Thus one upper hole is closed, two lower holes are added; this is a decomposition
(net hole change +1), not a net proof gain. No definition contains a hole, and
no already proved theorem has been replaced by a hole.

## No longer needed

No module is withdrawn or claimed pruned. The lower construction files import
`TateTwistFiniteLocallyFree` in place of the aggregate `TateTwistLocallyFree`;
the item retains its old aggregate public import. This narrows the lower file's
imports but does not remove the aggregate from the targets' import closure. The item's
former proof-only imports
`ConstantZModScalarTensor`, `FiniteDiscreteCondensedRing`, `FiniteDiscreteSchemeRing`,
`ScalarExtensionBinaryCoherence`, `IntegersModPow`, `Monoidal.Limits.Colimits`, and
`Filtered.Final` move with their actual uses to the construction files; they remain
needed there. All original public imports are retained.

The common-cover node now directly uses only the finite common-root theorem and the
two single-slice basis lemmas. Its old slice-sheafification, tensor, inverse-limit,
coefficient-limit, localization and field-colimit dependencies remain required by the
lower slice arguments, and are recorded there. They are not pruned mathematics.
The unit's root/finite/integral/rational/colimit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The initially absent item is a quarantine restoration assignment, not a withdrawal;
its archive and attachments are preserved. The archived module already proved all
its other historical holes, including finite-level comparison and transition laws.
Only the common-cover hole remained. The stated generic slice and coefficient
comparisons do not directly identify this particular root-tensor inverse system or
its field colimit: those are the two explicitly stated residual arguments.

Edge checks: the finite proof uses only ell^(r+1)=0, so includes the zero ring and
r=0. Both new statements concern an arbitrary single slice W with a supplied
normalized compatible root tower; neither asserts existence of a new cover. The
empty scheme or empty W imposes no nonemptiness assumptions. The positive index
n means exponent n+1, including ell=2 and ramified finite coefficient fields. Cofinality
uses a positive ramification exponent, and the algebraic-closure argument uses the
finite-subextension-valued coefficient colimit, not all continuous Qbar-valued maps.

## New nodes

`lem-sp-integral-rational-root-basis` formalizes the inverse-limit and localization
calculation for one E on one slice with a prescribed compatible root basis. Its
conclusion omits the covering-family existence and every finite/Qbar clause of the
parent, so it is strictly a part of the argument.

`lem-sp-qbar-root-basis` formalizes the field-transition-compatible basis and colimit
action calculation on one prescribed slice. Its conclusion is only the Qbar local
isomorphism. Its proof in words specifies the finite pure tensors, their limit and
localization maps, the common finite stage for products, and slice sheafification.
Both nodes carry the source, complete proof steps, searches and verbatim Lean statements.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
