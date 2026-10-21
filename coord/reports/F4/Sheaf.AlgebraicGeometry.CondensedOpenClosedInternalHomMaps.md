## What changed

Restored `lean/Sheaf/AlgebraicGeometry/CondensedOpenClosedInternalHomMaps.lean`
from the exact quarantine path in `coord/rework.tsv`, preserving its six declarations
and the projection/evaluation constructions. This is a definition restoration/repair,
not a theorem-hole task.

The archived source fails to compile with
`failed to synthesize instance of type class PreservesFiniteColimits (i)_*⟦Λ⟧`
at the closed termwise functors. Repaired `closedPullbackDerivedAdjunction` and
`closedSupportProjection` by making this necessary exactness instance explicit.
`closedSupportHomMap` supplies it from `closedSupport_lowerStarExact Λ i j hij`,
scoped over the entire type (including the inverse-direction projection argument) and
its construction. No additional hypothesis on complementary pairs or derived inputs
is introduced. Open maps and their construction bodies are unchanged. Corrected the
module documentation, which had claimed the file stated invertibility/naturality;
those results belong to the consuming theorem.

Restored and adapted the three quarantined direct consumers in the same delivery:

- `Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization`: the two private
  closed-image helpers take exactness explicitly; the public theorem installs the
  already proved instance in its type and proof.
- `Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula`: the public theorem
  installs that instance in its type and proof.
- `Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom`: the two private closed
  projection naturality helpers take exactness, their explicit application supplies
  it, and the public theorem installs the same instance in its type and proof.

Also restored `Sheaf.SixFunctors.ClosedImmersionTensorProjection`, the quarantined
transitive consumer that uses the general closed adjunction and projection directly.
Its sole code change is supplying `closedSupport_lowerStarExact Λ f j hij` after
constructing its quasi-compact open complement; its public signature is unchanged.
The archived open tensor projection consumer compiles unchanged against this set.

All imports and existing proof arguments are retained. Four existing node copies
retain their Lean attachments and dependency route; their statement records now agree
with the actual scoped Lean types. The definition node's `statement_change` records
the explicit exactness correction and checks all three DAG citers: each already has
the complementary quasi-compact open hypothesis. The unit route is unchanged.

The change record is `coord/changes/F4-closed-derived-support-exactness.md`, with the
old/new signatures and both live and quarantined consumer inventory. No source-root
module or target signature is changed.

Validation: the restored maps, derived localization, support projection formula and
internal-Hom theorem compile together through `lcompile.py`, individually within the
60-second limit. The restored closed tensor projection and an unchanged copy of the
open tensor projection consumer also compile through `lcompile.py`. The final delivery
reruns compilation and the project preflight, including declaration/axiom probes.

## Proved and sorry left

Item holes before: 0. Item holes after: 0. Holes closed: none. Holes added: none.
Split-off statements: none. The assigned elaboration defect is repaired.

All six item definitions are restored with real construction bodies:
`openSupportDerivedAdjunction`, `closedPullbackDerivedAdjunction`,
`openSupportProjection`, `closedSupportProjection`, `openSupportHomMap`, and
`closedSupportHomMap` (namespace `AlgebraicGeometry.ProEtale.CondensedRing`).

The existing complete proofs of `condensedSupportDerivedLocalization`,
`openClosedSupportProjectionFormula`, `openClosedInternalHomFormulas`, and
`closedImmersionTensorProjection` are restored and adapted; none is counted as a
newly closed hole. There is no `sorry` in any of the five delivered modules, nor in
any definition. Existing holes in imported modules are unchanged, including
`existsUnique_supportDerivedTensorComparison`; no claim of transitive axiom-freedom
or closure progress is made for those unchanged inputs.

## No longer needed

None. No import, declaration, node, module, proof step, or dependency is pruned.
The quarantined archives are preserved. The current live downstream scan returns
zero modules because these paths were absent; that is not used as a withdrawal
argument. The DAG and quarantined parents still require these declarations.

## Where the brief, the DAG or earlier work was wrong

The dispatcher wording about a `sorry` does not describe this item: it is the listed
zero-hole rework/restoration. The archived closed termwise constructions omitted
finite-colimit preservation of direct image, so copying the archive without repair
fails to elaborate. The existing support exactness theorem has the necessary
complementary quasi-compact open hypotheses. It is supplied directly in every
complementary-pair application; no unproved general closed-image exactness assertion
is introduced. The definition node now documents the explicit exactness requirement
for the two general closed constructions.

The three archived consumers also failed at closed termwise functors without this
instance. They are restored with the required local instance and their actual
projection, localization and Hom arguments intact. The further closed tensor
projection consumer needed the same local instance. No numbered return for this item
is present in the current local F4 return file; the rework row records the cluster
restore rollback as its reason.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
