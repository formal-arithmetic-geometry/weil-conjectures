# Supported Kunneth proof interface and local elaboration commands

Item: `Sheaf.AlgebraicGeometry.KunnethSupported`, group P9, 2026-10-21.

## Reason

The supported Kunneth proof needs a lower-bound result for the external product.
It also needs control of large derived-functor conversions to elaborate within the
existing compile limit. These changes supply the result and local proof settings.
No target statement, existing theorem statement or definition meaning changes.

## Old

`AlgebraicGeometry.Etale.isIso_supportedExteriorProduct` had one hole. Its module
opened CategoryTheory, CategoryTheory.Limits and AlgebraicGeometry, without the
additional local elaboration attributes listed below. The new lower-bound theorem
was not present. No adopted source-library file is changed by this packet.

## New

The original supported Kunneth statement and coefficient instances are unchanged.
The item's hole is replaced by a proof from the existing localization and comparison
lemmas and two separate new compatibility results, recorded as holes in report.md.

The item adds the public proved theorem
`AlgebraicGeometry.Etale.supportedExternalProduct_boundedBelow`, attached to
`lem-pur-supported-product-bounded-below`. It supplies precisely the lower bound
needed to apply localization and site comparison, using preservation of Tor
amplitude by inverse image and the general tensor estimate. Its proof has no holes.
The four new statement modules and their attachments are listed in report.md.

The item opens `MonoidalCategory` for tensor notation and adds local attributes
making totalization, the supported/ordinary pairings, and the pro-etale pairing
irreducible during proof elaboration. It locally enables the composition instances
for preservation of finite limits and colimits, and raises the local priority of
`CommRing.toRing` at the finite-coefficient specialization. It initially sets
`backward.isDefEq.respectTransparency` false for localization glue, then true before
the abstract predicate adapter and finite-ring specialization. These commands
control proof elaboration and prevent expensive unfolding; no global attribute is
added. The private witness transport is irreducible for the same reason.

## Users

No existing consumer requires adaptation: the old theorem retains its exact
signature, the new imports used only by proofs are private, and local attributes
and namespace openings do not change imported declarations. The new public
lower-bound theorem is used by the item proof. The item also uses the new
support-congruence, full-support and pro-etale naturality modules; the full-support
module uses the new forgetful pairing equation. Those uses and their DAG
attachments are included in this packet. No existing statement or definition was
repaired, no other group's module was adapted, and there are no forced adaptations.

## Status

landed 20261021T111424-L-124716 2026-10-21 (merge of deliver/P9/Sheaf.AlgebraicGeometry.KunnethSupported)

All five modules passed lcompile --all in dependency order, with the item in
27.4 seconds and the full-support module in 19.4 seconds. The item has zero holes;
the packet adds two separate compatibility holes and therefore records a
decomposition rather than net closure progress. The original main signature was
compared with the shared source after whitespace normalization and is identical.
The corrected node searches passed server preflight; the preceding change-record
failure was solely the absence of these five required section headings. During
the last delivery attempt, the compile server did not answer two axiom probes;
the tool continued and stated that merge reruns the probes. Delivery is resubmitted
with this corrected record for independent review.
