## What changed

Replaced the sorry in `AlgebraicGeometry.exists_selfTor_target_basic_localization`
with a complete Lean proof. Its signature and visibility are unchanged. The proof
combines coordinates on all algebraic Tor classes with preservation of the normalized
pure conormal wedge by a certified resolution-induced restriction map. Naturality of
the ideal-sheaf inclusion supplies the required equality on actual ideal sections.

Added four modules: `SelfTorRestrictionCertificate` defines the explicit chain-level
certificate (no postponed data); `SelfTorTargetRestrictionCoordinates` isolates the
sheafified K-flat coordinate comparison; `KoszulRestrictionTestCycles` proves the
compatible Koszul cycle construction; `SelfTorRestrictionConormalWedge` proves the
algebraic normalization step from the certificate, cycle construction, and the existing
`selfTorConormalComparison_spec`, using homologyπ naturality and cancellation of the
projective-resolution isomorphisms. Each new module has its own node.

All five modules compile through lcompile.py. The cycle construction builds the
normalized scalar-extension isomorphism with real exterior-basis data, transfers
the lift by the extension/restriction adjunction on complexes, checks augmentation
on the degree-zero generator, constructs cycles by iCyclesIso after proving the
quotient-tensored differentials vanish, and proves the tensor cycle equation. New imports in the item are proof imports.
No existing statement or definition changed, no consumer was adapted, and no target changed.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.exists_selfTor_target_basic_localization`
(node `new-t2-self-tor-target-basic-localization`). Also proved the new algebraic theorem
`AlgebraicGeometry.selfTor_restriction_conormal_wedge`
(node `new-t2-self-tor-restriction-conormal-wedge`).

Also proved `AlgebraicGeometry.exists_koszul_restriction_test_cycles`
(node `new-t2-koszul-restriction-test-cycles`). Its private helpers are all proved;
its basis isomorphisms and cycles are actual constructions, with no postponed data.

One new hole remains, the whole proof of a public theorem:

- `AlgebraicGeometry.exists_selfTor_target_restriction_coordinates`, node
  `new-t2-self-tor-target-restriction-coordinates`: construct the sheaf coordinates
  and show compatibility on arbitrary algebraic Tor classes. It does not mention the
  conormal comparison or any ideal-wedge tuple.
This is a decomposition: one original hole closed, one new hole added; net 0.
The algebraic half of the plan, including the compatible-cycle construction and
normalized wedge transport, is fully proved from the existing library interfaces.
There are no remaining holes in the assigned module or in any definition.

## No longer needed

Removed the assigned module's direct proof import
`Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`. Its statement is still
needed below `SelfTorTargetRestrictionCoordinates`, where its proof import now lives.
The existing conormal comparison and affine-section modules remain needed.
The unnormalized existential theorem in `Sheaf.RingTheory.KoszulBaseChangeIso`
(node `lem-sc-koszul-base-change-iso`) is not needed by the new cycle proof, so its
provisional import and proof dependency were removed. Its standard-basis construction
was reused privately with the actual wedge equations exposed to this proof; importing
its bare existential statement would not provide those equations. This does not
claim that other users of that existing module have been pruned. No original
proof node or module is pruned from the transitive route. The unit route is unchanged.

Discarded the unlanded previous attempt's `SelfTorTargetBasicLocalizationCore` and its
node: it repeated the assigned statement and was not a reduction. Removed unchanged
sandbox copies of other library modules; they are not part of this delivery.

## Where the brief, the DAG or earlier work was wrong

The previous core statement had exactly the assigned theorem's hypotheses and conclusion.
Applying it merely moved the original sorry. This delivery replaces that with two strict
parts, joined by actual Lean proofs at the algebraic and sheaf levels.

The original node's sheafification lemma gives a quasi-isomorphic affine augmentation,
not the derived-tensor homology coordinates or their principal-localization compatibility.
Those comparison steps need the first intermediate theorem. The proved cycle theorem
makes explicit the chain-level construction that the original plan used only in prose. The existing Koszul scalar-extension theorem gives an unnormalized
existential isomorphism; its proof constructs the standard-basis isomorphism, which is
the normalized construction required by the cycle-transport argument.

Edge cases checked in the new statements: n=0 uses the empty wedge and ψ(1)=1; full
ideals and zero quotient rings give zero tensor complexes; φ need not be flat in the
algebraic cycle statement; the geometric statement assumes a principal localization,
which is flat. No regularity or finite-generation hypothesis was added.

LeanSearch was attempted and returned an Internal Server Error; LeanFinder and Mathlib
source searches ran. Searches found generic projective-resolution and scalar-extension
interfaces, but no exact version of these project-specific comparisons.

## New nodes

`new-t2-self-tor-restriction-certificate` is the definition of the resolution certificate
in `Sheaf.RingTheory.SelfTorRestrictionCertificate`; it contains no sorry or chosen data.

`new-t2-self-tor-target-restriction-coordinates` is the remaining sheaf coordinate and
restriction comparison in `Sheaf.AlgebraicGeometry.SelfTorTargetRestrictionCoordinates`.

`new-t2-koszul-restriction-test-cycles` is the proved chain-level construction in
`Sheaf.RingTheory.KoszulRestrictionTestCycles`.

`new-t2-self-tor-restriction-conormal-wedge` is the proved algebraic normalization result
in `Sheaf.RingTheory.SelfTorRestrictionConormalWedge`.

No change records are needed: all existing interfaces and public imports are unchanged.

## Second reading by T2

1. **Statements and interfaces.** I compared the delivered item and all adapted files with
`sheaf-dag`. Existing declaration signatures and visibility are unchanged; the target
statement is byte-for-byte unchanged apart from proof-import and proof-body text. The
remaining coordinate theorem has the same hypotheses and conclusion as its node and is a
strict intermediate statement: it omits the conormal wedge tuple and the final localization
wedge equation. The certificate is a predicate with explicit resolution data and contains
no chosen witness or postponed definition data.

2. **Proof and trust.** I compiled the five delivered modules with `lcompile.py --all` and
searched them for forbidden declarations and unscoped `sorry`. The only remaining `sorry`
is the whole public theorem `exists_selfTor_target_restriction_coordinates`, with its
blueprint node and complete proof docstring. The other theorem proofs and every definition
are concrete. The cycle proof constructs the scalar-extension isomorphism, Koszul cycles,
and lifts explicitly; no arbitrary existence witness is stored in a definition. The
axiom probe is delegated to `deliver3.py` as required for the final check.

3. **New statements.** I checked the four new nodes against their Lean declarations and
against the imported declarations used by each proof. The certificate predicate is exactly
the all-resolutions comparison property used by the wedge theorem. The cycle theorem is
strictly below the wedge theorem and only asserts compatible Koszul test cycles. The wedge
theorem is algebraic and does not assert any sheaf coordinate. The remaining coordinate
theorem is the genuine sheaf/K-flat comparison and is not a restatement of the target.
I searched the local library and ran LeanFinder/Mathlib searches; no duplicate declaration
matching these project-specific statements was found. Edge cases n=0, empty/basic opens,
and zero quotient rings are addressed in the theorem docstrings.

4. **Pruning and route.** The item now uses the coordinate theorem, the restriction
certificate, the normalized cycle theorem, the conormal comparison, and the affine-section
map. The former direct import of `AffineQuotientResolutionSheafification` is removed from
the item because it is used by the coordinate module where its proof is needed. The old
Koszul base-change existential is not imported by the cycle proof; its required normalized
construction is proved privately. No unit statement or unit step is bypassed: the DAG unit
record remains unchanged.

5. **DAG and report consistency.** I checked that each delivered node's `lean` record,
`proof`, `proof_deps`, and `proof_origin` match the code's imports and applications. The
remaining hole and all four new nodes are listed in `Proved and sorry left` and `New nodes`.
I corrected the review wording to make the removed direct dependency and the strict
coordinate reduction explicit; no code or existing statement required repair.
