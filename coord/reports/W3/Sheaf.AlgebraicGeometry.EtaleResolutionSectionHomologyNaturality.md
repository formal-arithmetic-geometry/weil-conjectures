## What changed

Repaired `AlgebraicGeometry.Etale.resolutionSection_homology_naturality`: the old
statement applied naturality to arbitrary equivalences. It now takes two comparison
families specified on cocycles by `InjectiveResolution.extMk` and the independently
constructed `etaleOpenObjectCohomologyMap`. The specification is a real structure,
with no chosen data and no compatibility identities in its fields.

The proof imports `EtaleResolutionSectionCanonicalRestriction` and
`EtaleResolutionSectionCanonicalTransfer`. Applying the first lemma on X and Y
and the second to the augmentation-preserving map gives the six conjuncts.
The single-scheme construction is in `EtaleResolutionSectionCanonicalData`.

The sole user `EtaleResolutionSectionHomology` is adapted only in its proof and its
construction import. Its full existential statement and visibility are unchanged.
All six delivered modules compile without warnings. The scratchpad preserves a
construction attempt: the generic represented Hom-complex isomorphism and the
isomorphism commuting evaluation with extension from naturals to integers compile.
The resulting Ext-to-section homology isomorphism also compiles. Its normalization
on `extMk` remains an unsolved scratch goal, so none of that experiment is delivered. The old caller demonstrably
fails against the new interface; the adapted caller compiles.

Change record: `coord/changes/resolutionSection_homology_naturality-canonical.md`.
The node records include the statement correction and every affected citer.

## Proved and sorry left

The corrected `AlgebraicGeometry.Etale.resolutionSection_homology_naturality`
contains a complete proof combining two strictly smaller naturality obligations.
Its original hole is retired by a documented statement repair, not counted as a
proof of the old false universal assertion. The unchanged
`AlgebraicGeometry.Etale.exists_resolutionSection_homology_comparison` is again
proved by constructing normalized witnesses and invoking the corrected theorem.

Three added holes, each exactly `:= by sorry` in its own module, with source,
complete proof in words, and matching DAG node:

- `AlgebraicGeometry.Etale.exists_resolutionSection_canonical_comparison`
  (`lem-weil-pbc-etale-resolution-section-canonical-data`): one resolution on one
  scheme; no scheme morphism, comparison lift, or naturality conclusion.
- `AlgebraicGeometry.Etale.resolutionSection_canonical_restriction`
  (`lem-weil-pbc-etale-resolution-section-canonical-restriction`): only the two
  restriction identities for one already normalized family.
- `AlgebraicGeometry.Etale.resolutionSection_canonical_transfer`
  (`lem-weil-pbc-etale-resolution-section-canonical-transfer`): only the two
  transfer identities for already normalized families and the prescribed lift.

No sorry remains in the item or its adapted caller. No hole is in a definition.
This is a repair plus decomposition, not a net proof-progress claim. The old
`exists_resolutionSection_homology_data` remains unchanged outside the delivery,
but its module is pruned from this branch of the targets' import closure.

## No longer needed

Removed the proof-only `Sheaf.AlgebraicGeometry.EtaleResolutionSectionHomologyData`
import from the forced caller and from the refreshed baseline of the item. Removed
the item's redundant proof-only
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance` import;
its cohomology-map definitions remain available through the existing statement imports. Its node
`lem-weil-pbc-etale-resolution-section-homology-data` and module are no longer
needed by this argument: mere existence of arbitrary equivalences supplies no
normalization. The naturality node also drops that node from its proof dependencies.

The baseline was refreshed during the dry runs: it added the two proof-dependency
imports just listed, and C2 proved the old unnormalized data theorem. That theorem
still gives no cocycle normalization, so it cannot supply the new construction
contract. The item's existing public imports remain because its statement uses
injective resolutions and section transfer.
The new canonical comparison module is public because the corrected statement uses
its structure; the two naturality lemmas are proof-only imports.
No unit-level statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old statement): naturality is not a property of four arbitrary
additive equivalences. For the identity restriction/transfer on a nonzero degree-zero
integer-valued section, replacing only the target equivalence by its negative turns
one side into its negative and leaves the other side unchanged. Both choices cannot
commute: that would force every image to satisfy a = -a. A nonempty field spectrum
with constant lifted integers supplies degree-zero sections with 1 ≠ -1. This is
an elementary mathematical counterexample; no full scheme-level Lean refutation is
claimed. The source constructs specific comparisons, not arbitrary ones.

The preceding data theorem only asserts existence; its statement does not promise
that its witnesses are the canonical comparisons. Its docstring cannot be used as a
missing hypothesis. Replacing it by normalized single-scheme data fixes the caller
without weakening its existential conclusion. The previous seven-minute attempt
reported the issue but left no compiling repaired reduction; this delivery does.

The Stacks 0A50 proof supplies the section-complex computation but does not explicitly
state the six pullback identities. Their cocycle argument is expanded here from the
parent docstring, localization in 03F3, and resolution functoriality in 01F8/01FB.
Tag pages were read; the local Stacks tex is absent on this machine. Mathlib searches
were actually run and logged. LeanSearch returned HTTP 500 and is recorded as
unavailable; Lean Finder and Loogle found `extMk` and the Ext/cocycle comparison.
Repository searches found no existing theorem supplying normalized comparisons for
arbitrary prescribed resolutions with these six identities.

## New nodes

`def-weil-pbc-etale-resolution-section-canonical-comparison` defines the comparison
families by their values on representing cocycles. Its structure uses only existing
actual maps, and none of the six desired naturality identities occurs in it.

`lem-weil-pbc-etale-resolution-section-canonical-data` constructs this structure on a
single scheme by the Hom-to-sections complex comparison and the bijective canonical
open-object map. It is strictly the construction part of the parent's argument.

`lem-weil-pbc-etale-resolution-section-canonical-restriction` handles the two
restriction families on a single scheme, using the cocycle normalization.

`lem-weil-pbc-etale-resolution-section-canonical-transfer` handles only global and
open transfer for the prescribed augmentation-preserving lift.

All four are below the same `sk-thm-p1` unit, with actual searches and explicit
proofs in words. The parent naturality and existential comparison nodes are updated
to match the corrected route. Change record:
`coord/changes/resolutionSection_homology_naturality-canonical.md`.

## Forced adaptations

`Sheaf.AlgebraicGeometry.EtaleResolutionSectionHomology` (unclaimed).
The original compiles against the baseline but, against the delivered interface,
produces at its line 109:

```
error: Application type mismatch: The argument eX has type
  (q : ℕ) → section homology q ≃+ G.H q
but is expected to have type
  ResolutionSectionCanonicalComparison G I
in the application resolutionSection_homology_naturality g G I J α hα eX
```

Only import line 11 and the final six proof lines change. The new import is needed
to construct normalized witnesses. The final lines obtain cX and cY from the
single-scheme construction, use their four equivalence fields as existential
witnesses, and apply naturality to cX and cY. Every original declaration signature
and visibility is identical; no public helper is added. Both compiler directions
are checked again by deliver3.py and independently by the second reader.

## Second reading by W3

I reread the delivered Lean files
`EtaleResolutionSectionCanonicalComparison.lean`,
`EtaleResolutionSectionCanonicalRestriction.lean`,
`EtaleResolutionSectionCanonicalTransfer.lean`,
`EtaleResolutionSectionHomologyNaturality.lean`, and the adapted
`EtaleResolutionSectionHomology.lean`. I also reread the copied DAG passages for
`def-weil-pbc-etale-resolution-section-canonical-comparison`,
`lem-weil-pbc-etale-resolution-section-canonical-data`,
`lem-weil-pbc-etale-resolution-section-canonical-restriction`,
`lem-weil-pbc-etale-resolution-section-canonical-transfer`, and the parent
naturality node. For the cited mathematics I checked the resolution-section
construction in Stacks Tag 0A50, localization and the object-cohomology map in
Tag 03F3 (especially part (2)), and the resolution functoriality calculation in
Tags 01F8 and 01FB. These are the passages used by the docstrings, rather than
only a signature or a compiler check.

1. The normalization in the structure is exactly the one used by the proof. A
`global_cocycle` field starts with a closed map `f` from the constant sheaf
`ULift ℤ` into `I.cocomplex.X q`, with `hf : f ≫ d q (q+1) = 0`, and identifies a
section cycle `z` whose `iCycles` representative is the constant-sheaf
adjunction image of `f`; it requires `globalEquiv` of `homologyπ z` to be
`I.extMk f (q+1) rfl hf`. The `open_cocycle` field has the same shape with the
free sheaf of the etale object `W`, its sections adjunction, and
`etaleOpenObjectCohomologyMap G q W` applied to the same `I.extMk`. Thus the
proof uses the node's normalization verbatim; it does not silently replace
these fields by an arbitrary equivalence or by a cocycle only up to an
unspecified isomorphism.

2. Every section-homology class has the required representing closed Hom
cocycle. The section/free-sheaf adjunction turns a degree-q section into a map
from the constant sheaf (for the terminal object) or the free representable
sheaf (for `W`) into `I.cocomplex.X q`. The section cycle equation is exactly
that this map composed with `I.cocomplex.d q (q+1)` is zero, so it supplies the
`hf` required by `global_cocycle` or `open_cocycle`; changing the representative
by a boundary changes `extMk` by the corresponding Ext boundary. The argument
uses the epimorphism `homologyπ q`, so it covers all homology classes. For
`q = 0` the same equation is the degree-zero cocycle equation (there is no
special negative-degree assumption); for the zero sheaf both sides are the
singleton group and the same representative argument is vacuous.

3. I checked the two restriction identities against the actual maps in the
statement. Whole-to-open restriction is the section map for
`W.ι`; under the representing free sheaf it precomposes with the identity
arrow, and the resulting Ext class is exactly `cohomologyMap W.ι G q`. For
`A ≤ B`, restriction is the map induced by `X.homOfLE h`; composing the two
inverse-image comparison isomorphisms gives the coefficient transport used by
`openCohomologyRestriction h G q`. The canonical restriction theorem applies
these calculations to the normalized `global_cocycle` and `open_cocycle`
fields, yielding precisely the first two conjuncts (and, after replacing
`X,G,I` by `Y,upperStar g.obj G,J`, the third and fourth), including the
identity and empty-open cases.

4. I separately checked the two transfer identities, including their
coefficient transports. Adjunction sends `α` to the inverse-image chain map;
`hα` says that it preserves the augmentation. On the terminal object,
evaluation of the pulled-back closed Hom cocycle is `α` followed by
`terminalSectionPullback g`, and the normalized Ext class is the displayed
`cohomologyMap g G q`. On `W`, the same free-representable calculation uses
`openSectionPullback g W`; the coefficient map is the upper-star comparison
for `g ⁻¹ᵁ W`, which is exactly the transport built into
`openCohomologyPullback g W G q`. Applying `global_cocycle` and `open_cocycle`
for `cX` and `cY`, then surjectivity of `homologyπ`, gives the fifth and sixth
conjuncts. This also checks the identity-map and zero-sheaf cases: the
transport is the identity and all equations reduce to the corresponding
restriction/transfer identity.

5. Finally I checked the empty-open case directly: the free representable and
its section group are zero, so both the open homology class and the transported
cohomology class are zero. For the identity scheme morphism, arbitrary prescribed resolutions and augmentation-preserving α need not give identity chain maps. After the canonical coefficient identifications, the induced homology transfers represent identity cohomology maps, by the cocycle calculation and independence of augmentation-preserving comparison lifts up to homotopy. These edge checks
agree with the four restriction and two transfer formulas and with the
canonical-comparison fields. The Lean declarations compile with only the three
named split-off theorem sorries, and the signatures and visibility of the
adapted existing module remain unchanged.

## Forced adaptations

### Sheaf.AlgebraicGeometry.EtaleResolutionSectionHomology
Original against changed dependencies failed:
```
/tmp/forced-adaptation-439gn86u/lean/Sheaf/AlgebraicGeometry/EtaleResolutionSectionHomology.lean:109:59: error: Application type mismatch: The argument
  eX
has type
  (q : ℕ) →
    ↑((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex (ComplexShape.up ℕ)).obj
              I.cocomplex).homology
          q) ≃+
      G.H q
but is expected to have type
  ResolutionSectionCanonicalComparison G I
in the application
  resolutionSection_homology_naturality g G I J α hα eX

(with the modules compiled into /tmp/forced-adaptation-439gn86u/.lbuild) [11.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Mechanical refresh

1. I compared every delivered module with the repository baseline. Existing declaration signatures are unchanged except for the documented repair of `resolutionSection_homology_naturality`; the adapted caller keeps its original theorem statement and visibility. The change record names the interface repair and forced caller adaptation.

2. I compiled the naturality module, the adapted homology caller, and all three canonical split modules with `lcompile.py`; all compile cleanly. The only remaining `sorry`s are the three named split-off theorems, each a standalone theorem with a docstring and matching DAG node. No definitions contain `sorry`, and no forbidden declarations occur.

3. The corrected normalized-comparison statement and the three split statements are true and strictly smaller than the parent: construction, restriction, and transfer are separated, while the old arbitrary-equivalence assertion is explicitly disputed. Repository searches found no duplicate declarations.

4. The proof follows the shortest available route through the canonical restriction and transfer lemmas, and the caller constructs normalized witnesses from the single-scheme data theorem. The redundant proof-only imports and old unnormalized data dependency were removed as reported; the unit route remains unchanged.

5. The DAG proof steps, dependencies, origins, Lean records, and new-node metadata match the delivered Lean declarations. The refreshed report and change record document the statement repair, decomposition, and forced adaptation.

Changed during this second reading: no Lean proof or statement changes were needed; I added this verification section and then ran the delivery dry run.

## Forced adaptations

### Sheaf.AlgebraicGeometry.EtaleResolutionSectionHomology
Original against changed dependencies failed:
```
/tmp/forced-adaptation-c68kkk_4/lean/Sheaf/AlgebraicGeometry/EtaleResolutionSectionHomology.lean:109:59: error: Application type mismatch: The argument
  eX
has type
  (q : ℕ) →
    ↑((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex (ComplexShape.up ℕ)).obj
              I.cocomplex).homology
          q) ≃+
      G.H q
but is expected to have type
  ResolutionSectionCanonicalComparison G I
in the application
  resolutionSection_homology_naturality g G I J α hα eX

(with the modules compiled into /tmp/forced-adaptation-c68kkk_4/.lbuild) [13.3 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Forced adaptations

### Sheaf.AlgebraicGeometry.EtaleResolutionSectionHomology
Original against changed dependencies failed:
```
/tmp/forced-adaptation-132jwmmn/lean/Sheaf/AlgebraicGeometry/EtaleResolutionSectionHomology.lean:109:59: error: Application type mismatch: The argument
  eX
has type
  (q : ℕ) →
    ↑((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex (ComplexShape.up ℕ)).obj
              I.cocomplex).homology
          q) ≃+
      G.H q
but is expected to have type
  ResolutionSectionCanonicalComparison G I
in the application
  resolutionSection_homology_naturality g G I J α hα eX

(with the modules compiled into /tmp/forced-adaptation-132jwmmn/.lbuild) [11.2 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
