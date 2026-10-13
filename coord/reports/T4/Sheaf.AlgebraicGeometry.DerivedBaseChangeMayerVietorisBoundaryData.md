## What changed

Repaired reviewer X-ea877 C1/C4: the remaining canonical pullback lemma now
explains all three K-injectivity hypotheses before using the termwise-split SES
theorem. Its docstring identifies the fixed resolution, preservation under exact
open restriction and its right adjoint, and preservation under finite biproducts
by additivity of Hom from acyclic complexes. Its DAG proof records the same
argument and adds `lem-sc-derived-k-injective-restrict-open` and
`lem-weil-pbc-right-adjoint-preserves-kinjective` to step 1 and `proof_deps`.
This repair changes no Lean statement, definition, proof term, or hole count.

Repaired X-62c4d E1/E2 in the sandbox. Replaced the false arbitrary-boundary and
arbitrary-shift equation interface by the actual SES boundaries and fixed
adjunction-mate shifts. Added their real construction in
`Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalData`.
The boundary uses the fixed functorial K-injective resolution, its concrete
Mayer--Vietoris SES, and the explicitly constructed open-image comparisons
normalized to the pinned adjunctions. No object or morphism is selected from
mere existence of distinguished triangles.

Proved the shift compatibility of the pinned adjunction's unit and counit,
the explicit Hom-equivalence shift identity, and triangulatedness. The source
shift composes the existing direct-image shift with that unique pullback shift;
the target shift is the existing right-derived one. The distinguishedness proof
identifies all three arrows of the concrete SES triangle using fixed comparisons,
not existential presentation isomorphisms. Inverse-image cover distinguishedness
uses the same construction, with overlap equality transported explicitly.

Proved the generic base-change shift step in
`Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalShift` from
`exists_pinned_base_change_mate_shifts`. Its counit-compatible shifts are equal
to our shifts by `pinnedDerivedAdjunction_commShift` and
`compatibilityUnit_unique_left`. Naturality, the shift equation and functor
composition identities give the full generic formula for every degree n.

Split off the remaining cover pullback boundary equation on X' into
`Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalPullback`.
This is strictly a part of the old calculation: it has no f, f', S, S', subsequent
direct image, or comparison on S'. The assigned module combines the generic
shift step with this cover boundary step using two rewrites, map_comp and
associativity. This is real Lean glue, not an application of a restatement.

Forced-adapted only the proof of
`Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary`; all existing
signatures and visibilities there stay identical. It takes the actual canonical
witnesses and their four distinguishedness properties, then uses the repaired
equation. Change record: `coord/changes/mvBoundaryCanonicalSESShifts.md`.
Updated the data, equation and consumer proof records; the equation's
`lean.statement`, natural-language statement and full statement_change describe
the corrected canonical interface.

Removed the duplicate private mv_mate_naturality theorem. The restriction comparison now follows directly from NatTrans.naturality of the explicitly assembled mate transformation. No other library module is adapted.

## Proved and sorry left

Original module has two holes; both are removed from its delivered source:

- `AlgebraicGeometry.mvBoundary_data`
  (`lem-pc-rf-mv-base-change-connecting-square-data`): original signature preserved,
  fully proved from existing construction and comparison lemmas.
- `AlgebraicGeometry.mvBoundary_equation`
  (`lem-pc-rf-mv-base-change-connecting-square-equation`): false interface corrected,
  then reduced by a complete Lean proof to the proved generic base-change shift
  step and the strictly smaller cover pullback boundary step.

One new hole remains:

- `AlgebraicGeometry.mvCanonicalBoundary_pullback`
  (`lem-pc-rf-mv-canonical-boundary-pullback`), in its own new module, with proof
  exactly `:= by sorry`, source and complete natural-language proof.

All new canonical definitions and theorems, including
`mvCanonicalBaseChange_shift`, `mvCanonicalPullbackShift_compatible`,
`mvCanonicalHomEquiv_shift`, `mvCanonicalPullbackShift_triangulated` and
`mvBoundary_canonical_data`, have no local sorry. Every private helper is proved.
The consumer theorem remains proved. This is one unchanged-statement proof and
one corrected-statement decomposition: two upper holes closed, one lower hole
added, net one hole removed. The false statement is not claimed to be proved.
Existing project dependencies retain their independent obligations; no claim
of complete target axiom closure is made.

Edge cases: empty or repeated opens use the same SES. Equality induction
identifies an inverse-image overlap with the intersection; its proof is
irrelevant. Zero objects and zero morphisms satisfy the same chain-map equation.
The shift formula covers n=0, n=1 and all other integers, with the zero/addition
coherence inherited from the mate construction. A (-1)^n twist of only one
pullback shift fails the pinned adjunction compatibility; uniqueness proves it
cannot replace the chosen structure. The cover lemma is stated before applying
any f' direct image and depends on actual SES naturality, not completion of two
squares in an abstract triangulated category.

## No longer needed

Removed direct imports from the original assigned module:

- `Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial`;
- `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`;
- `Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation`;
- `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh`.

The data proof no longer invokes
`lem-pc-kinjective-mayer-vietoris-presentation` or
`lem-pc-derived-mayer-vietoris-functorial`: it uses the concrete exact sequence
and explicit unit/restriction comparisons. The equation proof no longer invokes
`lem-pc-derived-mayer-vietoris-functorial`,
`lem-pc-kinjective-mayer-vietoris-presentation`,
`lem-pc-derived-direct-image-composition`, or
`lem-pc-ringed-spaces-derived-pullback-composition` directly. It uses the two
canonical compatibility steps instead. The new lower cover lemma still needs
composition mate identities, and the generic shift proof takes the tensor-pullback
additivity witnesses from the composition theorem, so that last node remains needed
in both lower nodes.

The direct imports of right-derived triangulated instances and the injective
resolution were also removed from the returned sandbox's assigned module;
CanonicalData publicly supplies the needed constructions and instances.
The old public Maps import remains publicly exported through the new canonical
module. Some removed direct imports are still reachable transitively through
Maps and existing canonical data; no global unreachability of those modules
is claimed. No unit statement or realized step is bypassed:
`dag/units/sk-thm-picard-semicon.json` has empty realized lists.

## Where the brief, the DAG or earlier work was wrong

The returned delivery correctly identified the sign-twist counterexample but
retained the false sorry theorem, so it did not repair the interface. The original
existential data theorem did not specify which boundaries or shifts its witnesses
were, and hT/hT' did not normalize either shift. Image distinguishedness alone
was also insufficient to establish compatibility of the selected adjunctions.
This repair constructs the SES boundary and adjoint shifts, proves their
compatibility explicitly, and uses exactly the same choices in both the canonical
data theorem and corrected equation.

The equation's old Lean statement was stronger than its canonical mathematical
intent. The source counit/base-change construction is fixed, and the SES boundary
is transported with its derived-functor shift. Sources read:
[Stacks 08BV](https://stacks.math.columbia.edu/tag/08BV),
[Stacks 08HY](https://stacks.math.columbia.edu/tag/08HY), and
[Stacks 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9).

## New nodes

`def-pc-rf-mv-canonical-ses-shifts`: actual fixed SES boundary construction,
normalized open comparison, adjunction-compatible shifts, and their proved
compatibility and triangulatedness. Module
`Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalData`.

`lem-pc-rf-mv-canonical-base-change-shift`: proved generic naturality/shift equation
of the pinned base-change map, with no cover or SES. Module
`Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalShift`.

`lem-pc-rf-mv-canonical-boundary-pullback`: remaining SES boundary naturality on X'
before any subsequent direct image; one named sorry. Module
`Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalPullback`.

Change record: `coord/changes/mvBoundaryCanonicalSESShifts.md`.

## Statement corrected

`lem-pc-rf-mv-base-change-connecting-square-equation`: removed universal arbitrary
boundary/shift parameters and the two distinguishedness hypotheses. The corrected
statement uses the concrete fixed SES boundaries and compatible adjunction-mate
shifts. The old statement is preserved verbatim in statement_change and the change
record. The sole citing node `lem-pc-rf-mv-base-change-connecting-square` holds:
its unchanged existential theorem uses these same choices in its adapted proof.

## Forced adaptations

`Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary` is unclaimed.
Original against the changed dependency fails at line 121:

```text
error: Function expected at
  mvBoundary_equation f f' g g' hsq K K' U V hU hV hUV hcover hK hK' ψ
but this term has type [the equation for the specified canonical boundaries and shifts].
Expected a function because this term is being applied to the argument δ.
```

Only its final proof block changes. The old existential elimination of arbitrary
witnesses from mvBoundary_data is replaced with local names for the specified
canonical boundaries and the call of mvBoundary_canonical_data supplying their
four distinguishedness proofs. The existential constructor uses the two specified
shifts, and the final equation call drops the now-removed arbitrary data arguments.
Each line is necessary to match the corrected equation. The original theorem's
signature and visibility are unchanged, and its imports and docstring are unchanged.
The original fails against the delivered dependencies; the adapted module compiles.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered assigned module and forced adaptation with the repository
versions. Existing theorem signatures and visibility are preserved; the corrected
equation is documented by the change record and the consumer adaptation is forced.
Verdict: pass.

2. Compiled every delivered Lean module with `lcompile.py`. The assigned module and
canonical data and shift modules contain no `sorry`, forbidden declarations, or
hollow definitions. The sole remaining `sorry` is the named canonical pullback
boundary theorem and has its node and source documentation. Verdict: pass.

3. Checked the split-off canonical pullback statement against its hypotheses and
conclusion. It is a strict lower-level boundary naturality statement, omits later
direct images, and is not duplicated by an existing declaration. Verdict: pass.

4. Read the proofs from the target downward. The canonical SES construction and
shift compatibility are used, the equation reduces to the generic shift theorem
and the lower cover boundary theorem, and removed imports and old proof dependencies
are listed under No longer needed. The unit route is retained. Verdict: pass.

5. Compared the Lean declarations with their DAG records, including proof steps,
proof dependencies, proof origins, the corrected equation statement, and the new
pullback node. Verdict: pass.

Changed only the missing second-reading record; no Lean proof or statement changes
were needed during this review.

## Forced adaptations

### Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary
Original against changed dependencies failed:
```
/tmp/forced-adaptation-_exuehlc/lean/Sheaf/AlgebraicGeometry/DerivedBaseChangeMayerVietorisBoundary.lean:121:8: error: Function expected at
  mvBoundary_equation f f' g g' hsq K K' U V hU hV hUV hcover hK hK' ψ
but this term has type
  have δ := mvCanonicalBoundary X U V (U ⊓ V) ⋯ hcover K;
  have δ' := mvCanonicalBoundary X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V)) ⋯ ⋯ K';
  have csF := mvCanonicalSourceShift f g;
  have csG := mvCanonicalTargetShift f';
  (schemeDerivedDirectImage f ⋙ derivedPullback g).map δ ≫
      (Functor.commShiftIso (schemeDerivedDirectImage f ⋙ derivedPullback g) 1).hom.app K ≫
        (shiftFunctor (schemeDerivedCategory S') 1).map
          (schemeDerivedBaseChangeMap f f' g g' ⋯ K ≫ (schemeDerivedDirectImage f').map ψ) =
    mvBaseChangeOpenMap f f' g g' ⋯ K K' ψ (U ⊓ V) ≫
      (schemeDerivedDirectImage f').map δ' ≫ (Functor.commShiftIso (schemeDerivedDirectImage f') 1).hom.app K'

Note: Expected a function because this term is being applied to the argument
  δ

(with the modules compiled into /tmp/forced-adaptation-_exuehlc/.lbuild) [6.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Earlier second reading (a previous round; superseded)

1. Compared all five delivered modules with the repository sources. The byte-for-byte
   signatures of `mvBoundary_data` and `derivedBaseChange_mayerVietoris_connectingSquare`
   are identical. The only existing signature change is `mvBoundary_equation`, recorded
   in `mvBoundaryCanonicalSESShifts.md` and its node's `statement_change`. The old
   universally quantified independent shifts admit the sign twist described there;
   the correction fixes the concrete SES boundaries and adjunction-mate shifts while
   preserving every hypothesis of the consuming existential theorem. Whole-library
   search finds only this consumer. Its final proof is the sole forced adaptation;
   delivery's counterfactual compilation checks necessity. No target signature or
   existing public definition changes. Verdict: pass.

2. Compiled all five modules with `lcompile.py --all`. Inspected every definition and
   private helper: the resolution, comparisons, boundary and shifts are explicit
   constructions, and no data is chosen from a bare boundary-existence theorem.
   The generic shift proof selects only an additivity proof and eliminates a proved
   shift-existence theorem locally; its returned equality contains no chosen data.
   No forbidden axiom, unsafe declaration, opaque declaration, extern, implemented_by
   or hollow definition occurs. The only local sorry is `mvCanonicalBoundary_pullback`.
   A scratch axiom probe of all substantive public constructions and theorems shows
   only propext, Classical.choice and Quot.sound for the canonical data, distinguishedness,
   `mvBoundary_data` and `mvCanonicalBaseChange_shift`; only the pullback lemma, equation
   and consumer additionally depend on sorryAx. Verdict: pass, with the reported hole.

3. Read the pullback lemma and its natural-language proof against the fixed definitions.
   Its conclusion is on X', before Rf'_* and the outer base-change comparison; it is
   strictly one part of the equation, which combines it with the independently proved
   generic shift step. The target SES is degreewise split by injectivity of its first
   term, and all three terms are K-injective by exact open restriction, its right
   adjoint, and finite biproducts. Hence the termwise-split theorem's hypotheses are
   accounted for. Empty opens, U = V = top, zero objects and psi = 0 do not introduce
   exceptions; overlap equality is transported by equality induction. Independent
   LeanFinder search on connecting morphisms and derived pullback found no match;
   Loogle search for triangleOfSESδ found its naturality and exact-functor map lemmas,
   which do not identify this pinned derived overlap mate. Read the existing proved
   `schemeMV_directImage_boundary` and `schemeDerived_mayerVietoris_naturality`:
   the former concerns direct image with schemeMVAdjunction and schemeMVOpenComparison,
   the latter existentially packages adjunctions. Neither supplies the stated pinned
   pullback equation without a further mate/comparison identification. No quick closure
   or exact duplicate was found. Sources checked: [08BV](https://stacks.math.columbia.edu/tag/08BV)
   for the SES construction, [08HY](https://stacks.math.columbia.edu/tag/08HY) for the
   canonical counit base-change map, and [0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
   for the relative Mayer--Vietoris induction diagram. Verdict: pass as a decomposition.

4. Read downward from the unchanged consumer through the canonical data and equation.
   The equation uses generic shift compatibility, then the cover pullback boundary,
   then map_comp and associativity; it does not apply a renamed restatement.
   The data theorem identifies all three SES arrows, including the minus sign on the
   second restriction. All removed original proof dependencies are listed above;
   retained direct-image triangulatedness and composition dependencies are distinguished
   from removed direct imports. Public imports supply types or definition bodies;
   comparison and shift proof imports are plain imports. The pullback node's planned
   termwise-split theorem was missing from its import closure; added its module as a
   plain proof import so the remaining node has its stated proof dependency available.
   The unit sk-thm-picard-semicon has empty realized lists, so no realized route is
   bypassed. Verdict: pass after the import repair.

5. Read all six delivered nodes and checked their declarations, hypotheses, proof steps,
   origins and new-node metadata. Every proof_deps list equals the union of step uses,
   and every dependency names an existing node or one delivered here. The shift proof
   omitted its use of exists_derivedPullbackComposition for the additivity witnesses;
   added that use to its first step and proof_deps. The equation's corrected signature
   and sole citer are recorded; the data and consumer statements remain unchanged.
   The single new sorry has its own source, complete docstring proof and matching node.
   Verdict: pass after the dependency repair.

Second reading changed the missing plain termwise-split proof import, the generic
shift node's additivity dependency, and the stale mvBoundary_data docstring reference
from exists_derivedPullback to mvCanonicalPullbackShift_triangulated. Restored the
original spacing at mvBoundary_data's proof delimiter. No proof term, existing
statement, definition or hole count was changed by this second reading. The original
unchanged-statement hole mvBoundary_data is proved; the false old equation is corrected
and decomposed, not proved as originally stated. One new lower hole remains.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered modules with the repository versions. Existing signatures
are unchanged except for `mvBoundary_equation`; that correction is documented by the
change record and the node's `statement_change`. The consumer adaptation changes only
the forced proof block. Verdict: pass.

2. Compiled all delivered modules with `lcompile.py --all`. There are no forbidden
declarations or hollow definitions. The only remaining local `sorry` is the named
`mvCanonicalBoundary_pullback` theorem, with its node and proof docstring. Verdict: pass.

3. Checked the split-off pullback boundary theorem. It is a strict lower-level
boundary naturality statement before later direct images, and is not duplicated by
the library. Its hypotheses and conclusion match the fixed canonical constructions.
Verdict: pass as a decomposition.

4. Read the proof downward from the consumer. The canonical SES data, generic shift
calculation, and lower pullback boundary step are used; removed imports and proof
dependencies are recorded, and the unit route is retained. Verdict: pass.

5. Compared the DAG proof steps, dependencies, origins, statement correction, and
new-node metadata with the Lean declarations. They agree, including the one named
remaining hole. Verdict: pass.

Changed only this required second-reading heading and its concise verification record;
no Lean proof, definition, or statement was changed during this reading.

## Forced adaptations

### Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary
Original against changed dependencies failed:
```
/tmp/forced-adaptation-udgq2r8m/lean/Sheaf/AlgebraicGeometry/DerivedBaseChangeMayerVietorisBoundary.lean:121:8: error: Function expected at
  mvBoundary_equation f f' g g' hsq K K' U V hU hV hUV hcover hK hK' ψ
but this term has type
  have δ := mvCanonicalBoundary X U V (U ⊓ V) ⋯ hcover K;
  have δ' := mvCanonicalBoundary X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V)) ⋯ ⋯ K';
  have csF := mvCanonicalSourceShift f g;
  have csG := mvCanonicalTargetShift f';
  (schemeDerivedDirectImage f ⋙ derivedPullback g).map δ ≫
      (Functor.commShiftIso (schemeDerivedDirectImage f ⋙ derivedPullback g) 1).hom.app K ≫
        (shiftFunctor (schemeDerivedCategory S') 1).map
          (schemeDerivedBaseChangeMap f f' g g' ⋯ K ≫ (schemeDerivedDirectImage f').map ψ) =
    mvBaseChangeOpenMap f f' g g' ⋯ K K' ψ (U ⊓ V) ≫
      (schemeDerivedDirectImage f').map δ' ≫ (Functor.commShiftIso (schemeDerivedDirectImage f') 1).hom.app K'

Note: Expected a function because this term is being applied to the argument
  δ

(with the modules compiled into /tmp/forced-adaptation-udgq2r8m/.lbuild) [6.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.


## Forced adaptations

### Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary
Original against changed dependencies failed:
```
/tmp/forced-adaptation-nrpy090e/lean/Sheaf/AlgebraicGeometry/DerivedBaseChangeMayerVietorisBoundary.lean:121:8: error: Function expected at
  mvBoundary_equation f f' g g' hsq K K' U V hU hV hUV hcover hK hK' ψ
but this term has type
  have δ := mvCanonicalBoundary X U V (U ⊓ V) ⋯ hcover K;
  have δ' := mvCanonicalBoundary X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V)) ⋯ ⋯ K';
  have csF := mvCanonicalSourceShift f g;
  have csG := mvCanonicalTargetShift f';
  (schemeDerivedDirectImage f ⋙ derivedPullback g).map δ ≫
      (Functor.commShiftIso (schemeDerivedDirectImage f ⋙ derivedPullback g) 1).hom.app K ≫
        (shiftFunctor (schemeDerivedCategory S') 1).map
          (schemeDerivedBaseChangeMap f f' g g' ⋯ K ≫ (schemeDerivedDirectImage f').map ψ) =
    mvBaseChangeOpenMap f f' g g' ⋯ K K' ψ (U ⊓ V) ≫
      (schemeDerivedDirectImage f').map δ' ≫ (Functor.commShiftIso (schemeDerivedDirectImage f') 1).hom.app K'

Note: Expected a function because this term is being applied to the argument
  δ

(with the modules compiled into /tmp/forced-adaptation-nrpy090e/.lbuild) [6.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by T4

1. Compared all five delivered modules with the repository using diff and parsed
   raw declaration headers. The existing signatures of mvBoundary_data and
   derivedBaseChange_mayerVietoris_connectingSquare are byte-for-byte identical.
   Only mvBoundary_equation changes its signature; the complete correction is
   recorded in mvBoundaryCanonicalSESShifts.md and statement_change. Its old
   independent shifts admit the sign-twist counterexample. The sole consumer
   changes only its necessary final proof block. No target or existing definition
   changes. Verdict: pass as a documented intermediate-statement repair.

2. Compiled all five modules in import order with lcompile.py --all, without errors
   or warnings. Independently compiled the scratch BoundaryReviewAxioms probe.
   Canonical comparisons, SES boundaries, shift constructions, compatibility,
   triangulatedness, mvBoundary_canonical_data, mvBoundary_data, and the generic
   shift theorem use only propext, Classical.choice and Quot.sound. Only the
   pullback boundary lemma, equation and consumer additionally use sorryAx.
   Inspected definitions: there is no arbitrary boundary witness, hollow data,
   forbidden declaration, or hidden sorry. The only local hole is the reported
   mvCanonicalBoundary_pullback. Verdict: pass with that named remaining hole.

3. Read the pullback lemma, docstring and node against the actual fixed
   constructions. It asserts boundary naturality on X' before any further direct
   image, so it is strictly smaller than the assigned equation. The target SES
   splits degreewise by injectivity of its first term; restriction, its exact
   left adjoint's right adjoint, and finite biproducts account for K-injectivity
   of all terms required by the termwise-split comparison. Empty opens, repeated
   opens, zero objects and zero psi require no excluded hypotheses. Checked
   Stacks 08BV, 08HY and 0DJ9 directly. Independent LeanFinder, Loogle and grep
   searches found SES naturality and exact-functor image lemmas but no theorem
   identifying this pinned pullback overlap mate. Read schemeMV_directImage_boundary
   and schemeDerived_mayerVietoris_naturality: their comparisons/adjunctions differ,
   and using them still requires the missing mate identification. No quick closure
   was found. Verdict: pass as one sourced decomposition obligation.

4. Read downward from the unchanged consumer. The data proof constructs a triangle
   isomorphism and checks its three arrows, including the negative second
   restriction. The equation genuinely combines the independently proved generic
   shift calculation with the pullback lemma and functor composition. Imports
   needed only for these proofs are plain imports. The four removed direct imports
   and all removed old proof_deps are already listed under No longer needed.
   No global module pruning is claimed because imports remain transitively reached.
   sk-thm-picard-semicon has empty realized statement and step lists, so no realized
   unit route is bypassed. Verdict: pass.

5. Checked the six changed/new node records against their Lean declarations and
   proof steps, including the statement-change record, sources, search metadata,
   origins and creation fields. Every proof_deps equals the union of step uses;
   every dependency exists in the repository or this delivery. The extra unchanged
   comparison-node copy contributes no delivered change. The remaining hole has
   its own module, named theorem, source, complete docstring argument and node.
   Verdict: pass.

This second reading changed only the required review record; no Lean proof,
statement, definition, import or hole count required another repair. One of the
original two statements, mvBoundary_data, is proved unchanged. The false old
mvBoundary_equation is corrected and decomposed, not proved as originally stated;
one lower hole is added. This is not a claim of two unchanged statements proved.

## Forced adaptations

### Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary
Original against changed dependencies failed:
```
/tmp/forced-adaptation-3xlw5dbu/lean/Sheaf/AlgebraicGeometry/DerivedBaseChangeMayerVietorisBoundary.lean:121:8: error: Function expected at
  mvBoundary_equation f f' g g' hsq K K' U V hU hV hUV hcover hK hK' ψ
but this term has type
  have δ := mvCanonicalBoundary X U V (U ⊓ V) ⋯ hcover K;
  have δ' := mvCanonicalBoundary X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V)) ⋯ ⋯ K';
  have csF := mvCanonicalSourceShift f g;
  have csG := mvCanonicalTargetShift f';
  (schemeDerivedDirectImage f ⋙ derivedPullback g).map δ ≫
      (Functor.commShiftIso (schemeDerivedDirectImage f ⋙ derivedPullback g) 1).hom.app K ≫
        (shiftFunctor (schemeDerivedCategory S') 1).map
          (schemeDerivedBaseChangeMap f f' g g' ⋯ K ≫ (schemeDerivedDirectImage f').map ψ) =
    mvBaseChangeOpenMap f f' g g' ⋯ K K' ψ (U ⊓ V) ≫
      (schemeDerivedDirectImage f').map δ' ≫ (Functor.commShiftIso (schemeDerivedDirectImage f') 1).hom.app K'

Note: Expected a function because this term is being applied to the argument
  δ

(with the modules compiled into /tmp/forced-adaptation-3xlw5dbu/.lbuild) [6.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
