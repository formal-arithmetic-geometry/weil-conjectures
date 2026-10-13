## What changed

Replaced the duplicate private counit proof with the existing
`AlgebraicGeometry.SingleComplexBaseChange.counit_isIso_kFlat` theorem from
`IsomorphismPullbackCounit`. Proved the original declaration from the residual comparison-square theorem and a
proved generic representative-data lemma. The latter constructs the literal restriction,
its K-flatness certificate, its invertible specified pullback counit, and its derived
identification using adjoint uniqueness and the inverse specified open pullback counit. The shared counit theorem compares the two universal counits by the unique
invertible left-derived lift; this delivery contains no private counit helper. The data construction is not delegated to an existence hole.
Added proof-only imports of `OpenRestrictedComparisonCore` and
`OpenRestrictedRepresentativeData`; the original theorem has a definitionally equal statement. Its inline β is
now the fully typed `openRestrictedCompositionMap`, whose body is exactly the
three original morphism factors. Added its statement-level public import.
This repairs repeated large inference: the main module compiled in 10.5 seconds.
The original file with its sorry compiled in 58.9 seconds.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.SingleComplexBaseChange.exists_open_restricted_comparison_transport`.
The delivery adds one hole:
`AlgebraicGeometry.SingleComplexBaseChange.exists_open_restricted_comparison_square`
(node `lem-pc-open-restricted-comparison-core`). This is a decomposition, not a claim of
an unconditional proof: one upper hole is replaced by one strictly smaller square hole.
The generic theorem
`AlgebraicGeometry.SingleComplexBaseChange.exists_open_restricted_representative_data`
(node `lem-pc-open-restricted-representative-data`) has a
complete proof and contain no sorry. There are no sorries left in the item module.

## No longer needed

No original import, node, or planned module is pruned. The original direct
proof dependencies are now reached through the supporting nodes:
`lem-pc-ringed-spaces-derived-pullback-composition`,
`lem-pc-open-restriction-stalk-extension-iso`, `lem-pc-kflat-open-restriction`,
`def-pc-derived-pullback`, `def-pc-base-derived-tensor-cohomology-model`, and
`lem-weil-pbc-module-stalk-pullback`. All remain in the argument; none is claimed
as pruned. The new composition module imports only `DerivedPullbackComposition`,
and the new representative-data module imports `SingleComplexBaseChangeStalkCondition`
in place of the unnecessary `StalkComparisonPullbackNaturality` import. The exploratory import of
`SingleComplexOpenRestrictionData` is unnecessary: the counit directly constructs eQ. The original dependencies are
still needed either by the square argument or by the explicit representative construction.
No dependency is claimed to be unnecessary merely because it is now below a new node.

## Where the brief, the DAG or earlier work was wrong

The previous delivery duplicated a theorem already provided by
`IsomorphismPullbackCounit`; this repair imports and uses that declaration. No mathematical error found. The second reader corrected the new helper citations: exact open restriction is in Stacks Tag 0D5U, whereas Tag 08DW concerns quasi-coherent derived pullback; composition is Tag 0D5S. The required second reading is recorded below. After the metadata checks passed, the dry-run
tool accepted this pending independent reading and printed OK; nothing was pushed. The original plan separates exact restriction,
representative data, and stalk/tensor commutativity. This delivery implements the
representative-data part and leaves the commutativity part as a named theorem.
The restriction functor requires its source and target module categories to be explicitly
typed in the derived construction, so that Lean uses the specified derived category
instances rather than attempting new instance searches through `Scheme.Modules`.
Edge cases: empty opens have no z for the square; the data lemma does not require z
and remains valid on empty opens. Zero complexes and zero rings use the same exact
restriction and universal-counit argument. No flatness or boundedness is introduced.

## New nodes

`lem-pc-open-restricted-comparison-core`, in
`lean/Sheaf/AlgebraicGeometry/OpenRestrictedComparisonCore.lean`, isolates the
additive stalk isomorphism and commuting comparison square when hcQ and eQ are
supplied; it omits their existence and Q's K-flatness assertion. Its proof documentation
retains the original Stacks locality argument and representative naturality for arbitrary
eQ. It is the only new hole.

`lem-pc-open-restricted-representative-data`, in
`lean/Sheaf/AlgebraicGeometry/OpenRestrictedRepresentativeData.lean`, is the proved
construction of the K-flat literal restriction, counit certificate along any q into U,
and derived identification. It needs no square, stalk point, f, f′, g or g′. It realizes
the representative-construction part of the original node, without changing the unit route.
Added `def-pc-open-restricted-composition-map` in
`lean/Sheaf/AlgebraicGeometry/OpenRestrictedComparisonComposition.lean` to factor
the existing β expression with an explicit type. The definition has real data and
contains no sorry; it is definitionally the original inline composition.
Change record: `coord/changes/open-restricted-composition-factor.md`.

Validation: all four modules compile. The main module compiled in 10.5 seconds;
the composition definition in 24.8 seconds, the square statement in 7.4 seconds,
and the representative-data theorem in 18.6 seconds. The delivery tool’s compile
and axiom probes passed. Final dry run printed OK for commit 94d07ebd77, with the
second reading explicitly left to its reader; nothing was pushed. LeanSearch is unavailable (Internal Server Error); other search kinds
are recorded, and no absence verdict is attributed to the unavailable service.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered transport module with the repository version. The theorem's mathematical
   statement is unchanged; its β expression is factored through the new definition to keep the
   module below the delivery compile limit. This is the only interface-level textual change and
   is recorded by the delivery's new composition node. Verdict: pass.
2. Compiled the representative-data, comparison-core, composition, and transport modules with
   `lcompile.py`. The transport theorem has no sorry, axiom, unsafe, opaque, extern, or
   implemented_by declarations; the core remains the single named split-off theorem. Verdict: pass.
3. Read the split-off core statement and representative-data theorem against their uses and nodes.
   The core is strictly smaller than the transport target and the representative theorem is a
   concrete construction, with no hollow definition or arbitrary witness. Verdict: pass.
4. Checked the proof route and imports. The transport proof uses the core square and the concrete
   representative-data theorem; the composition definition is retained for the core's public
   statement and the transport theorem's factored β signature. No unnecessary
   original import or dependency was removed. Verdict: pass.
5. Checked the DAG records and unit route. The transport node's proof and proof_deps match the two
   supporting nodes, and the new nodes carry source, proof, search, Lean, chapter, and unit fields.
   Verdict: pass.

Changed during second reading: checked the interface-level β factoring and retained the typed
composition definition because restoring the repeated inline expression exceeded the 60-second
delivery compile limit. Added this second-reading report section.

## Forced adaptations

Sheaf.AlgebraicGeometry.OpenComparisonIntoPullbackTransport (unclaimed): the original compiles against the published library but fails against the delivered dependencies at line 201 with Type mismatch after simplification of congrArg (fun t ↦ l.hom ≫ t) hs. Replace the final simpa only list [Category.assoc, Iso.trans_hom] with [l, FU, HU, q, RQ, eR, β, openRestrictedCompositionMap, Category.assoc, Iso.trans_hom]. This unfolds the aliases and factored composition map needed to match the transported square. The adapted module compiles cleanly; signatures and visibility are unchanged.

## Earlier second reading (a previous round; superseded)

1. Compared all existing delivered modules with the repository using diff. The only
   signature edit is the declared β factoring in
   `exists_open_restricted_comparison_transport`, recorded in
   `coord/changes/open-restricted-composition-factor.md`. The definition contains
   the same three morphism factors verbatim, so the statement is definitionally
   equal to the original. All binders, hypotheses, conclusions, universes and
   visibility are unchanged. The adapted downstream module changes only its final
   simplification list. Verdict: pass.
2. Compiled the five modules through lcompile.py, in import order. Scanned every
   delivered Lean file for sorry and forbidden declarations; the sole sorry is
   `exists_open_restricted_comparison_square`. Explicit #print axioms probes give
   only propext, Classical.choice and Quot.sound for the composition definition
   and representative-data theorem. The square, transport and downstream transport
   additionally use sorryAx, as expected from the named square hole. The private
   counit helper is the proved universal-counit argument already present privately
   in SingleComplexBaseChangeStalkCondition. The definition and representative
   construction contain no arbitrary existence-witness data or sorry. Verdict: pass.
3. Read the core's quantified square and its natural-language proof against
   representative naturality and source transport. For a supplied eQ, its ratio
   with the canonical eQ is an automorphism of DQ(Q); source transport and
   comparisonIntoPullback_naturality transport the canonical square along that
   automorphism. Thus the extra universal quantifier does not assume invertibility
   of the comparison. Empty opens have no z, the top open gives the identity
   restriction case, and zero complexes give zero comparison sources and targets.
   The core omits constructing Q's K-flatness, hcQ and eQ; these are obtained by a
   separate fully proved construction. It is a strictly smaller residual argument,
   not a restatement of the target. Fresh leanfinder, loogle and grep queries and
   library/upstream searches found the underived restriction-stalk isomorphism,
   derived uniqueness and exact-functor factors, but no theorem supplying the full
   square. SingleComplexOpenRestrictionData supplies a functor comparison, not this
   square. The square cannot be closed by a short application of these results.
   Verdict: pass as a decomposition, with one closed hole and one added hole.
4. The proof first obtains η from the residual square, constructs the literal
   representative data and packages its witnesses. Narrowed the new helper imports:
   composition publicly imports DerivedPullbackComposition, and representative data
   publicly imports SingleComplexBaseChangeStalkCondition; neither needs to import
   StalkComparisonPullbackNaturality. Main/core statement imports and the two main
   proof-only imports are appropriate. Listed every original proof dependency now
   routed through supporting nodes under No longer needed; none is actually pruned.
   The unit sk-thm-picard-semicon has empty realized statement/step arrays, and this
   delivery changes neither the unit nor any chapter/unit route. Verdict: pass.
5. Checked all four node lean.statement fields against their declarations modulo
   whitespace, each proof_deps against the union of proof-step uses, the new-node
   source/search/created/blueprint/chapter/unit records, and the transport's reduction.
   Added the missing lem-pc-module-pullback-adjunction proof dependency to the
   representative node. Corrected exact-open restriction references to Stacks
   Tag 0D5U and the composition definition reference to Tag 0D5S. Verdict: pass.

Changed in this reading: narrowed the two new helper imports, corrected their
source references and the representative node's proof dependencies, added fresh
search records, and clarified the original dependencies in No longer needed.
No Lean proof or mathematical statement was rewritten. A scratch test unfolding
only openRestrictedCompositionMap in the downstream final simpa still failed at
line 201 with Type mismatch; retain the delivered local-alias unfolding list.
The delivery tool separately checks that the original downstream module compiles
against the baseline and fails against the changed dependencies.

## Forced adaptations

### Sheaf.AlgebraicGeometry.OpenComparisonIntoPullbackTransport
Original against changed dependencies failed:
```
duleCat.extendScalars
              (algebraMap
                (TensorProduct ↑(R f g' ((pullback.fst g' U.ι) z)) ↑(A g' ((pullback.fst g' U.ι) z))
                  ↑(B f' ((pullback.fst g' U.ι) z)))
                ↑(C ((pullback.fst g' U.ι) z)))).obj
          ((cohomologyModel f f' g g' sq ((pullback.fst g' U.ι) z) P).cohomology i)) ⟶
      (derivedPullback (pullback.fst g' U.ι) ⋙
            comparisonStalkCohomology (pullback g' U.ι) z i ⋙
              forget₂ (ModuleCat ↑((pullback g' U.ι).presheaf.stalk z)) AddCommGrpCat).obj
        ((derivedPullback g').obj K))
    ((Classical.choose ⋯).hom ≫
      (forget₂ (ModuleCat ↑((pullback g' U.ι).presheaf.stalk z)) AddCommGrpCat).map
          (comparisonIntoPullback (U.ι ≫ f) (pullback.fst g' U.ι ≫ f') g (pullback.snd g' U.ι) sqU z
            (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⋯ i) ≫
        (comparisonStalkCohomology (pullback g' U.ι) z i ⋙
              forget₂ (ModuleCat ↑((pullback g' U.ι).presheaf.stalk z)) AddCommGrpCat).map
          ((derivedPullback (pullback.snd g' U.ι)).map (Classical.choose ⋯).hom ≫ openRestrictedCompositionMap g' U K))
    (l.hom ≫
      n.hom ≫
        (forget₂ (ModuleCat ↑((pullback g' U.ι).presheaf.stalk z)) AddCommGrpCat).map
            (comparisonIntoPullback (U.ι ≫ f) (pullback.fst g' U.ι ≫ f') g (pullback.snd g' U.ι) sqU z Q hcQ i) ≫
          (comparisonStalkCohomology (pullback g' U.ι) z i ⋙
                forget₂ (ModuleCat ↑((pullback g' U.ι).presheaf.stalk z)) AddCommGrpCat).map
            ((derivedPullback (pullback.snd g' U.ι)).map eQ.hom ≫
              (Classical.choose ⋯ (pullback.snd g' U.ι) U.ι).hom.app K ≫
                eqToHom ⋯ ≫ (Classical.choose ⋯ (pullback.fst g' U.ι) g').inv.app K))

Note: The following definitions were not unfolded because their definition is not exposed:
  getLimitCone ↦ 32
  getColimitCocone ↦ 436

(with the modules compiled into /tmp/forced-adaptation-i2i0vybx/.lbuild) [31.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by F2

1. Compared both existing delivered modules with the read-only repository using diff.
   All existing binders, hypotheses, universes, conclusions and visibility are unchanged.
   The sole textual signature edit factors β through openRestrictedCompositionMap;
   its body is the original three morphism factors verbatim and the change record
   declares it. The downstream adaptation changes only its final simplification list.
   Verdict: pass, with the recorded definitionally equal interface presentation.
2. Compiled all five delivered modules in import order through lcompile.py: composition
   20.0 s, representative data 6.4 s, core 7.0 s, transport 9.4 s, downstream 36.4 s.
   Scanned every delivered Lean file: exactly one sorry, in the named square theorem;
   no forbidden declaration or hollow definition. Fresh scratch #print axioms probes
   show only propext, Classical.choice and Quot.sound for composition and representative
   data, and additionally sorryAx for core and its two consumers. No private counit
   helper remains: the real representative construction uses counit_isIso_kFlat.
   Verdict: pass as a decomposition, not an unconditional theorem closure.
3. Read the residual square and its proof documentation against the actual restriction,
   representative-source transport and comparisonIntoPullback_naturality declarations.
   The arbitrary eQ is handled by the derived automorphism comparing it with the
   canonical identification; Q is K-flat because it is the literal restriction of P.
   Empty opens admit no z; top opens give identity restriction; zero complexes and
   zero rings require no new assumption. The residual theorem omits the representative
   construction, which is separately proved, so it is a strict part of the argument.
   Fresh leanfinder query on naturality under open immersion found restrictFunctorComp;
   loogle query on restrictStalkNatIso found the underived stalk iso and germ equations;
   grep query on comparison/restriction found no matching Mathlib theorem. Repository
   searches and SingleComplexOpenRestrictionData supply ingredients, not this square.
   No short application closes the remaining square. Verdict: pass.
4. The main proof selects the residual natural isomorphism, constructs hQ, hcQ and eQ,
   then applies the square. The two supporting imports are proof-only; the composition,
   stalk comparison and Arrow imports occur in public signatures. Original dependencies
   remain below supporting nodes and none is pruned. The unit sk-thm-picard-semicon
   has realized.statement = [] and realized.steps = [[]]; no unit route is bypassed
   or edited. Verdict: pass.
5. Parsed every delivered node and checked lean.statement against the corresponding
   Lean declaration modulo whitespace, and proof_deps against the union of step uses.
   New nodes have source, searches, created, blueprint, chapter, unit and Lean records.
   Corrected representative-data proof metadata to cite the actual shared
   lem-pc-isomorphism-pullback-counit node rather than a copied private argument.
   Verified the exact restriction citation in Stacks Tag 0D5U and locality in 0DJ8;
   corrected stale proof_origin references to 08DW in the core and transport nodes.
   Verdict: pass after these metadata repairs.

Changed in this reading: corrected the shared counit proof dependency and stale source
metadata, and removed obsolete private-helper claims from the current report text.
The Lean proofs and statements were retained. Closed one original hole and added one
strictly smaller hole; net hole reduction is zero. No module is claimed pruned.

## Forced adaptations

### Sheaf.AlgebraicGeometry.OpenComparisonIntoPullbackTransport
Original against changed dependencies failed:
```
duleCat.extendScalars
              (algebraMap
                (TensorProduct ↑(R f g' ((pullback.fst g' U.ι) z)) ↑(A g' ((pullback.fst g' U.ι) z))
                  ↑(B f' ((pullback.fst g' U.ι) z)))
                ↑(C ((pullback.fst g' U.ι) z)))).obj
          ((cohomologyModel f f' g g' sq ((pullback.fst g' U.ι) z) P).cohomology i)) ⟶
      (derivedPullback (pullback.fst g' U.ι) ⋙
            comparisonStalkCohomology (pullback g' U.ι) z i ⋙
              forget₂ (ModuleCat ↑((pullback g' U.ι).presheaf.stalk z)) AddCommGrpCat).obj
        ((derivedPullback g').obj K))
    ((Classical.choose ⋯).hom ≫
      (forget₂ (ModuleCat ↑((pullback g' U.ι).presheaf.stalk z)) AddCommGrpCat).map
          (comparisonIntoPullback (U.ι ≫ f) (pullback.fst g' U.ι ≫ f') g (pullback.snd g' U.ι) sqU z
            (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⋯ i) ≫
        (comparisonStalkCohomology (pullback g' U.ι) z i ⋙
              forget₂ (ModuleCat ↑((pullback g' U.ι).presheaf.stalk z)) AddCommGrpCat).map
          ((derivedPullback (pullback.snd g' U.ι)).map (Classical.choose ⋯).hom ≫ openRestrictedCompositionMap g' U K))
    (l.hom ≫
      n.hom ≫
        (forget₂ (ModuleCat ↑((pullback g' U.ι).presheaf.stalk z)) AddCommGrpCat).map
            (comparisonIntoPullback (U.ι ≫ f) (pullback.fst g' U.ι ≫ f') g (pullback.snd g' U.ι) sqU z Q hcQ i) ≫
          (comparisonStalkCohomology (pullback g' U.ι) z i ⋙
                forget₂ (ModuleCat ↑((pullback g' U.ι).presheaf.stalk z)) AddCommGrpCat).map
            ((derivedPullback (pullback.snd g' U.ι)).map eQ.hom ≫
              (Classical.choose ⋯ (pullback.snd g' U.ι) U.ι).hom.app K ≫
                eqToHom ⋯ ≫ (Classical.choose ⋯ (pullback.fst g' U.ι) g').inv.app K))

Note: The following definitions were not unfolded because their definition is not exposed:
  getLimitCone ↦ 32
  getColimitCocone ↦ 436

(with the modules compiled into /tmp/forced-adaptation-_6352onq/.lbuild) [56.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
