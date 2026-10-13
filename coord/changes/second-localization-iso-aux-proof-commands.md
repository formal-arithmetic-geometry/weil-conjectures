# RingTensorCohomology second localization proof commands

## Reason

The stage-3 preflight requests a change record for local commands introduced by the proof.
No statement, definition, visibility, global instance, or public import changes. The added
`omit ... in` commands apply only to new private helpers. The two backward elaboration options
control checking of these proofs; they do not alter exported declarations. The existing
`tools/leanindex.py` interface scanner also treats the original indented ` theorem` lines as
continuations of the preceding variable command, so changing their proof bodies is reported as
changing ordinary commands. This record makes that static-check finding explicit for independent
review; the script itself was not changed.

## Old

The public signatures, unchanged:

```lean
 theorem exists_secondLocalization_hom
    (T : Submonoid B) [IsLocalization T Bp] (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D) :
    ∃ f : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ⟶
      (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj (K.cohomology i),
      IsSecondLocalizationMap R A B Bp D hflat Q L K i f

 theorem secondLocalization_hom_isIso
    (T : Submonoid B) [IsLocalization T Bp] (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
    (f : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ⟶
      (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj (K.cohomology i))
    (hf : IsSecondLocalizationMap R A B Bp D hflat Q L K i f) : IsIso f
```

No backward elaboration options or private-helper `omit` prefixes were present.

## New

Exactly the same public signatures as above. Both proofs are complete. Added checking options:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Four private comparison helpers use `omit [Algebra A D] [Algebra B D] [Algebra Bp D]
tAD tBD tApD tBpD tBBpD in`. The private algebra-map equality helper omits the three
HasDerivedCategory assumptions. All these omissions end at their respective private theorem.
They do not change either public theorem's context. No downstream module needs adaptation.

## Users

`tools/downstream.py --uses` finds only the following external user of the two public declarations;
it also finds their declarations in the item itself. The unchanged interface leaves all
1372 transitive importing modules unaffected.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.SecondLocalizationIso | unclaimed in this clone | Same signatures; its existing applications need no changes. |
| Sheaf.Algebra.Homology.SecondLocalizationIsoAux | Y3 | Both proofs completed; no public signature change. |

No definition used by a target has changed, so no target statement review is reopened.

## Status

landed 20261013T234526-L-2168759 2026-10-13 (merge of deliver/Y3/Sheaf.Algebra.Homology.SecondLocalizationIsoAux)
