# completedFree_adicSeparated and completedFreeCell_automaticLinearity

## Reason

The old separation statement is false for non-quasi-separated representables.
This was independently diagnosed in M8's landed report and confirmed here.
Let X be the Boolean spectrum of eventually constant F2 sequences, with points
N and infinity. Take l=3. Double X along its open isolated-point locus E=N, obtaining an
etale X-scheme U. Its two sections s,t agree exactly on E. For the continuous
coefficient a(n)=l^n, a(infinity)=0, the sheafified section a([s]-[t]) is nonzero
but divisible by every positive l-power: divide its tail, and discard the finite
initial coordinates where [s]-[t] is already zero. A map killing its free-presheaf representative has
image in E or in {infinity}; these maps do not form a pro-etale cover, by the
finite quasi-compact-image criterion. See coord/reports/M8/Sheaf.Paper.CompletedFreeAdicSeparation.md.
Repleteness cannot turn countably many unrelated presheaf-equality sieves into
a covering intersection.

Correct the two intermediate helpers to pro-affine etale U. Preserve the free
presheaf, free cell, distinguished generator and descent-map definitions verbatim.
Preserve completedRealization_section_action and every other public declaration
of CompletedCoefficientSectionAction verbatim: prove the action formula first on
this basis, and descend using the already proved cover-density of
Scheme.AffineProEt.toProEt X. That instance works for arbitrary X; no affineness
assumption on X is added. No target signature or target-used definition changes.
The revised separation proof reduces to geometric local-dual detection; the
coefficient annihilation, limit detection and local functional calculation are
fully proved. This is a repair/decomposition, not a proof of the false old theorem.

The free-generator module also narrows its public imports from
DiagonalCoefficientReference to DiagonalTowerLimitInterface,
ProEtaleCompletedCoefficients and InternalAbelianSheafModuleEquivalence. Its sole
direct importer SectionAction already imports DiagonalCoefficientReference itself.
No exported attribute or definition body changes.

## Old

```lean
theorem completedFree_adicSeparated (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ) :
    let R := Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)
    let P := (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      ((PresheafOfModules.free R.obj).obj (uliftYoneda.{u + 1}.obj U.unop))
    ∀ (V : X.ProEtᵒᵖ) (x : P.val.obj V),
      (∀ n : ℕ, Presheaf.imageSieve
        ((l ^ (n + 1) • 𝟙 ((SheafOfModules.toSheaf R).obj P)).hom) x ∈
          Scheme.ProEt.topology X V.unop) → x = 0
```

```lean
theorem completedFreeCell_automaticLinearity (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ)
    (c : (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X)
            (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)) ≅
        Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
    (N : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X)
          (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X))))
    (g : (SheafOfModules.toSheaf _).obj N ⟶
      (SheafOfModules.toSheaf _).obj (completedFreeCell l X U))
    (V : X.ProEtᵒᵖ) (r : ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X)
          (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X))).obj.obj V)
    (x : N.val.obj V) :
    g.hom.app V (r • x) =
      @SMul.smul _ ((completedFreeCell l X U).val.obj V) inferInstance
        (c.hom.hom.app V r) (g.hom.app V x)
```

## New

```lean
theorem completedFree_adicSeparated (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ) (hU : proAffineEtale U.unop.hom) :
    let R := Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)
    let P := (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      ((PresheafOfModules.free R.obj).obj (uliftYoneda.{u + 1}.obj U.unop))
    ∀ (V : X.ProEtᵒᵖ) (x : P.val.obj V),
      (∀ n : ℕ, Presheaf.imageSieve
        ((l ^ (n + 1) • 𝟙 ((SheafOfModules.toSheaf R).obj P)).hom) x ∈
          Scheme.ProEt.topology X V.unop) → x = 0
```

```lean
theorem completedFreeCell_automaticLinearity (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ) (hU : proAffineEtale U.unop.hom)
    (c : (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X)
            (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)) ≅
        Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
    (N : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X)
          (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X))))
    (g : (SheafOfModules.toSheaf _).obj N ⟶
      (SheafOfModules.toSheaf _).obj (completedFreeCell l X U))
    (V : X.ProEtᵒᵖ) (r : ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X)
          (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X))).obj.obj V)
    (x : N.val.obj V) :
    g.hom.app V (r • x) =
      @SMul.smul _ ((completedFreeCell l X U).val.obj V) inferInstance
        (c.hom.hom.app V r) (g.hom.app V x)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedFreeAdicSeparation | F2 | Corrects its false intermediate statement and supplies a complete combination proof. |
| Sheaf.Paper.CompletedCoefficientFreeGenerator | unclaimed | Sole user of completedFree_adicSeparated; adds the proAffineEtale hypothesis to automatic linearity and passes it to separation. Definitions remain identical. |
| Sheaf.Paper.CompletedCoefficientSectionAction | unclaimed | Sole external user of completedFreeCell_automaticLinearity; uses it on pro-affine etale generators and descends the unchanged public identity by the cover-dense basis. |

These are exactly the declaration users found by tools/downstream.py --uses,
including the defining modules. Direct importers of each changed public interface
are the next module in the table and are compiled together in this packet.
Other nodes citing the helpers are exactly the corresponding two parent nodes;
their proofs and dependency records are updated in this packet. The section-action
node's statement and public signatures are unchanged. No source-library module is
modified or withdrawn.

## Status

landed 20261027T034636-L-3668862 2026-10-27 (merge of deliver/F2/Sheaf.Paper.CompletedFreeAdicSeparation)
