module

public import Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- The Hom equivalences and their stage/apex compatibility after a chosen open
localization. Source: Stacks Project, perfect.tex Tags 09RE and 079W.
(blueprint: lem-pc-perfect-hom-open-stage-maps).
Proof: Put B = t inverse-image W and L = exact derived restriction to B.
Yoneda and derived adjunction identify F_j with Rpi_j* Lpi_j*Q;
evaluate stageNatural at identities to recover the representing isomorphism.
Apply the canonical open-restriction/direct-image comparison to this isomorphism.
The restricted projection is canonically the pullback projection for B.ι ≫ s.
Open adjunction and shift adjunction identify Hom(P,RB.ι* LF_j[n]) with
Hom(LP[-n],LF_j). Derived adjunction for the restricted projection and the
pullback-composition comparison give the displayed stage equivalences for
P' = LP[-n] and Q' = LQ. Repeat at the apex. Naturality of these comparisons,
with h.stageMap and h.limitMap, proves both displayed equations; the comparisons
are pinned by their derived units and counits, hence give exactly the specified
perfectStageMap and perfectLimitMap. The same constructions work on empty opens,
where all Hom sets are singletons, and for zero objects. -/
theorem perfect_hom_open_stage_maps
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s₀] [QuasiCompact s₀] [QuasiSeparated s₀]
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (W : X.Opens) (hW : IsCompact (W : Set X))
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (ht : W ≤ t.opensRange)
    (s : Y ⟶ Spec (R.obj i)) (hs : s = t ≫ s₀)
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ B : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over B))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d) (n : ℤ)
    :
    let B := t ⁻¹ᵁ W
    let Z := B.toScheme
    let s' := B.ι ≫ s
    let P' := ((schemeMVDerivedRestriction Y B).obj P)⟦-n⟧
    let Q' := (schemeMVDerivedRestriction Y B).obj Q
    let H := schemeMVDerivedRestriction Y B ⋙ schemeDerivedDirectImage B.ι
    ∃ (e : ∀ j : Set.Ici i, (P ⟶ (H.obj (F.obj j))⟦n⟧) ≃
        ((derivedPullback (pullback.fst s' (Spec.map (R.map (homOfLE j.property))))).obj P' ⟶
         (derivedPullback (pullback.fst s' (Spec.map (R.map (homOfLE j.property))))).obj Q'))
      (b : (P ⟶ (H.obj d.pt)⟦n⟧) ≃
        ((derivedPullback (pullback.fst s' (Spec.map (c.ι.app i)))).obj P' ⟶
         (derivedPullback (pullback.fst s' (Spec.map (c.ι.app i)))).obj Q')),
      (∀ (j l : Set.Ici i) (hjl : j ≤ l) (f : P ⟶ (H.obj (F.obj j))⟦n⟧),
        e l (f ≫ (H.map (F.map (homOfLE hjl)))⟦n⟧') =
          perfectStageMap R s' j.property hjl (e j f)) ∧
      (∀ (j : Set.Ici i) (f : P ⟶ (H.obj (F.obj j))⟦n⟧),
        b (f ≫ (H.map (d.ι.app j))⟦n⟧') =
          perfectLimitMap R c s' j.property (e j f)) := by
  sorry

end AlgebraicGeometry
