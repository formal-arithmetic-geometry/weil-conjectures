/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

/- Source anchor for this transported binary-gluing step:
`det-sp-tower-gluing`, Gluing and Uniformity, in the current blueprint at
`part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-ladic-summary/`
`sec-towers-and-integral-coefficients/sk-prop-sp-tower-geometric/`
`sk-prop-sp-tower-geometric-gluing.proof.md`.
-/

/-! # Restriction of representing pairs to source opens

Source: latest smooth-purity blueprint, Local pairs, Gluing and Uniformity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Restriction along an arbitrary open immersion over the ground field.
Source: latest smooth-purity blueprint, Gluing, restriction of local pairs
(blueprint: lem-sp-tower-pair-open-restriction).

Proof. Apply the etale preservation fields to the open map. Transport extension
through the specified openEtaleCoordinates isomorphism. Then compose the open
adjunction Hom equivalence, the representing bijection for the extended test,
and the compact-support open-composition Hom equivalence. Naturality identifies
the resulting map with the displayed counit word. The right preservation field
also puts the restricted representing object in the full ctf category. -/
theorem tower_pair_open_morphism_restriction
    (k : Type u) [Field k] (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h)
    (U X Y : Over (Spec (.of k)))
    [IsSeparated U.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left]
    (f : X ⟶ Y) (c : Compactification f.left)
    (H : SpTowerCalculus.C l E b q X.left)
    (K : SpTowerCalculus.C l E b q Y.left)
    (eps : (SpTowerCalculus.F l E b o q c).obj H.obj ⟶ K.obj)
    (rep : ∀ M : SpTowerCalculus.C l E b q X.left,
      Function.Bijective (fun a : M.obj ⟶ H.obj ↦
        (SpTowerCalculus.F l E b o q c).map a ≫ eps)) :
    spConstructibleTorTowers l E U.left (q.abelian U.left)
      ((SpTowerCalculus.etalePullback l E b o q j.left).obj H.obj) ∧
      ∀ M : SpTowerCalculus.C l E b q U.left,
        Function.Bijective (fun a : M.obj ⟶
            (SpTowerCalculus.etalePullback l E b o q j.left).obj H.obj ↦
          (SpTowerCalculus.F l E b o q (c.precomp j.left)).map a ≫
            (SpTowerCalculus.openComposition l E b o q j.left c).inv.app
              ((SpTowerCalculus.etalePullback l E b o q j.left).obj H.obj) ≫
            (SpTowerCalculus.F l E b o q c).map
              ((towerOpenAdjunction l E b o q j.left).counit.app H.obj) ≫ eps) := by
  let : U.left.Over (Spec (.of k)) := ⟨U.hom⟩
  have : IsSeparated (U.left ↘ Spec (.of k)) := by
    change IsSeparated U.hom
    infer_instance
  have : LocallyOfFiniteType (U.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType U.hom
    infer_instance
  have : QuasiCompact (U.left ↘ Spec (.of k)) := by
    change QuasiCompact U.hom
    infer_instance
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  have : IsSeparated (X.left ↘ Spec (.of k)) := by
    change IsSeparated X.hom
    infer_instance
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType X.hom
    infer_instance
  have : QuasiCompact (X.left ↘ Spec (.of k)) := by
    change QuasiCompact X.hom
    infer_instance
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  have : IsSeparated (Y.left ↘ Spec (.of k)) := by
    change IsSeparated Y.hom
    infer_instance
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType Y.hom
    infer_instance
  have : QuasiCompact (Y.left ↘ Spec (.of k)) := by
    change QuasiCompact Y.hom
    infer_instance
  have : j.left.IsOver (Spec (.of k)) := ⟨Over.w j⟩
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  obtain ⟨hL, hR⟩ := cal.etale.etale_preserves j.left
  refine ⟨hR H, ?_⟩
  have hL' (M : SpTowerCalculus.C l E b q U.left) :
      spConstructibleTorTowers l E X.left (q.abelian X.left)
        ((SpTowerCalculus.openExtension l E b o q j.left).obj M.obj) :=
    tower_ctf_of_iso l E b q X.left
      ((SpTowerCalculus.openEtaleCoordinates l E b o q z j.left
        (cal.etale.etale j.left)).app M.obj) (hL M)
  exact fun M ↦ restrict_representing_subcategory _ _ _ _
    (towerOpenAdjunction l E b o q j.left) hL' _ _
    (SpTowerCalculus.openComposition l E b o q j.left c) H K.obj eps rep M

/-- Restriction of a representing pair along an arbitrary source open, with the
actual open-adjunction counit and normalized compact-support compositor.
Source: latest blueprint `sk-prop-sp-tower-geometric-gluing.proof.md`, Gluing,
restriction of local pairs (blueprint: lem-sp-tower-pair-open-restriction).

Proof. Open extension preserves the constructible finite-Tor category by the supplied
calculus. Apply the original representing bijection to that extension. The open
adjunction identifies its source with Hom into the open inverse image of H, and
openComposition identifies its target with compact support on the smaller open.
Naturality of the inverse compositor and the adjunction counit formula identify this
composite bijection with the displayed map. The argument applies also to an empty open.
-/
theorem tower_pair_open_restriction
    (k : Type u) [Field k] (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h)
    (X Y : Over (Spec (.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (H : SpTowerCalculus.C l E b q X.left)
    (K : SpTowerCalculus.C l E b q Y.left)
    (eps : (SpTowerCalculus.F l E b o q c).obj H.obj ⟶ K.obj)
    (rep : ∀ M : SpTowerCalculus.C l E b q X.left,
      Function.Bijective (fun a : M.obj ⟶ H.obj ↦
        (SpTowerCalculus.F l E b o q c).map a ≫ eps))
    (U : X.left.Opens) (M : SpTowerCalculus.C l E b q U.toScheme) :
    Function.Bijective (fun a : M.obj ⟶
        (SpTowerCalculus.etalePullback l E b o q U.ι).obj H.obj ↦
      (SpTowerCalculus.F l E b o q (c.precomp U.ι)).map a ≫
        (SpTowerCalculus.openComposition l E b o q U.ι c).inv.app
          ((SpTowerCalculus.etalePullback l E b o q U.ι).obj H.obj) ≫
        (SpTowerCalculus.F l E b o q c).map
          ((towerOpenAdjunction l E b o q U.ι).counit.app H.obj) ≫ eps) := by
  exact restrict_representing_subcategory _ _ _ _ (towerOpenAdjunction l E b o q U.ι)
    (tower_pair_open_preserves l E b o q k z h cal X U).1 _ _
    (SpTowerCalculus.openComposition l E b o q U.ι c) H K.obj eps rep M

end AlgebraicGeometry.ProEtale.SpTowerGluing
