/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CondensedProjectionScalarSquare
import WeilConjectures.SixFunctors.CondensedScalarProjectionCocycleData

/-! # Condensed scalar projection cocycle: compact-support tower -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing
set_option maxHeartbeats 10000000 in
-- Normalize several derived-category presentations while keeping their constructions folded.
/-- The coefficient cocycle for the specified compact-support comparison on an
arbitrary compactification.

Source: latest blueprint, sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, successive coefficient changes
(blueprint: lem-sf-condensed-scalar-compact-support-cocycle).

Proof: Regard c.Z as a scheme over k via c.g followed by Y.hom. The compactification
maps become an open immersion and a proper map over k. Expand
scalarCompactSupportMap into the direct-image mate at the open extension of K
followed by direct image of the canonical open scalar comparison. Apply the
coefficient-composition clause of scalarDirectImageMateCoherence to the first
factor. Its naturality moves the first open comparison through the second
coefficient's direct-image mate. The normalized immersion tower of scalarSixPullback
and its openComparison field give the tower for the actual derived open comparison:
conjugate the immersion tower by scalarSixOpenIso, use naturality of scalarSixTower,
and cancel the inverse presentation maps. Map that open tower under the final
proper direct-image functor. Functoriality and associativity now give the stated
compact-support identity. This proof needs no canonical choice of c, no inverse
of the direct-image mate, and no flatness of either coefficient map. -/
theorem condensedScalarCompactSupportCocycle
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (_hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell k)
    {Λ₀ Λ₁ Λ₂ : ScalarSixRing.{u}}
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂)
    (_ha : ListedCoefficientMap ell a) (_hb : ListedCoefficientMap ell b)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left) :
(∀ K : DerivedCategory (ModuleRingedComparison.internalModules Λ₀.X X.left),
      (scalarSixTower a b Y.left).hom.app
            ((rightDerivedLowerShriekOfCompactification Λ₀.X c).obj K) ≫
          (scalarCompactSupportMap (a ≫ b) c.i c.g).app K =
        (scalarSixChange b Y.left).map ((scalarCompactSupportMap a c.i c.g).app K) ≫
          (scalarCompactSupportMap b c.i c.g).app ((scalarSixChange a X.left).obj K) ≫
          (rightDerivedLowerShriekOfCompactification Λ₂.X c).map
            ((scalarSixTower a b X.left).hom.app K)) := by
  classical
  let Z : Over (Spec (.of k)) := Over.mk (c.g ≫ Y.hom)
  have : LocallyOfFiniteType Z.hom :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y.hom))
  have : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (c.g ≫ Y.hom))
  have : IsSeparated Z.hom := inferInstanceAs (IsSeparated (c.g ≫ Y.hom))
  let j : X ⟶ Z := Over.homMk c.i (by
    change c.i ≫ c.g ≫ Y.hom = X.hom
    rw [← Category.assoc, ← c.comm, f.w])
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion c.i)
  obtain ⟨G, C, hext⟩ := scalarSixPullback
  obtain ⟨E, _hE, D, O, ⟨S⟩⟩ := hext ell k
  have hi {A B : ScalarSixRing.{u}} (r : A ⟶ B) :
      Functor.isoWhiskerRight (scalarSixOpenIso E G O A j).symm
          (scalarSixChange r Z.left) ≪≫
        S.normalized.beta r j ≪≫
        Functor.isoWhiskerLeft (scalarSixChange r X.left) (scalarSixOpenIso E G O B j) =
      scalarSixOpenScalarIso r j.left := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (cancel_epi ((scalarSixChange r Z.left).map
      ((scalarSixOpenIso E G O A j).hom.app M))).mp
    simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    rw [(scalarSixChange r Z.left).map_id, Category.id_comp]
    exact (S.normalized.openComparison r j M).symm
  have hopen (K : DerivedCategory (ModuleRingedComparison.internalModules Λ₀.X X.left)) :=
    condensedScalarCocyclePresentationTransport
      (scalarSixChange a X.left) (scalarSixChange b X.left)
      (scalarSixChange (a ≫ b) X.left)
      (scalarSixChange a Z.left) (scalarSixChange b Z.left)
      (scalarSixChange (a ≫ b) Z.left)
      (scalarSixExtension E G Λ₀ j) (openImmersionLowerShriek Λ₀.X c.i).mapDerivedCategory
      (scalarSixExtension E G Λ₁ j) (openImmersionLowerShriek Λ₁.X c.i).mapDerivedCategory
      (scalarSixExtension E G Λ₂ j) (openImmersionLowerShriek Λ₂.X c.i).mapDerivedCategory
      (scalarSixOpenIso E G O Λ₀ j).symm
      (scalarSixOpenIso E G O Λ₁ j).symm
      (scalarSixOpenIso E G O Λ₂ j).symm
      (S.normalized.beta a j) (S.normalized.beta b j) (S.normalized.beta (a ≫ b) j)
      (scalarSixTower a b X.left) (scalarSixTower a b Z.left) (S.tower a b j) K
  intro K
  have ho := hopen K
  simp only [Iso.symm_symm_eq] at ho
  rw [hi a, hi b, hi (a ≫ b)] at ho
  simp only [scalarSixOpenScalarIso] at ho
  have hg := (scalarDirectImageMateCoherence a c.g (𝟙 Y.left)).2.2.2.2 Λ₂ b
    ((openImmersionLowerShriek Λ₀.X c.i).mapDerivedCategory.obj K)
  have hn := (scalarDirectImageMate b c.g).naturality
    ((derivedOpenImmersionShriekIso (Λ := Λ₀.X) (Λ' := Λ₁.X) a.hom.hom c.i).hom.app K)
  simp only [Functor.comp_map] at hn
  simp only [scalarCompactSupportMap, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp, Category.comp_id]
  simp only [Category.assoc]
  erw [reassoc_of% hg]
  erw [← Functor.map_comp, ho]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hn]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
