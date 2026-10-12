/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence

/-!
# The Frobenius exchange isomorphisms of `φ̄^*` and `φ̄_*` are mates

Let `φ : X₀ ⟶ Y₀` be a morphism of schemes over a finite field `k`, with base change
`φ̄ : X ⟶ Y` to the geometric fibers. The pullback and the pushforward along `φ̄` of sheaves of
`ℚ̄_ℓ,X`-modules commute with the Frobenius pullbacks `Fr^* = (Fr⁻¹)_*`, through the exchange
isomorphisms `AlgebraicGeometry.ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso` (`e^*`)
and `AlgebraicGeometry.ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso` (`e_*`). This
file shows that `e_*` is the mate of `(e^*)⁻¹` under the adjunction `φ̄^* ⊣ φ̄_*`, so that the
adjunction lifts to sheaves with a Frobenius structure
(`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction`).

Both are compared with the composition isomorphism of pushforwards along the two sides of
`Fr_X ≫ φ̄ = φ̄ ≫ Fr_Y`: the conjugate of `(e^*)⁻¹` under the adjunctions composed with the
Frobenius equivalences is this isomorphism, and so is the mate of `e_*` under the Frobenius
equivalences; the iterated mate of `(e^*)⁻¹` is its conjugate.

## Main results

- `AlgebraicGeometry.ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv`:
  the mate of `(e^*)⁻¹` is `e_*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

section Sections

variable (A : Type u') [Category.{u + 1} A]

set_option maxHeartbeats 1000000 in
-- The section-wise comparison of the iterated base changes is a long `simp` computation.
/-- The unit of the Frobenius equivalences, pushed forward along `J`, followed by the
composition isomorphisms of pushforwards along `Fr_X ≫ J = J ≫ Fr_Y`, agrees with the unit
followed by the pushforward of the exchange isomorphism of `J_*` with `Fr^* = (Fr⁻¹)_*`. Both are
restriction maps along canonical isomorphisms of iterated base changes. -/
lemma lowerStar_map_unit_comp_lowerStarComp {X Y : Scheme.{u}} (J : Y ⟶ X) (a : Y ≅ Y)
    (b : X ≅ X) (c : a.hom ≫ J = J ≫ b.hom) (c' : J ≫ b.inv = a.inv ≫ J)
    (M : Sheaf (Scheme.ProEt.topology Y) A) :
    (J)_*[A].map ((lowerStarId A Y).inv.app M ≫
        (lowerStarCongr A a.inv_hom_id.symm).hom.app M ≫
        (lowerStarComp A a.inv a.hom).inv.app M) ≫
      (lowerStarComp A a.hom J).hom.app ((a.inv)_*[A].obj M) ≫
      (lowerStarCongr A c).hom.app ((a.inv)_*[A].obj M) ≫
      (lowerStarComp A J b.hom).inv.app ((a.inv)_*[A].obj M) =
    ((lowerStarId A X).inv.app ((J)_*[A].obj M) ≫
        (lowerStarCongr A b.inv_hom_id.symm).hom.app ((J)_*[A].obj M) ≫
        (lowerStarComp A b.inv b.hom).inv.app ((J)_*[A].obj M)) ≫
      (b.hom)_*[A].map ((lowerStarComp A J b.inv).hom.app M ≫
        (lowerStarCongr A c').hom.app M ≫ (lowerStarComp A a.inv J).inv.app M) := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V ↦ ?_))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStarId_inv_app_hom_app, lowerStar_map_hom_app', lowerStar_obj_obj_map',
    ← Functor.map_comp, ← op_comp, Category.assoc]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp only [Quiver.Hom.unop_op]
  apply pullback.hom_ext
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullbackId]
  · simp only [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullbackId, Functor.comp_obj, Functor.id_obj, Functor.const_obj_obj,
      Functor.map_comp, Category.assoc, MorphismProperty.Comma.comp_hom, Comma.comp_left,
      MorphismProperty.Over.pullback_map_left, MorphismProperty.Over.pullbackComp_inv_app_left,
      pullback.map_id, Category.comp_id, MorphismProperty.Over.pullbackComp_hom_app_left,
      Category.id_comp, MorphismProperty.Over.pullbackId_hom_app_left, limit.lift_π,
      PullbackCone.mk_π_app]
    rw [pullback.condition_assoc]
    simp

end Sections

/-- The inverse of the exchange isomorphism
`AlgebraicGeometry.ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso` of the pullbacks is
conjugate, under the adjunctions `φ̄^* ⊣ φ̄_*` composed with the Frobenius equivalences, to the
composition isomorphism `(Fr_X)_* ⋙ φ̄_* ≅ φ̄_* ⋙ (Fr_Y)_*` of pushforwards. Each of its five
constituents is conjugate to the identity, to a composition isomorphism or to a congruence
isomorphism of pushforwards. -/
lemma conjugateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv :
    conjugateEquiv
        ((adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h)).comp
          (adicLowerStarEquivalence l f.geometricGaloisFrobenius).symm.toAdjunction)
        ((adicLowerStarEquivalence l g.geometricGaloisFrobenius).symm.toAdjunction.comp
          (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h)))
      (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h).inv =
    (adicLowerStarComp l f.geometricGaloisFrobenius.hom (Scheme.Hom.geometricFiberMap φ h)).hom ≫
      (adicLowerStarCongr l
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm).hom ≫
      (adicLowerStarComp l (Scheme.Hom.geometricFiberMap φ h)
        g.geometricGaloisFrobenius.hom).inv := by
  set j := Scheme.Hom.geometricFiberMap φ h
  set a := f.geometricGaloisFrobenius
  set b := g.geometricGaloisFrobenius
  set adj := adicUpperStarLowerStarAdjunction l j
  have h₁ := conjugateEquiv_whiskerRight (adicUpperStarLowerStarAdjunction l b.hom)
    (adicLowerStarEquivalence l b).symm.toAdjunction adj (adicUpperStarIsoLowerStarInv l b).inv
  have h₂ : conjugateEquiv (adicUpperStarLowerStarAdjunction l (j ≫ b.hom))
      ((adicUpperStarLowerStarAdjunction l b.hom).comp adj) (adicUpperStarComp l j b.hom).inv =
      (adicLowerStarComp l j b.hom).inv :=
    conjugateEquiv_adicUpperStarComp_inv l j b.hom
  have h₃ := conjugateEquiv_adicUpperStarCongr_inv l
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm
  have h₄ : conjugateEquiv (adj.comp (adicUpperStarLowerStarAdjunction l a.hom))
      (adicUpperStarLowerStarAdjunction l (a.hom ≫ j)) (adicUpperStarComp l a.hom j).hom =
      (adicLowerStarComp l a.hom j).hom :=
    conjugateEquiv_adicUpperStarComp_hom l a.hom j
  have h₅ := conjugateEquiv_whiskerLeft (adicLowerStarEquivalence l a).symm.toAdjunction
    (adicUpperStarLowerStarAdjunction l a.hom) adj (adicUpperStarIsoLowerStarInv l a).hom
  have hb : conjugateEquiv (adicUpperStarLowerStarAdjunction l b.hom)
      (adicLowerStarEquivalence l b).symm.toAdjunction
      (adicUpperStarIsoLowerStarInv l b).inv = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_inv _ _
  have ha : conjugateEquiv (adicLowerStarEquivalence l a).symm.toAdjunction
      (adicUpperStarLowerStarAdjunction l a.hom) (adicUpperStarIsoLowerStarInv l a).hom = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_hom _ _
  rw [hb] at h₁
  rw [ha] at h₅
  simp only [adicUpperStarGeometricFiberMapCompFrobeniusIso, Iso.trans_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv, Category.assoc]
  rw [← conjugateEquiv_comp _ ((adicUpperStarLowerStarAdjunction l b.hom).comp adj) _,
    ← conjugateEquiv_comp _ (adicUpperStarLowerStarAdjunction l (j ≫ b.hom)) _,
    ← conjugateEquiv_comp _ (adicUpperStarLowerStarAdjunction l (a.hom ≫ j)) _,
    ← conjugateEquiv_comp _ (adj.comp (adicUpperStarLowerStarAdjunction l a.hom)) _]
  rw [h₁, h₂, h₃, h₄, h₅, Functor.whiskerRight_id', Functor.whiskerLeft_id']
  simp only [Category.comp_id, Category.assoc]
  rw [Category.id_comp]

set_option maxHeartbeats 2000000 in
-- The kernel needs more time to unfold the composite `(Fr⁻¹)_* ⋙ Fr_*` in the unit of the
-- Frobenius equivalence.
/-- The composition isomorphism `J_* ⋙ (b⁻¹)_* ≅ (a⁻¹)_* ⋙ J_*` of pushforwards along the two
sides of `J ≫ b⁻¹ = a⁻¹ ≫ J` is the mate, under the equivalences `(a⁻¹)_* ⊣ a_*` and
`(b⁻¹)_* ⊣ b_*`, of the composition isomorphism along the two sides of `a ≫ J = J ≫ b`. -/
lemma mateEquiv_adicLowerStarComp_hom {X Y : Scheme.{u}} (J : Y ⟶ X) (a : Y ≅ Y) (b : X ≅ X)
    (c : a.hom ≫ J = J ≫ b.hom) (c' : J ≫ b.inv = a.inv ≫ J) :
    (mateEquiv (adicLowerStarEquivalence l a).symm.toAdjunction
        (adicLowerStarEquivalence l b).symm.toAdjunction
        (TwoSquare.mk _ _ _ _ (adicLowerStarComp l J b.inv ≪≫ adicLowerStarCongr l c' ≪≫
          (adicLowerStarComp l a.inv J).symm).hom)).natTrans =
    (adicLowerStarComp l a.hom J).hom ≫ (adicLowerStarCongr l c).hom ≫
      (adicLowerStarComp l J b.hom).inv := by
  refine congrArg TwoSquare.natTrans (mateEquiv_eq_of_unit _ _ _ (TwoSquare.mk _ _ _ _ _)
    fun M ↦ Mod.hom_ext _ _ ?_)
  have key := lowerStar_map_unit_comp_lowerStarComp (WeilCoefficients.{u} l) J a b c c' M.X
  have hu (X : Scheme.{u}) (e : X ≅ X) (N : AdicSheaf l X) :
      ((adicLowerStarEquivalence l e).symm.toAdjunction.unit.app N).hom =
        (lowerStarId _ X).inv.app N.X ≫ (lowerStarCongr _ e.inv_hom_id.symm).hom.app N.X ≫
          (lowerStarComp _ e.inv e.hom).inv.app N.X :=
    adicLowerStarEquivalence_counitIso_inv_app_hom e N
  simp only [Mod.comp_hom', adicLowerStar_map_hom, hu, NatTrans.comp_app,
    adicLowerStarComp_hom_app_hom, adicLowerStarComp_inv_app_hom, adicLowerStarCongr_hom_app_hom,
    Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc] at key ⊢
  exact key

/-- The exchange isomorphism
`AlgebraicGeometry.ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso` of the pushforwards
is the mate, under the Frobenius equivalences, of the composition isomorphism
`(Fr_X)_* ⋙ φ̄_* ≅ φ̄_* ⋙ (Fr_Y)_*` of pushforwards. -/
lemma mateEquiv_adicLowerStarGeometricFiberMapCompFrobeniusIso_hom :
    (mateEquiv (adicLowerStarEquivalence l f.geometricGaloisFrobenius).symm.toAdjunction
        (adicLowerStarEquivalence l g.geometricGaloisFrobenius).symm.toAdjunction
        (TwoSquare.mk _ _ _ _
          (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ h).hom)).natTrans =
    (adicLowerStarComp l f.geometricGaloisFrobenius.hom (Scheme.Hom.geometricFiberMap φ h)).hom ≫
      (adicLowerStarCongr l
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm).hom ≫
      (adicLowerStarComp l (Scheme.Hom.geometricFiberMap φ h)
        g.geometricGaloisFrobenius.hom).inv :=
  mateEquiv_adicLowerStarComp_hom l _ _ _ _ _

/-- **The Frobenius exchange isomorphisms of `φ̄^*` and `φ̄_*` are mates**: under the adjunction
`φ̄^* ⊣ φ̄_*`, the mate of the inverse of the exchange isomorphism
`AlgebraicGeometry.ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso` of the pullbacks is
the exchange isomorphism `AlgebraicGeometry.ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso`
of the pushforwards. Both iterated mates under the Frobenius equivalences are the composition
isomorphism `(Fr_X)_* ⋙ φ̄_* ≅ φ̄_* ⋙ (Fr_Y)_*`. -/
lemma mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv :
    (mateEquiv (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h))
        (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h))
        (TwoSquare.mk _ _ _ _
          (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h).inv)).natTrans =
      (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ h).hom := by
  have h₁ := iterated_mateEquiv_conjugateEquiv
    (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h))
    (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h))
    (adicLowerStarEquivalence l g.geometricGaloisFrobenius).symm.toAdjunction
    (adicLowerStarEquivalence l f.geometricGaloisFrobenius).symm.toAdjunction
    (TwoSquare.mk _ _ _ _ (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h).inv)
  rw [conjugateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv,
    ← mateEquiv_adicLowerStarGeometricFiberMapCompFrobeniusIso_hom] at h₁
  exact congrArg TwoSquare.natTrans ((mateEquiv _ _).injective h₁)

end AlgebraicGeometry.ProEtale
