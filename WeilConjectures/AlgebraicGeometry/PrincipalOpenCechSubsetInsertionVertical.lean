/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion

/-! # Vertical differential of explicit subset insertion

## References

* Stacks Project, Tag 08C1 and equation (20.40.0.1) (Tag 08C0).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

private theorem sum_apply {α : Type*} [Fintype α]
    {G H : AddCommGrpCat.{u}} (F : α → (G ⟶ H)) (x : G) :
    (∑ i, F i) x = ∑ i, F i x := by
  change (AddCommGrpCat.homAddEquiv (∑ i, F i)) x = _
  simp only [map_sum, AddMonoidHom.finsetSum_apply]
  rfl

private theorem sectionTransport_natural
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (S : {S : Finset (Fin r) // S.Nonempty})
    {M N : (Spec (.of A)).Modules} (g : M ⟶ N)
    (s : (modulesSpecToSheaf.obj M).obj.obj (op (principalSubsetOpen A r f S.val))) :
    let V := principalSubsetUnion A r f
    let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
    let W := alternatingCechIntersection U (principalSubsetTuple r S)
    let R := SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) V ⋙
      (Scheme.Modules.overEquiv V).functor
    (principalSubsetSectionTransport A r f N S).hom
        ((modulesSpecToSheaf.map g).hom.app (op (principalSubsetOpen A r f S.val)) s) =
      (R.map g).app W ((principalSubsetSectionTransport A r f M S).hom s) := by
  intro V U W R
  have hW : V.ι ''ᵁ W = principalSubsetOpen A r f S.val := by
    dsimp only [W, U, V]
    rw [principalSubsetIntersection, V.ι.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_eq_right.mpr (principalSubsetOpen_le A r f S)]
  let e := (Scheme.Modules.overFunctorEquiv V).inv
  have hq := congrArg (fun z ↦ z s) (g.mapPresheaf.naturality (eqToHom hW).op)
  have he := congrArg (fun z ↦ (z.app W)
    (M.presheaf.map (eqToHom hW).op s)) (e.naturality g)
  change (e.app N).app W
    (N.presheaf.map (eqToHom hW).op ((g.app (principalSubsetOpen A r f S.val)) s)) = _
  change (g.app (V.ι ''ᵁ W)) (M.presheaf.map (eqToHom hW).op s) =
    N.presheaf.map (eqToHom hW).op ((g.app (principalSubsetOpen A r f S.val)) s) at hq
  exact (congrArg ((e.app N).app W) hq.symm).trans he

set_option maxHeartbeats 400000 in
-- Elaborating both extension components and the section-transport coercions exceeds 200000.
/-- The vertical total differential on explicit subset coordinates, with the total differential
convention of `alternatingCechTotalFunctor` (Stacks, Tag 08C1). -/
theorem principalSubsetInsertion_vertical
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) :
    let V := principalSubsetUnion A r f
    let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
    let K := (alternatingCechDoubleFunctor U).obj (principalSubsetRestriction A r f J)
    let H := forget₂
      (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
    let D := principalSubsetOpen A r f
    ∀ (n : ℤ) (s : principalSubsetCoordinates A r f J n),
      (H.map (K.D₂ (ComplexShape.up ℤ) n (n + 1)))
        (principalSubsetInsertion A r f J n s) =
      principalSubsetInsertion A r f J (n + 1) (fun S ↦
          (-1 : A) ^ (S.val.card - 1) •
            (modulesSpecToSheaf.map
              (J.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
                (op (D S.val)) (s S))  := by
  classical
  intro V U K H D n s
  change ((principalSubsetInsertion A r f J n ≫
    H.map (K.D₂ (ComplexShape.up ℤ) n (n + 1))) s) = _
  simp only [principalSubsetInsertion, Preadditive.sum_comp, Category.assoc]
  with_unfolding_all
    rw [sum_apply, sum_apply]
  apply Finset.sum_congr rfl
  intro S _
  change ((principalSubsetInsertOne A r f J n S ≫
    H.map (K.D₂ (ComplexShape.up ℤ) n (n + 1))) (s S)) =
      (principalSubsetInsertOne A r f J (n + 1) S)
        ((-1 : A) ^ (S.val.card - 1) •
          (modulesSpecToSheaf.map
            (J.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
              (op (D S.val)) (s S))
  let p : ℕ := S.val.card - 1
  let q : ℤ := n + 1 - (S.val.card : ℤ)
  let q' : ℤ := n + 1 + 1 - (S.val.card : ℤ)
  let P := alternatingCechModulePresheaf.obj ((principalSubsetRestriction A r f J).X q)
  let Q := alternatingCechModulePresheaf.obj ((principalSubsetRestriction A r f J).X q')
  let L := alternatingCechComplex U P
  let L' := alternatingCechComplex U Q
  let e : (K.X (p : ℤ)).X q ≅ L.X p :=
    L.extendXIso ComplexShape.embeddingUpNat rfl
  let e' : (K.X (p : ℤ)).X q' ≅ L'.X p :=
    L'.extendXIso ComplexShape.embeddingUpNat rfl
  let v : AddCommGrpCat.of (P.obj
      (op (alternatingCechIntersection U (principalSubsetTuple r S)))) ⟶ H.obj (L.X p) :=
    AddCommGrpCat.ofHom (AddMonoidHom.single
      (fun t : Fin (p + 1) ↪o Fin r ↦ P.obj (op (alternatingCechIntersection U t)))
        (principalSubsetTuple r S))
  let v' : AddCommGrpCat.of (Q.obj
      (op (alternatingCechIntersection U (principalSubsetTuple r S)))) ⟶ H.obj (L'.X p) :=
    AddCommGrpCat.ofHom (AddMonoidHom.single
      (fun t : Fin (p + 1) ↪o Fin r ↦ Q.obj (op (alternatingCechIntersection U t)))
        (principalSubsetTuple r S))
  have hpq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ((p : ℤ), q) = n := by
    change (p : ℤ) + q = n
    dsimp [p, q]
    rw [Nat.cast_sub (by have := S.property.card_pos; omega)]
    push_cast
    omega
  have hpq' : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ((p : ℤ), q') = n + 1 := by
    change (p : ℤ) + q' = n + 1
    change (p : ℤ) + q = n at hpq
    dsimp [q, q'] at *
    omega
  change (((principalSubsetSectionTransport A r f (J.X q) S).hom ≫ v ≫
    H.map e.inv ≫ H.map (K.ιTotal (ComplexShape.up ℤ) (p : ℤ) q n hpq) ≫
      H.map (K.D₂ (ComplexShape.up ℤ) n (n + 1))) (s S)) =
    (((principalSubsetSectionTransport A r f (J.X q') S).hom ≫ v' ≫
      H.map e'.inv ≫ H.map (K.ιTotal (ComplexShape.up ℤ) (p : ℤ) q' (n + 1) hpq'))
        ((-1 : A) ^ p • (modulesSpecToSheaf.map (J.d q q')).hom.app (op (D S.val)) (s S)))
  with_unfolding_all
    simp only [← H.map_comp, HomologicalComplex₂.ι_D₂]
  with_unfolding_all
    rw [K.d₂_eq (ComplexShape.up ℤ) (p : ℤ)
      (show (ComplexShape.up ℤ).Rel q q' by change q + 1 = q'; dsimp [q, q']; omega)
      (n + 1) hpq']
  let R := SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) V ⋙
    (Scheme.Modules.overEquiv V).functor
  let g := R.map (J.d q q')
  let γ := alternatingCechModulePresheaf.map g
  let a := alternatingCechTermsMap U γ p
  have hkd : (K.X (p : ℤ)).d q q' = e.hom ≫ a ≫ e'.inv := by
    change (HomologicalComplex.extendMap (alternatingCechComplexMap U γ)
      ComplexShape.embeddingUpNat).f (p : ℤ) = _
    exact HomologicalComplex.extendMap_f _ _ rfl
  with_unfolding_all
    rw [hkd]
    simp only [ComplexShape.ε₂, Linear.comp_units_smul,
      Category.assoc, Iso.inv_hom_id_assoc]
  have ha (x : P.obj (op (alternatingCechIntersection U (principalSubsetTuple r S)))) :
      (H.map a) (v x) = v' ((γ.app
        (op (alternatingCechIntersection U (principalSubsetTuple r S)))).hom x) := by
    change (alternatingCechTermsMap U γ p).hom
      (Pi.single (principalSubsetTuple r S) x) =
        Pi.single (principalSubsetTuple r S) ((γ.app
          (op (alternatingCechIntersection U (principalSubsetTuple r S)))).hom x)
    funext t
    by_cases ht : t = principalSubsetTuple r S
    · subst t
      change (γ.app (op (alternatingCechIntersection U (principalSubsetTuple r S)))).hom
        ((Pi.single (M := fun t : Fin (p + 1) ↪o Fin r ↦
          P.obj (op (alternatingCechIntersection U t))) (principalSubsetTuple r S) x)
            (principalSubsetTuple r S)) = _
      simp only [Pi.single_eq_same]
    · change (γ.app (op (alternatingCechIntersection U t))).hom
        ((Pi.single (M := fun t : Fin (p + 1) ↪o Fin r ↦
          P.obj (op (alternatingCechIntersection U t))) (principalSubsetTuple r S) x) t) = _
      rw [Pi.single_eq_of_ne ht, map_zero, Pi.single_eq_of_ne ht]
  have hs (x : (modulesSpecToSheaf.obj (J.X q')).obj.obj (op (D S.val))) :
      (-1 : A) ^ p • x = ((p : ℤ).negOnePow : ℤ) • x := by
    rw [← Int.cast_smul_eq_zsmul A, Int.cast_negOnePow_natCast]
  change ((p : ℤ).negOnePow : ℤ) •
    ((H.map (e'.inv ≫ K.ιTotal (ComplexShape.up ℤ) (p : ℤ) q' (n + 1) hpq'))
      ((H.map a) (v ((principalSubsetSectionTransport A r f (J.X q) S).hom (s S))))) = _
  rw [ha]
  change ((p : ℤ).negOnePow : ℤ) •
    ((H.map (e'.inv ≫ K.ιTotal (ComplexShape.up ℤ) (p : ℤ) q' (n + 1) hpq'))
      (v' (g.app (alternatingCechIntersection U (principalSubsetTuple r S))
        ((principalSubsetSectionTransport A r f (J.X q) S).hom (s S))))) = _
  rw [← sectionTransport_natural A r f S (J.d q q') (s S)]
  rw [hs]
  with_unfolding_all
    simp only [map_zsmul]
  rfl

end AlgebraicGeometry
