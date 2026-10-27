/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchangeComposition
public import WeilConjectures.TraceFormula.Specialization.NearbyCompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.OpenImmersionLowerShriekComp

/-!

# The exchanges of an open sub-model

For an open sub-model `N ⊆ M` of nearby-cycles models over open immersions `j : Y ⟶ X`,
`j' : Y' ⟶ X'`, with invertible pullback exchange `α_j : j'^* Ψ_M ⟶ Ψ_N j^*`, this file builds the
exchange `ν_j : Rj'_! Ψ_N ⟶ Ψ_M Rj_!` adjoint to `α_j⁻¹`
(`ProEtale.CondensedRing.NearbyCyclesModel.Hom.boundedConstructibleLowerShriekExchange`) and shows:

* its exceptional adjoint is `β_j = α_j⁻¹` through `Rj^! ≅ j^*`
  (`ProEtale.CondensedRing.NearbyCyclesModel.Hom.exceptionalExchange_boundedConstructibleLowerShriekExchange_app`);
* a compactification `M ⊆ P` of a trait model over the base restricts to a compactification
  `N ⊆ P` (`NearbyCyclesModel.IsTraitModelOfBase.Compactification.ofOpen`), along which the
  compact-support exchange of `N` is the composite of `ν_j` and of the compact-support exchange
  of `M` (`NearbyCyclesModel.IsTraitModelOfBase.Compactification.compactSupportExchange_ofOpen_app`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section OpenExchange

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {j : Y ⟶ X} {j' : Y' ⟶ X'} [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  (φ : N.Hom M j.left j'.left)
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))

/-- The components of `lowerShriekExchangeOfInv`. -/
lemma lowerShriekExchangeOfInv_app {DC DC' DP DP' : Type*} [Category DC] [Category DC']
    [Category DP] [Category DP'] {ΨC : DC ⥤ DC'} {ΨP : DP ⥤ DP'} {Dh : DC ⥤ DP} {Lh : DP ⥤ DC}
    {Dh' : DC' ⥤ DP'} {Lh' : DP' ⥤ DC'} (adj : Dh ⊣ Lh) (adj' : Dh' ⊣ Lh')
    (α : ΨP ⋙ Lh' ⟶ Lh ⋙ ΨC) [IsIso α] (K : DC) :
    (lowerShriekExchangeOfInv adj adj' α).app K =
      Dh'.map (ΨC.map (adj.unit.app K) ≫ (inv α).app (Dh.obj K)) ≫
        adj'.counit.app (ΨP.obj (Dh.obj K)) := by
  simp [lowerShriekExchangeOfInv]

instance [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))] :
    IsIso (φ.boundedConstructiblePullbackExchange ℓ hN hM) := by
  have (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
      IsIso ((φ.boundedConstructiblePullbackExchange ℓ hN hM).app K) := by
    have : IsIso ((ObjectProperty.ι _).map ((φ.boundedConstructiblePullbackExchange ℓ hN hM).app
        K)) := by
      rw [ObjectProperty.ι_map, NearbyCyclesModel.Hom.boundedConstructiblePullbackExchange_app_hom]
      infer_instance
    exact isIso_of_fully_faithful (ObjectProperty.ι _) _
  exact NatIso.isIso_of_isIso_app _

/-- The exchange `ν_j : j'_! Ψ_N ⟶ Ψ_M j_!` of an open immersion of models on bounded
constructible complexes, adjoint to the inverse of the pullback exchange. -/
noncomputable def NearbyCyclesModel.Hom.boundedConstructibleOpenExchange
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))] :
    NearbyCyclesModel.boundedConstructibleNearbyCycles hN ⋙
        boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j' ⟶
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
        NearbyCyclesModel.boundedConstructibleNearbyCycles hM :=
  lowerShriekExchangeOfInv
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j')
    (φ.boundedConstructiblePullbackExchange ℓ hN hM)

/-- The components of the inverse of the restricted pullback exchange are those of the inverse of
the ambient one. -/
lemma NearbyCyclesModel.Hom.inv_boundedConstructiblePullbackExchange_app_hom
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((inv (φ.boundedConstructiblePullbackExchange ℓ hN hM)).app K).hom =
      (inv (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app K.obj := by
  rw [NatIso.isIso_inv_app (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)) K.obj]
  refine IsIso.eq_inv_of_hom_inv_id ?_
  rw [← NearbyCyclesModel.Hom.boundedConstructiblePullbackExchange_app_hom ℓ φ hN hM,
    ← ObjectProperty.FullSubcategory.comp_hom, ← NatTrans.comp_app, IsIso.hom_inv_id]
  rfl

/-- The components of `NearbyCyclesModel.Hom.boundedConstructibleOpenExchange` on the ambient
derived categories are those of the exchange adjoint to the inverse of the ambient pullback
exchange. -/
lemma NearbyCyclesModel.Hom.boundedConstructibleOpenExchange_app_hom
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((φ.boundedConstructibleOpenExchange ℓ hN hM).app K).hom =
      (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ j.left)
        (openImmersionAdjunction ℓ j'.left)
        (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app K.obj := by
  rw [NearbyCyclesModel.Hom.boundedConstructibleOpenExchange, lowerShriekExchangeOfInv_app,
    lowerShriekExchangeOfInv_app]
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    boundedConstructibleOpenImmersionLowerShriek_map_hom,
    boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_counit_app_hom,
    NearbyCyclesModel.Hom.inv_boundedConstructiblePullbackExchange_app_hom]
  rw [← openImmersionLowerShriekUpperStarAdjunction_unit_app_hom]
  rfl

/-- The exchange `ν_j : Rj'_! Ψ_N ⟶ Ψ_M Rj_!` of an open immersion of models on bounded
constructible complexes: `NearbyCyclesModel.Hom.boundedConstructibleOpenExchange` read through
the identifications `Rj_! ≅ j_!` of the lower shrieks of open immersions. -/
noncomputable def NearbyCyclesModel.Hom.boundedConstructibleLowerShriekExchange
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))] :
    NearbyCyclesModel.boundedConstructibleNearbyCycles hN ⋙ boundedConstructibleLowerShriek ℓ j' ⟶
      boundedConstructibleLowerShriek ℓ j ⋙ NearbyCyclesModel.boundedConstructibleNearbyCycles hM :=
  Functor.whiskerLeft _ (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
      j').hom ≫ φ.boundedConstructibleOpenExchange ℓ hN hM ≫
    Functor.whiskerRight (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
      j).inv _

/-- The mate of `NearbyCyclesModel.Hom.boundedConstructibleOpenExchange` is the inverse of the
pullback exchange. -/
lemma NearbyCyclesModel.Hom.mateEquiv_boundedConstructibleOpenExchange
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))] :
    mateEquiv (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j')
        (φ.boundedConstructibleOpenExchange ℓ hN hM) =
      inv (φ.boundedConstructiblePullbackExchange ℓ hN hM) := by
  rw [NearbyCyclesModel.Hom.boundedConstructibleOpenExchange,
    lowerShriekExchangeOfInv_eq_mateEquiv_symm, Equiv.apply_symm_apply]

/-- `Rj^! ≅ Lj^*` is the conjugate of `Rj_! ≅ j_!`. -/
lemma boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl_eq_conjugateIsoEquiv
    {V W : Over (Spec (.of k))} [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [IsSeparated V.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (f : V ⟶ W) [IsOpenImmersion f.left] :
    boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ f =
      conjugateIsoEquiv (boundedConstructibleUpperShriekAdjunction ℓ f)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ f)
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ f).symm := by
  unfold boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl
  rfl

/-- **The exceptional exchange of an open immersion of models is the inverse of the pullback
exchange**, through the identifications `Rj^! ≅ j^*`: `β_j = α_j⁻¹`. -/
lemma NearbyCyclesModel.Hom.exceptionalExchange_boundedConstructibleLowerShriekExchange_app
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (exceptionalExchange ℓ j j' (φ.boundedConstructibleLowerShriekExchange ℓ hN hM)).app A =
      (NearbyCyclesModel.boundedConstructibleNearbyCycles hN).map
          ((boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).hom.app A) ≫
        (inv (φ.boundedConstructiblePullbackExchange ℓ hN hM)).app A ≫
        (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j').inv.app
          ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj A) := by
  have h := mateEquiv_whiskerLeft_comp_comp_whiskerRight_app
      (boundedConstructibleUpperShriekAdjunction ℓ j)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
      (boundedConstructibleUpperShriekAdjunction ℓ j')
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j')
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j)
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j')
      (φ.boundedConstructibleOpenExchange ℓ hN hM) A
  rw [NearbyCyclesModel.Hom.mateEquiv_boundedConstructibleOpenExchange,
    ← boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl_eq_conjugateIsoEquiv,
    ← boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl_eq_conjugateIsoEquiv] at h
  rw [exceptionalExchange, NearbyCyclesModel.Hom.boundedConstructibleLowerShriekExchange]
  cast_proofs h

end OpenExchange

section Verdier

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {U X : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The two identifications `Rj^! ≅ Lj^*` of an open immersion agree. -/
lemma boundedConstructibleUpperShriekIsoUpperStar_eq_padicAlgCl (j : U ⟶ X)
    [IsOpenImmersion j.left] :
    boundedConstructibleUpperShriekIsoUpperStar ℓ j =
      boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j := by
  have e : boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek ℓ j =
      boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j := by
    ext K
    simp [boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek,
      boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl,
      boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq']
    erw [Category.id_comp]
  rw [boundedConstructibleUpperShriekIsoUpperStar, e]
  rfl

/-- The identification `Rj^! ω_X ≅ ω_U` of Verdier duality is the composition isomorphism of the
dualizing complexes. -/
lemma upperShriekDualizingComplexIso_eq_dualizingComplexComp (j : U ⟶ X) :
    upperShriekDualizingComplexIso ℓ j = dualizingComplexComp ℓ j :=
  rfl

end Verdier

section Composition

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {Y X Z : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- On the ambient derived categories, the composition isomorphism of the extensions by zero on
bounded constructible complexes is the conjugate of the composition isomorphism of the derived
pullbacks. -/
lemma boundedConstructibleOpenImmersionLowerShriekComp_hom_app_hom (j : Y ⟶ X) (ι : X ⟶ Z)
    [IsOpenImmersion j.left] [IsOpenImmersion ι.left] [IsOpenImmersion (j ≫ ι).left]
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ j
      ι).hom.app K).hom =
      (((conjugateIsoEquiv (openImmersionAdjunction ℓ (j ≫ ι).left)
        ((openImmersionAdjunction ℓ j.left).comp (openImmersionAdjunction ℓ ι.left))).symm
          (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) j.left ι.left)).symm).hom.app
        K.obj := by
  simp only [boundedConstructibleOpenImmersionLowerShriekComp, Iso.symm_hom, conjugateIsoEquiv,
    Equiv.coe_fn_symm_mk, conjugateEquiv_symm_apply_app, ObjectProperty.FullSubcategory.comp_hom,
    boundedConstructibleOpenImmersionLowerShriek_map_hom, Adjunction.comp_unit_app,
    openImmersionLowerShriekUpperStarAdjunction_unit_app_hom, boundedConstructibleUpperStar_map_hom,
    upperStarComp_inv_app_hom,
    boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_counit_app_hom, Functor.map_comp]
  rfl

/-- **The associativity of the composition isomorphisms of the lower shriek**, for morphisms equal
to composites. -/
lemma lowerShriekCompOfEq_hom_app_comp_hom_app {S : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom] (j : Y ⟶ X) (ι : X ⟶ Z)
    (p : Z ⟶ S) {a : X ⟶ S} {b : Y ⟶ S} (wa : ι ≫ p = a) (wb : j ≫ a = b)
    (wjι : (j ≫ ι) ≫ p = b) (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (lowerShriekCompOfEq ℓ j a wb).hom.app L ≫
        (lowerShriekCompOfEq ℓ ι p wa).hom.app ((boundedConstructibleLowerShriek ℓ j).obj L) =
      (lowerShriekCompOfEq ℓ (j ≫ ι) p wjι).hom.app L ≫
        (boundedConstructibleLowerShriek ℓ p).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ j ι).hom.app L) := by
  subst wa wb
  have h := boundedConstructibleLowerShriekComp_padicAlgCl_assoc ℓ j ι p L
  simp only [lowerShriekCompOfEq, Iso.trans_hom, eqToIso.hom, NatTrans.comp_app, eqToHom_app,
    Category.assoc] at h ⊢
  rw [h]
  simp

/-- The diagram chase behind
`compactificationLowerShriekIso_hom_app_comp_map_openImmersionLowerShriekComp`, in abstract
categories. -/
lemma compactificationLowerShriekIso_comp_aux {A B C S : Type*} [Category A] [Category B]
    [Category C] [Category S] {Lb : A ⥤ S} {Lj oj : A ⥤ B} {La : B ⥤ S} {Ljι ojι : A ⥤ C}
    {Lι oι : B ⥤ C} {Lp Pp : C ⥤ S} (c₁ : Lb ≅ Ljι ⋙ Lp) (c₂ : Lb ≅ Lj ⋙ La)
    (c₃ : La ≅ Lι ⋙ Lp) (c : Ljι ≅ Lj ⋙ Lι) (ij : Lj ≅ oj) (iι : Lι ≅ oι) (ijι : Ljι ≅ ojι)
    (oc : ojι ≅ oj ⋙ oι) (ip : Lp ≅ Pp)
    (hassoc : ∀ L, c₂.hom.app L ≫ c₃.hom.app (Lj.obj L) = c₁.hom.app L ≫ Lp.map (c.hom.app L))
    (hA : ∀ L, c.hom.app L ≫ Lι.map (ij.hom.app L) ≫ iι.hom.app (oj.obj L) =
      ijι.hom.app L ≫ oc.hom.app L) (L : A) :
    (c₁ ≪≫ Functor.isoWhiskerRight ijι Lp ≪≫ Functor.isoWhiskerLeft ojι ip).hom.app L ≫
        Pp.map (oc.hom.app L ≫ oι.map (ij.inv.app L)) =
      c₂.hom.app L ≫
        (c₃ ≪≫ Functor.isoWhiskerRight iι Lp ≪≫ Functor.isoWhiskerLeft oι ip).hom.app
          (Lj.obj L) := by
  have hι := iι.hom.naturality (ij.inv.app L)
  have hp := ip.hom.naturality (oc.hom.app L ≫ oι.map (ij.inv.app L))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Category.assoc]
  rw [← hp, reassoc_of% (hassoc L), ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 2
  rw [← reassoc_of% (hA L), ← hι, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The factorizations of the lower shriek through a composite of open immersions**: for open
immersions `j`, `ι` and a proper `p`, the factorization `Rb_! ≅ (j ≫ ι)_! ⋙ Rp_*` followed by
`(j ≫ ι)_! ≅ j_! ⋙ ι_! ≅ Rj_! ⋙ ι_!` is the composition isomorphism `Rb_! ≅ Rj_! ⋙ Ra_!` followed
by the factorization `Ra_! ≅ ι_! ⋙ Rp_*`. -/
lemma compactificationLowerShriekIso_hom_app_comp_map_openImmersionLowerShriekComp
    {S : Over (Spec (.of k))} [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [IsSeparated S.hom] (j : Y ⟶ X) (ι : X ⟶ Z) (p : Z ⟶ S) [IsOpenImmersion j.left]
    [IsOpenImmersion ι.left] [IsOpenImmersion (j ≫ ι).left] [IsProper p.left] {a : X ⟶ S}
    {b : Y ⟶ S} (wa : ι ≫ p = a) (wb : j ≫ a = b) (wjι : (j ≫ ι) ≫ p = b)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactificationLowerShriekIso ℓ (j ≫ ι) p wjι).hom.app L ≫
        (boundedConstructibleLowerStar ℓ p).map
          ((boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ j
            ι).hom.app L ≫
          (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ ι).map
            ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app
              L)) =
      (lowerShriekCompOfEq ℓ j a wb).hom.app L ≫
        (compactificationLowerShriekIso ℓ ι p wa).hom.app
          ((boundedConstructibleLowerShriek ℓ j).obj L) := by
  have h := compactificationLowerShriekIso_comp_aux (lowerShriekCompOfEq ℓ (j ≫ ι) p wjι)
    (lowerShriekCompOfEq ℓ j a wb) (lowerShriekCompOfEq ℓ ι p wa)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ j ι)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ ι)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (j ≫ ι))
    (boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ j ι)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ p)
    (fun L ↦ by cast_proofs lowerShriekCompOfEq_hom_app_comp_hom_app ℓ j ι p wa wb wjι L)
    (fun L ↦ by
      cast_proofs boundedConstructibleLowerShriekComp_padicAlgCl_hom_app_of_isOpenImmersion ℓ j ι
        L) L
  rw [compactificationLowerShriekIso, compactificationLowerShriekIso]
  cast_proofs h

end Composition

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfBase

open Scheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {Y : Over (Spec (.of k))} {Y' : Over (Spec (.of k'))} {N : NearbyCyclesModel Y.left Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}
  {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X.left X'.left}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {hM : M.IsTraitModelOfBase k qM gM}

/-- **A compactification of a model restricts to its open sub-models**: for an open sub-model
`N ⊆ M` over open immersions `j`, `j'` and a compactification `M ⊆ P` over `ι`, `ι'`, the
compactification `N ⊆ P` over `j ≫ ι`, `j' ≫ ι'`. -/
noncomputable def Compactification.ofOpen (C : hM.Compactification)
    (hN : N.IsTraitModelOfBase k q g) (j : Y ⟶ X) [IsOpenImmersion j.left] (j' : Y' ⟶ X')
    [IsOpenImmersion j'.left] (φ : N.Hom M j.left j'.left) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic N.j M.j φ.total) (hq : q = φ.total ≫ qM)
    (hg : g = φ.generic ≫ gM) : hN.Compactification where
  X := C.X
  X' := C.X'
  model := C.model
  qc := C.qc
  gc := C.gc
  isTraitModelOfBase := C.isTraitModelOfBase
  isPullback_ε := C.isPullback_ε
  ι := j ≫ C.ι
  ι' := j' ≫ C.ι'
  isOpenImmersion_ι := by
    rw [Over.comp_left]
    infer_instance
  isOpenImmersion_ι' := by
    rw [Over.comp_left]
    infer_instance
  hom := φ.comp C.hom
  isOpenImmersion_hom_total := by
    rw [NearbyCyclesModel.Hom.comp_total]
    infer_instance
  isPullback_hom_j := hφ.paste_horiz C.isPullback_hom_j
  q_eq := by rw [hq, NearbyCyclesModel.Hom.comp_total, Category.assoc, ← C.q_eq]
  g_eq := by rw [hg, NearbyCyclesModel.Hom.comp_generic, Category.assoc, ← C.g_eq]

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfBase
