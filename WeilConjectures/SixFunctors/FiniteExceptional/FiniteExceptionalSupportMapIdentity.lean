/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalSupportMapCocycle
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison

/-! Identity normalization of finite exceptional compact-support comparisons.

Source: the equal-index specialization of the quotient cocycle in
`lem-sf-finite-exceptional-quotient-coherence`.
(blueprint: lem-sf-finite-exceptional-quotient-coherence)

Proof: specialize the quotient cocycle at m = n = t and identify every scalar
associator with the tensor identity unitor. Conjugate the resulting component of
q by the source and target `selfReduction` unitors. The conjugated endomorphism is
idempotent, while q is an isomorphism by the compact-support comparison
construction; composing the idempotence equation with its inverse gives that the
endomorphism is the identity. Undo the conjugation, rewrite the inverse unitor as
the chosen `selfReduction.inv`, and obtain the displayed component formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteExceptional

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
  [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (c : Compactification f)

private theorem unit_of_cocycle
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (U : C ⥤ C) (V : D ⥤ D)
    (u : U ≅ 𝟭 C) (v : V ≅ 𝟭 D) (q : F ⋙ V ≅ U ⋙ F)
    (h : ∀ K : C, V.map (q.hom.app K) ≫ q.hom.app (U.obj K) ≫
      F.map (U.map (u.hom.app K)) = V.map (v.hom.app (F.obj K)) ≫ q.hom.app K)
    (K : C) : q.hom.app K ≫ F.map (u.hom.app K) = v.hom.app (F.obj K) := by
  let : V.Faithful := Functor.Faithful.of_iso v.symm
  apply V.map_injective
  apply (cancel_mono (q.hom.app K)).mp
  have hc := h K
  have hn := q.hom.naturality (u.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn] at hc
  simpa only [Functor.map_comp, Functor.id_obj, Category.assoc] using hc

private theorem lifted_unit
    {C : Type*} [Category* C] (P : ObjectProperty C) (U : C ⥤ C)
    (hP : ∀ K : P.FullSubcategory, P (U.obj K.obj))
    (u : U ≅ 𝟭 C) (a : U ⋙ U ≅ U)
    (ha : ∀ K : C, a.hom.app K = U.map (u.hom.app K)) (K : P.FullSubcategory) :
    let Q := P.lift (P.ι ⋙ U) hP
    let r : Q ⋙ Q ≅ Q := Functor.fullyFaithfulCancelRight P.ι
      (Functor.isoWhiskerLeft P.ι a)
    let v : Q ≅ 𝟭 _ := Functor.fullyFaithfulCancelRight P.ι
      (Functor.isoWhiskerLeft P.ι u)
    r.hom.app K = Q.map (v.hom.app K) := by
  dsimp only
  apply P.ι.map_injective
  rw [ObjectProperty.ι_obj_lift_map, Functor.comp_map]
  simp only [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, ObjectProperty.ι_obj]
  exact ha K.obj

private theorem cancel_mapped_unit
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {U : C ⥤ C} (u : U ≅ 𝟭 C) (K : C) {N : D}
    (a : N ⟶ F.obj (U.obj K)) (b : N ⟶ F.obj K)
    (h : a ≫ F.map (u.hom.app K) = b) :
    a = b ≫ F.map (u.inv.app K) := by
  calc
    a = a ≫ (F.map (u.hom.app K) ≫ F.map (u.inv.app K)) := by
      rw [← F.map_comp, Iso.hom_inv_id_app, F.map_id, Category.comp_id]
    _ = _ := by rw [← Category.assoc, h]

private theorem scalar_lifted_unit {T : Scheme.{u}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (a : R ⟶ R)
    (ha : a = 𝟙 R) (hc : a ≫ a = a)
    (P : ObjectProperty (reductionDerivedCategory T R))
    (hP : ∀ K : P.FullSubcategory, P ((pbcDerivedExtend a).obj K.obj))
    (K : P.FullSubcategory) :
    let Q := P.lift (P.ι ⋙ pbcDerivedExtend a) hP
    let r : Q ⋙ Q ≅ Q := Functor.fullyFaithfulCancelRight P.ι
      (Functor.isoWhiskerLeft P.ι (PurCompactSupport.tensorComposition a a a hc))
    let v : Q ≅ 𝟭 _ := Functor.fullyFaithfulCancelRight P.ι
      (Functor.isoWhiskerLeft P.ι
        (eqToIso (congrArg (fun a ↦ pbcDerivedExtend a) ha) ≪≫
          PurCompactSupport.tensorIdentity R))
    r.hom.app K = Q.map (v.hom.app K) := by
  exact lifted_unit P (pbcDerivedExtend a) hP _ _
    (PurCompactSupport.tensorComposition_identity_left_of_eq R a ha hc) K

private theorem self_reassoc (T : Scheme.{u}) (n : ℕ)
    (K : (domain l E T n).FullSubcategory) :
    (reassoc l E T (le_refl n) (le_refl n)).hom.app K =
      (Q l E T (le_refl n)).map ((selfReduction l E T n).hom.app K) := by
  exact scalar_lifted_unit _ _ (quotient_id l E T n)
    (quotient_comp l E T (le_refl n) (le_refl n)) (domain l E T n)
    (reduction_preserves l E T (le_refl n)) K

private theorem support_map_unit (n : ℕ) (K : (domain l E X n).FullSubcategory) :
    (q l E D hl f c (le_refl n)).hom.app K ≫
      (F l E D hl f c n).map ((selfReduction l E X n).hom.app K) =
        (selfReduction l E Y n).hom.app ((F l E D hl f c n).obj K) := by
  apply unit_of_cocycle (F l E D hl f c n) (Q l E X (le_refl n))
    (Q l E Y (le_refl n)) (selfReduction l E X n) (selfReduction l E Y n)
    (q l E D hl f c (le_refl n))
  intro M
  have hc := support_map_cocycle l E D hl f c (le_refl n) (le_refl n) M
  rw [self_reassoc l E X n M,
    self_reassoc l E Y n ((F l E D hl f c n).obj M)] at hc
  exact hc

/-- The equal-level compact-support comparison is normalized by the tensor unit.
Source: blueprint lem-sf-finite-exceptional-quotient-coherence, proof paragraph 2.
-/
theorem support_map_identity (n : ℕ) :
    ∀ (L : (domain l E Y n).FullSubcategory),
      (q l E D hl f c (le_refl n)).hom.app ((G l E D hl f c n).obj L) =
        (selfReduction l E Y n).hom.app
          ((F l E D hl f c n).obj ((G l E D hl f c n).obj L)) ≫
          (F l E D hl f c n).map
            ((selfReduction l E X n).inv.app ((G l E D hl f c n).obj L)) := by
  intro L
  exact cancel_mapped_unit (F l E D hl f c n) (selfReduction l E X n)
    ((G l E D hl f c n).obj L) _ _
    (support_map_unit l E D hl f c n ((G l E D hl f c n).obj L))

end WeilConjectures.FiniteExceptional
