/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientHeartCommonStratification
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Algebra.DirectSum.Basic
import Sheaf.Paper.ConstructibleExtContinuity
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Ext out of a constructible sheaf commutes with sums of ind-constructible sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-ind-heart-ii,
node det-ind-heart-ii-sums (blueprint: det-ind-heart-ii-sums).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits DirectSum
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open CoproductsFromFiniteFiltered

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem preserves_coproduct_of_finite_subcoproducts
    {A D : Type*} [Category A] [Category D]
    (F : A ⥤ D) [HasFiniteCoproducts A] [PreservesFiniteCoproducts F]
    {S : Type*} (B : S → A) [HasCoproduct B]
    [HasColimitsOfShape (Finset (Discrete S)) A]
    [PreservesColimit (liftToFinsetObj (Discrete.functor B)) F] :
    PreservesColimit (Discrete.functor B) F := by
  classical
  let L := liftToFinsetObj (Discrete.functor B)
  let k := finiteSubcoproductsCocone B
  let hk := isColimitOfPreserves F (isColimitFiniteSubproductsCocone B)
  let hf (T : Finset (Discrete S)) :=
    isColimitOfPreserves F (coproductIsCoproduct (fun s : T ↦ B s.val.as))
  let t (d : Cocone (Discrete.functor B ⋙ F)) : Cocone (L ⋙ F) :=
    { pt := d.pt
      ι :=
        { app := fun T ↦ (hf T).desc
            { pt := d.pt, ι := Discrete.natTrans (fun s ↦ d.ι.app s.as.val) }
          naturality := by
            intro T U h
            apply (hf T).hom_ext
            rintro ⟨s⟩
            change F.map (Sigma.ι (fun j : T ↦ B j.val.as) s) ≫
              F.map (L.map h) ≫ _ = F.map (Sigma.ι (fun j : T ↦ B j.val.as) s) ≫
                _ ≫ 𝟙 _
            rw [Category.comp_id, ← Category.assoc, ← F.map_comp]
            have hs : Sigma.ι (fun j : T ↦ B j.val.as) s ≫ L.map h =
                Sigma.ι (fun j : U ↦ B j.val.as) ⟨s.val, h.down.down s.property⟩ := by
              simp [L, liftToFinsetObj]
            rw [hs]
            exact ((hf U).fac _ ⟨⟨s.val, h.down.down s.property⟩⟩).trans
              ((hf T).fac
                { pt := d.pt, ι := Discrete.natTrans (fun s ↦ d.ι.app s.as.val) }
                ⟨s⟩).symm } }
  apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct B)
  refine ⟨fun d ↦ hk.desc (t d), ?_, ?_⟩
  · intro d s
    let T : Finset (Discrete S) := {s}
    let j : T := ⟨s, by simp [T]⟩
    have h0 : Sigma.ι (fun j : T ↦ B j.val.as) j ≫ k.ι.app T =
        Sigma.ι B s.as := by
      simp [k, finiteSubcoproductsCocone, j]
    have hh := congrArg
      (fun f ↦ F.map (Sigma.ι (fun j : T ↦ B j.val.as) j) ≫ f)
      (hk.fac (t d) T)
    change F.map (Sigma.ι (fun j : T ↦ B j.val.as) j) ≫
      F.map (k.ι.app T) ≫ hk.desc (t d) =
      F.map (Sigma.ι (fun j : T ↦ B j.val.as) j) ≫ (t d).ι.app T at hh
    rw [← Category.assoc, ← F.map_comp, h0] at hh
    exact hh.trans ((hf T).fac
      { pt := d.pt, ι := Discrete.natTrans (fun s ↦ d.ι.app s.as.val) } ⟨j⟩)
  · intro d m hm
    apply hk.hom_ext
    intro T
    apply (hf T).hom_ext
    rintro ⟨s⟩
    change F.map (Sigma.ι (fun j : T ↦ B j.val.as) s) ≫
      F.map (k.ι.app T) ≫ m =
      F.map (Sigma.ι (fun j : T ↦ B j.val.as) s) ≫
        F.map (k.ι.app T) ≫ hk.desc (t d)
    have hfac : F.map (k.ι.app T) ≫ hk.desc (t d) = (t d).ι.app T :=
      hk.fac (t d) T
    rw [hfac, ← Category.assoc, ← F.map_comp]
    have h0 : Sigma.ι (fun j : T ↦ B j.val.as) s ≫ k.ι.app T =
        Sigma.ι B s.val.as := by
      simp [k, finiteSubcoproductsCocone]
    rw [h0]
    exact (hm s.val).trans ((hf T).fac
      { pt := d.pt, ι := Discrete.natTrans (fun s ↦ d.ι.app s.as.val) } ⟨s⟩).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem directSum_bijective_of_preserves
    {A : Type*} [Category A] {S : Type w}
    (B : S → A) (c : Cofan B) (hc : IsColimit c)
    (F : A ⥤ AddCommGrpCat.{w}) [PreservesColimit (Discrete.functor B) F] :
    Function.Bijective
      (@DirectSum.toAddMonoid S _ _ (Classical.decEq S) _ _
        (fun s ↦ AddCommGrpCat.Hom.hom (F.map (c.inj s)))) := by
  classical
  let d : Cocone (Discrete.functor B ⋙ F) :=
    { pt := AddCommGrpCat.of (⨁ s, F.obj (B s))
      ι := Discrete.natTrans (fun s ↦
        AddCommGrpCat.ofHom (DirectSum.of (fun s ↦ F.obj (B s)) s.as)) }
  let hd : IsColimit d :=
    { desc := fun t ↦ AddCommGrpCat.ofHom
        (DirectSum.toAddMonoid (fun s ↦ (t.ι.app ⟨s⟩).hom))
      fac := by
        intro t s
        ext x
        exact DirectSum.toAddMonoid_of (β := fun s ↦ ↥(F.obj (B s))) (γ := ↥t.pt)
          (fun s ↦ (t.ι.app ⟨s⟩).hom) s.as x
      uniq := by
        intro t m h
        apply AddCommGrpCat.hom_ext
        apply DirectSum.addHom_ext
        intro s x
        simpa [d] using congrArg (fun f ↦ f.hom x) (h ⟨s⟩) }
  let e := hd.coconePointUniqueUpToIso (isColimitOfPreserves F hc)
  exact ConcreteCategory.bijective_of_isIso e.hom

/-- Ext out of a constructible module sheaf preserves arbitrary coproducts of
ind-constructible module sheaves.
Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-ind-heart-ii,
node det-ind-heart-ii-sums (blueprint: det-ind-heart-ii-sums).

Proof:
1. View the ambient category as sheaves of modules over the commutative ring sheaf
   `Λ_X`; its module-object construction is `CategoryTheory.Mod`.  For every finite
   subfamily `T ⊆ S`, the coproduct is a biproduct.  The inclusions and projections
   satisfy the two biproduct identities, so postcomposition gives an additive
   isomorphism from the finite direct sum of Ext groups to the Ext group of the
   finite coproduct, with inverse given by postcomposition with the projections.
   These identities hold for degree-zero complexes in the derived category and after
   every integer shift.
2. The finite subsets of `S`, ordered by inclusion, form a small filtered category,
   including the empty subset.  The coproduct over `S` is the filtered colimit of the
   finite subcoproducts, and the same is true in abelian groups for the Ext groups.
   The required colimits exist in the ambient module category.
3. Apply the constructible Ext-continuity statement to this filtered diagram, the
   constructible source `C`, and the chosen coefficient ring.  It identifies the
   filtered colimit of the finite comparisons with the comparison for the full
   coproduct.  The finite inverses are compatible with the transition maps, so they
   induce an inverse on colimits.  On the `s`-th summand this composite is exactly
   postcomposition with the shifted coprojection, which is the displayed map.
-/
theorem det_ind_heart_ii_sums
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ)
    (C : CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (hC : IsConstantModelConstructible (coefficientHeartRingObj R) X C)
    (q : ℤ) (S : Type (u + 1))
    (B : S → CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (hB : ∀ s : S, ObjectProperty.ind
      (IsConstantModelConstructible (coefficientHeartRingObj R) X) (B s))
    (c : Cofan B) (hc : IsColimit c) :
    Function.Bijective
      (@DirectSum.toAddMonoid S _ _ (Classical.decEq S) _ _ (fun s : S ↦
        Preadditive.rightComp ((DerivedCategory.singleFunctor _ 0).obj C)
          ((shiftFunctor _ q).map ((DerivedCategory.singleFunctor _ 0).map (c.inj s)))) :
        (⨁ s : S,
          ((DerivedCategory.singleFunctor _ 0).obj C ⟶
            (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj (B s)))) →+
          ((DerivedCategory.singleFunctor _ 0).obj C ⟶
            (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj c.pt))) := by
  classical
  have _ := hB
  let A := CategoryTheory.Mod
    (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (coefficientHeartRingObj R) X)
  let F : A ⥤ AddCommGrpCat.{u + 1} :=
    DerivedCategory.singleFunctor A 0 ⋙ shiftFunctor _ q ⋙
      preadditiveCoyoneda.obj (Opposite.op ((DerivedCategory.singleFunctor A 0).obj C))
  have : HasCoproduct B := ⟨⟨c, hc⟩⟩
  let M := liftToFinsetObj (Discrete.functor B)
  have hi : IsIso (colimit.desc _ (F.mapCocone (colimit.cocone M))) :=
    constructible_sheaf_ext_continuity ℓ E R hR X C hC M
      (colimit.cocone M) (colimit.isColimit M) q
  have : IsIso ((colimit.isColimit (M ⋙ F)).desc
      (F.mapCocone (colimit.cocone M))) := by
    convert hi using 1 <;> rfl
  have : PreservesColimit M F :=
    preservesColimit_of_preserves_colimit_cocone (colimit.isColimit M)
      (IsColimit.ofPointIso (colimit.isColimit (M ⋙ F)))
  have : PreservesColimit (Discrete.functor B) F :=
    preserves_coproduct_of_finite_subcoproducts F B
  exact directSum_bijective_of_preserves B c hc F

end AlgebraicGeometry.ProEtale
