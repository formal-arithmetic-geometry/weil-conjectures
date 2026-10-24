/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence
public import WeilConjectures.TraceFormula.Dualizing

/-!

# The trace of the dualizing complexes along the compactly supported direct image

For a morphism `a : A ⟶ B` of separated `k`-schemes of finite type, the *trace*
`t_a : Ra_! ω_A ⟶ ω_B` (`ProEtale.CondensedRing.lowerShriekDualizingComplexTrace`) is the exceptional
adjoint of `ω_A ≅ Ra^! ω_B`. Its adjoint along the structure morphism of `B` is the composition
isomorphism followed by the counit of `A`
(`ProEtale.CondensedRing.lowerShriek_map_lowerShriekDualizingComplexTrace_comp_counit`), and the
traces are compatible with composition: `t_{a ≫ b} = t_b ∘ Rb_! t_a`
(`ProEtale.CondensedRing.lowerShriekDualizingComplexTrace_comp`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- The counit of a composite adjunction through the conjugate composition isomorphisms:
```
Lp La Rap N ⟶ Lp La Ra Rp N ⟶ Lp Rp N ⟶ N
     ‖                                  ‖
Lp La Rap N ⟶ Lap Rap N ─────────────▶ N
```
for `Rap ≅ Rp ⋙ Ra` the conjugate of `Lap ≅ La ⋙ Lp`. -/
lemma Adjunction.map_map_conjugateIsoEquiv_comp_counit {CA CB CC : Type*} [Category CA]
    [Category CB] [Category CC] {La : CA ⥤ CB} {Ra : CB ⥤ CA} {Lp : CB ⥤ CC} {Rp : CC ⥤ CB}
    {Lap : CA ⥤ CC} {Rap : CC ⥤ CA} (Aa : La ⊣ Ra) (Ap : Lp ⊣ Rp) (Aap : Lap ⊣ Rap)
    (c : Lap ≅ La ⋙ Lp) (N : CC) :
    Lp.map (La.map ((conjugateIsoEquiv Aap (Aa.comp Ap) c.symm).hom.app N) ≫
        Aa.counit.app (Rp.obj N)) ≫ Ap.counit.app N =
      c.inv.app (Rap.obj N) ≫ Aap.counit.app N := by
  have h := conjugateEquiv_counit Aap (Aa.comp Ap) c.inv N
  simp only [Functor.comp_map, Adjunction.comp_counit_app, Functor.comp_obj] at h
  rw [Functor.map_comp, Category.assoc]
  exact h

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {A B C : Over (Spec (.of k))}
  [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]

/-- The *trace* `t_a : Ra_! ω_A ⟶ ω_B` of the dualizing complexes along a morphism `a`: the
exceptional adjoint of `ω_A ≅ Ra^! ω_B`. For proper `a` it is
`ProEtale.CondensedRing.lowerStarDualizingComplexTrace` read through `Ra_! ≅ Ra_*`. -/
noncomputable def lowerShriekDualizingComplexTrace (a : A ⟶ B) :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ a).obj
        (dualizingComplex' ℓ A) ⟶ dualizingComplex' ℓ B :=
  (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ a).map
      (dualizingComplexComp ℓ a).inv ≫
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ a).counit.app _

lemma lowerShriek_map_eqToHom_comp_counit {r r' : A ⟶ B} (h : r = r')
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ r).map
        (eqToHom (congrArg (fun s ↦
          (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ s).obj N) h.symm)) ≫
      (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ r).counit.app N =
    eqToHom (by subst h; rfl) ≫
      (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ r').counit.app N := by
  subst h
  simp

/-- The adjoint of the trace `t_a` along the structure morphism `a_B` of `B`:
`Ra_{B!} t_a ≫ ε = R(a ≫ a_B)_! ≅ Ra_{A!}` followed by the counit. -/
lemma lowerShriek_map_lowerShriekDualizingComplexTrace_comp_counit (a : A ⟶ B) :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint B)).map
        (lowerShriekDualizingComplexTrace ℓ a) ≫
      (boundedConstructibleUpperShriekAdjunction _ ℓ (toPoint B)).counit.app (𝟙_ _) =
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a (toPoint B)).inv.app
        (dualizingComplex' ℓ A) ≫
      eqToHom (by rw [comp_toPoint]; rfl) ≫
      (boundedConstructibleUpperShriekAdjunction _ ℓ (toPoint A)).counit.app (𝟙_ _) := by
  have hP := Adjunction.map_map_conjugateIsoEquiv_comp_counit
    (boundedConstructibleUpperShriekAdjunction _ ℓ a)
    (boundedConstructibleUpperShriekAdjunction _ ℓ (toPoint B))
    (boundedConstructibleUpperShriekAdjunction _ ℓ (a ≫ toPoint B))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a (toPoint B)) (𝟙_ _)
  have hn := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a (toPoint B)).inv.naturality
    (eqToHom (congrArg (fun s ↦
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ s).obj (𝟙_ _))
        (comp_toPoint a).symm))
  have he := lowerShriek_map_eqToHom_comp_counit ℓ (comp_toPoint a) (𝟙_ _)
  simp only [Functor.comp_map] at hn
  simp only [lowerShriekDualizingComplexTrace, dualizingComplexComp,
    boundedConstructibleUpperShriekComp_padicAlgCl, Iso.trans_inv, Iso.symm_inv, Iso.app_hom,
    eqToIso.inv, Functor.map_comp, Category.assoc] at hP ⊢
  rw [hP, reassoc_of% hn, he]

lemma lowerShriek_map_comp_eqToHom {r r' : A ⟶ B} (h : r = r')
    {M N : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : M ⟶ N) :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ r).map φ ≫
        eqToHom (congrArg (fun s ↦
          (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ s).obj N) h) =
      eqToHom (congrArg (fun s ↦
          (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ s).obj M) h) ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ r').map φ := by
  subst h
  simp

lemma lowerShriekComp_hom_app_comp_eqToHom {r r' : B ⟶ C} (h : r = r') (a : A ⟶ B)
    (M : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a r).hom.app M ≫ eqToHom (by rw [h]) =
      eqToHom (by rw [h]) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a r').hom.app M := by
  subst h
  simp

/-- **The trace is compatible with composition**: `t_{a ≫ b} = t_b ∘ Rb_! t_a`, read through
`R(a ≫ b)_! ≅ Ra_! ⋙ Rb_!`. -/
theorem lowerShriekDualizingComplexTrace_comp (a : A ⟶ B) (b : B ⟶ C) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a b).hom.app (dualizingComplex' ℓ A) ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ b).map
          (lowerShriekDualizingComplexTrace ℓ a) ≫ lowerShriekDualizingComplexTrace ℓ b =
      lowerShriekDualizingComplexTrace ℓ (a ≫ b) := by
  apply ((boundedConstructibleUpperShriekAdjunction _ ℓ (toPoint C)).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have pa := lowerShriek_map_lowerShriekDualizingComplexTrace_comp_counit ℓ a
  have pb := lowerShriek_map_lowerShriekDualizingComplexTrace_comp_counit ℓ b
  have pab := lowerShriek_map_lowerShriekDualizingComplexTrace_comp_counit ℓ (a ≫ b)
  have hn := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ b (toPoint C)).inv.naturality
    (lowerShriekDualizingComplexTrace ℓ a)
  simp only [Functor.comp_map] at hn
  have he := lowerShriek_map_comp_eqToHom ℓ (comp_toPoint b) (lowerShriekDualizingComplexTrace ℓ a)
  have hc := lowerShriekComp_hom_app_comp_eqToHom ℓ (comp_toPoint b) a (dualizingComplex' ℓ A)
  have hassoc := boundedConstructibleLowerShriekComp_padicAlgCl_assoc ℓ a b (toPoint C)
    (dualizingComplex' ℓ A)
  have hassoc' : (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      (toPoint C)).map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ a b).hom.app
        (dualizingComplex' ℓ A)) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ b (toPoint C)).inv.app
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ a).obj
          (dualizingComplex' ℓ A)) =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (a ≫ b) (toPoint C)).inv.app
          (dualizingComplex' ℓ A) ≫ eqToHom (by rw [Category.assoc]) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a (b ≫ toPoint C)).hom.app
          (dualizingComplex' ℓ A) := by
    rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ (a ≫ b)
      (toPoint C)).hom.app (dualizingComplex' ℓ A)), reassoc_of% hassoc]
    simp
  rw [pb, reassoc_of% hn, reassoc_of% he, pa, pab, reassoc_of% hassoc', reassoc_of% hc, Iso.hom_inv_id_app_assoc, eqToHom_trans_assoc,
    eqToHom_trans_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
