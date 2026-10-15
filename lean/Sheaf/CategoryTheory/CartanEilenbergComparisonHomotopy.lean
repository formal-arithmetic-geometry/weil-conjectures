/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopy
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-!
# Homotopy uniqueness of Cartan--Eilenberg comparison lifts

Source: Stacks Project, Derived Categories, Tags 015I and 015K
(blueprint: lem-sp-cartan-eilenberg-comparison-homotopy).

Resolutions use the augmentation and resolution fields of
`exists_cartanEilenberg_resolution`. Extend the natural resolution index by zero
before forming total complexes. The filtration is by the second, resolution index.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option linter.unusedVariables false in
/-- Comparison lifts of homotopic complex maps have a total homotopy lowering
resolution degree by at most one.
Source: Stacks Project, Derived Categories, Tags 015I and 015K
(blueprint: lem-sp-cartan-eilenberg-comparison-homotopy).

Proof:
1. Set delta = phi - psi. The augmentation identities imply that delta lifts
   u - u', whose null-homotopy is the given s (Homotopy.equivSubZero).
2. Exactness of F preserves the augmented boundary, cycle and cohomology
   resolutions of I and their canonical short exact sequences. The corresponding
   resolutions of J have injective terms, by lem-sp-cartan-eilenberg-exists.
   Apply lem-sp-cartan-eilenberg-double-complex-homotopy to delta and s.
3. Its horizontal component s1 restricts to s on the augmentation; its vertical
   component s2 supplies the residual null-homotopy.
4. On each summand set H = s1 + (-1)^p s2. The component equations give
   Tot(phi) - Tot(psi) = dH + Hd. The horizontal component preserves resolution
   degree and the vertical component lowers it by one, so their sum factors
   through the second filtration step q-1 in degree n-1
   (def-sp-double-complex-total, def-sp-filtration).
When u = u', take Homotopy.ofEq of this equality, whose components are zero.
The same conclusion gives the final assertion without an additional hypothesis.
-/
theorem cartanEilenberg_comparison_homotopy
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (hK : ∀ p : ℤ, p < 0 → IsZero (K.X p))
    (hL : ∀ p : ℤ, p < 0 → IsZero (L.X p))
    (u u' : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (s : Homotopy u u')
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (hIbelow : ∀ p : ℤ, p < 0 → IsZero (I.X p))
    (hIcol : ∀ p : ℤ, QuasiIso (eI.f p))
    (hIinj : ∀ (p : ℤ) (q : ℕ), Injective ((I.X p).X q))
    (hIinj' : ∀ (p : ℤ) (q : ℕ),
      Injective ((I.cycles p).X q) ∧
      Injective ((image (I.d (p - 1) p)).X q) ∧
      Injective ((I.homology p).X q))
    (hIres : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eI p) ∧
      QuasiIso (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eI p))
    (J : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eJ : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ J)
    (hJbelow : ∀ p : ℤ, p < 0 → IsZero (J.X p))
    (hJcol : ∀ p : ℤ, QuasiIso (eJ.f p))
    (hJinj : ∀ (p : ℤ) (q : ℕ), Injective ((J.X p).X q))
    (hJinj' : ∀ (p : ℤ) (q : ℕ),
      Injective ((J.cycles p).X q) ∧
      Injective ((image (J.d (p - 1) p)).X q) ∧
      Injective ((J.homology p).X q))
    (hJres : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eJ p) ∧
      QuasiIso (image.map (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p) (eJ.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eJ p)) :
    let FI : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ) :=
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I
    let E := (ComplexShape.embeddingUpNat.extendFunctor B).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let FIZ : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) := E.obj FI
    let JZ : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) := E.obj J
    ∀ (φ ψ : FI ⟶ J),
      (∀ p : ℤ,
        F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).inv ≫
            (eI.f p).f 0) ≫ (φ.f p).f 0 =
          u.f p ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X p)).inv ≫
            (eJ.f p).f 0) →
      (∀ p : ℤ,
        F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).inv ≫
            (eI.f p).f 0) ≫ (ψ.f p).f 0 =
          u'.f p ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X p)).inv ≫
            (eJ.f p).f 0) →
      ∃ (tI : FIZ.HasTotal (ComplexShape.up ℤ)) (tJ : JZ.HasTotal (ComplexShape.up ℤ)),
        letI := tI
        letI := tJ
        ∃ H : Homotopy
          (HomologicalComplex₂.total.map (E.map φ) (ComplexShape.up ℤ))
          (HomologicalComplex₂.total.map (E.map ψ) (ComplexShape.up ℤ)),
          ∀ q n : ℤ,
            ∃ f : ((FIZ.secondFiltration n).step q : B) ⟶
              ((JZ.secondFiltration (n - 1)).step (q - 1) : B),
              f ≫ ((JZ.secondFiltration (n - 1)).step (q - 1)).arrow =
                ((FIZ.secondFiltration n).step q).arrow ≫ H.hom n (n - 1) := by
  classical
  let G := F.mapHomologicalComplex (ComplexShape.up ℕ)
  let GG := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let FK := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let a := (NatIso.mapHomologicalComplex
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0)
    (ComplexShape.up ℤ)).app K
  let eFI : ((CochainComplex.single₀ B).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj FK ⟶ GG.obj I := a.inv ≫ GG.map eI
  dsimp only
  intro φ ψ hφ hψ
  have hFIbelow (p : ℤ) (hp : p < 0) : IsZero ((GG.obj I).X p) :=
    G.map_isZero (hIbelow p hp)
  -- Transport the three augmented rows through the exact functor.
  have hFIres (p : ℤ) :
      QuasiIso (HomologicalComplex.cyclesMap eFI p) ∧
      QuasiIso (image.map (Arrow.homMk' (eFI.f (p - 1)) (eFI.f p)
        (eFI.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eFI p) := by
    let M := ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    let e := GG.map eI
    have hc : QuasiIso (HomologicalComplex.cyclesMap e p) := by
      have : QuasiIso (HomologicalComplex.cyclesMap eI p) := (hIres p).1
      rw [← quasiIso_iff_comp_right _ ((I.sc p).mapCyclesIso G).hom]
      change QuasiIso (ShortComplex.cyclesMap (G.mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor _ _ p).map eI)) ≫ _)
      rw [ShortComplex.mapCyclesIso_hom_naturality]
      change QuasiIso (((M.sc p).mapCyclesIso G).hom ≫
        (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (HomologicalComplex.cyclesMap eI p))
      infer_instance
    have hh : QuasiIso (HomologicalComplex.homologyMap e p) := by
      have : QuasiIso (HomologicalComplex.homologyMap eI p) := (hIres p).2.2
      rw [← quasiIso_iff_comp_right _ ((I.sc p).mapHomologyIso G).hom]
      change QuasiIso (ShortComplex.homologyMap (G.mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor _ _ p).map eI)) ≫ _)
      rw [ShortComplex.mapHomologyIso_hom_naturality]
      change QuasiIso (((M.sc p).mapHomologyIso G).hom ≫
        (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (HomologicalComplex.homologyMap eI p))
      infer_instance
    have hb : QuasiIso (image.map (Arrow.homMk' (e.f (p - 1)) (e.f p)
        (e.comm (p - 1) p))) := by
      let b := image.map (Arrow.homMk' (e.f (p - 1)) (e.f p) (e.comm (p - 1) p))
      let b₀ := image.map
        (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))
      have : QuasiIso b₀ := (hIres p).2.1
      have fac : b ≫ (PreservesImage.iso G (I.d (p - 1) p)).hom =
          (PreservesImage.iso G (M.d (p - 1) p)).hom ≫ G.map b₀ := by
        apply (cancel_mono (G.map (image.ι (I.d (p - 1) p)))).1
        rw [Category.assoc, PreservesImage.hom_comp_map_image_ι]
        change image.map (Arrow.homMk' (G.map (eI.f (p - 1))) (G.map (eI.f p))
          (e.comm (p - 1) p)) ≫ image.ι (G.map (I.d (p - 1) p)) = _
        erw [image.map_homMk'_ι]
        rw [Category.assoc, ← G.map_comp, image.map_homMk'_ι, G.map_comp,
          ← Category.assoc, PreservesImage.hom_comp_map_image_ι]
        rfl
      change QuasiIso b
      rw [← quasiIso_iff_comp_right _ (PreservesImage.iso G (I.d (p - 1) p)).hom,
        fac]
      infer_instance
    -- Precomposing the augmentation by its canonical single-complex isomorphism
    -- preserves all three quasi-isomorphisms.
    have hca : IsIso (HomologicalComplex.cyclesMap a.inv p) :=
      inferInstanceAs (IsIso ((HomologicalComplex.cyclesFunctor _ _ p).map a.inv))
    have hha : IsIso (HomologicalComplex.homologyMap a.inv p) :=
      inferInstanceAs (IsIso ((HomologicalComplex.homologyFunctor _ _ p).map a.inv))
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [eFI]
      rw [HomologicalComplex.cyclesMap_comp]
      change QuasiIso (HomologicalComplex.cyclesMap a.inv p ≫
        HomologicalComplex.cyclesMap e p)
      infer_instance
    · let r := Arrow.homMk' (a.inv.f (p - 1)) (a.inv.f p) (a.inv.comm (p - 1) p)
      have : IsIso r.left := inferInstanceAs (IsIso
        ((HomologicalComplex.eval _ _ (p - 1)).map a.inv))
      have : IsIso r.right := inferInstanceAs (IsIso
        ((HomologicalComplex.eval _ _ p).map a.inv))
      have : IsIso r := Arrow.isIso_of_isIso_left_of_isIso_right r
      have : IsIso (image.map r) := inferInstanceAs (IsIso (im.map r))
      have fac : image.map (Arrow.homMk' (eFI.f (p - 1)) (eFI.f p)
          (eFI.comm (p - 1) p)) = image.map r ≫
            image.map (Arrow.homMk' (e.f (p - 1)) (e.f p) (e.comm (p - 1) p)) := by
        rw [← image.map_comp]
        congr 1
      rw [fac]
      infer_instance
    · dsimp only [eFI]
      rw [HomologicalComplex.homologyMap_comp]
      infer_instance
  -- The supplied homotopy is a null-homotopy of the difference.
  have hs (p : ℤ) :
      (u - u').f p = s.hom p (p - 1) ≫ L.d (p - 1) p +
        FK.d p (p + 1) ≫ s.hom (p + 1) (p + 1 - 1) ≫
          eqToHom (congrArg L.X (Int.add_sub_cancel p 1)) := by
    have h := (Homotopy.equivSubZero s).comm p
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (p - 1) p by simp)] at h
    simpa [Homotopy.equivSubZero, FK, add_comm] using h
  have hδ (p : ℤ) :
      (eFI.f p).f 0 ≫ ((φ - ψ).f p).f 0 = (u - u').f p ≫ (eJ.f p).f 0 := by
    simp only [eFI, HomologicalComplex.comp_f, Category.assoc]
    change ((HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.up ℕ) 0).inv.app (K.X p)).f 0 ≫
        F.map ((eI.f p).f 0) ≫ ((φ - ψ).f p).f 0 = _
    rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    simp only [CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv]
    erw [Category.id_comp, F.map_id, Category.id_comp]
    simp only [HomologicalComplex.sub_f_apply, Preadditive.comp_sub,
      Preadditive.sub_comp]
    have hφp := hφ p
    have hψp := hψ p
    simp only [CochainComplex.single₀ObjXSelf, Iso.refl_inv] at hφp hψp
    erw [Category.id_comp, Category.id_comp] at hφp hψp
    rw [hφp, hψp]
  obtain ⟨tI, tJ, _, _, _, _, _, H, _, hfil⟩ :=
    cartanEilenberg_doubleComplex_homotopy B FK L (GG.obj I) J eFI eJ
      hFIbelow hJbelow hFIres hJres hJinj' (φ - ψ) (u - u')
      (fun p ↦ s.hom p (p - 1)) hs hδ
  refine ⟨tI, tJ, ?_⟩
  let := tI
  let := tJ
  let E := (ComplexShape.embeddingUpNat.extendFunctor B).mapHomologicalComplex
    (ComplexShape.up ℤ)
  -- Totalization is additive on maps; keep the homotopy components unchanged
  -- so that its filtration factorization can be reused verbatim.
  have hm : HomologicalComplex₂.total.map (E.map (φ - ψ)) (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map (E.map φ) (ComplexShape.up ℤ) -
        HomologicalComplex₂.total.map (E.map ψ) (ComplexShape.up ℤ) := by
    rw [E.map_sub]
    ext n p q hpq
    simp only [HomologicalComplex.sub_f_apply, Preadditive.comp_sub,
      HomologicalComplex₂.ιTotal_map]
    simp only [Preadditive.sub_comp]
  let H' : Homotopy
      (HomologicalComplex₂.total.map (E.map φ) (ComplexShape.up ℤ) -
        HomologicalComplex₂.total.map (E.map ψ) (ComplexShape.up ℤ)) 0 :=
    { hom := H.hom
      zero := H.zero
      comm := fun n ↦ by rw [← hm]; exact H.comm n }
  exact ⟨Homotopy.equivSubZero.symm H', hfil⟩

end CategoryTheory
