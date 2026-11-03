/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedAffineLineOrdinaryCohomology
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierCharacters
import WeilConjectures.AlgebraicGeometry.AffineLineCondensedCohomology
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ForgetRightDerivedLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedConnectedCoefficientCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Constant cohomology of a nonzero linear Artin–Schreier cover

Source: latest blueprint lem-fd-cohomology-affine-line-character, the finite-cover
comparison and the coordinate identification with the affine line.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierTrace

/-- Lift a specified root by the quotient and pullback universal properties. -/
private theorem linear_cover_root_lift (n : ℕ) (X : Scheme.{u}) (f : Γ(X, ⊤))
    (T : Scheme.{u}) (x : T ⟶ X) (t : Γ(T, ⊤))
    (ht : t ^ n - t = x.appTop f) :
    ∃ s : Over.mk x ⟶ artinSchreierCover n X f,
      s.left.appTop (artinSchreierCoverCoordinate n X f) = t := by
  let R := AdjoinRoot (artinSchreierCoverPolynomial n X f)
  have hroot : (artinSchreierCoverPolynomial n X f).eval₂ x.appTop.hom t = 0 := by
    simp only [artinSchreierCoverPolynomial, Polynomial.eval₂_sub,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, ht, sub_self]
  let φ : R →+* Γ(T, ⊤) := AdjoinRoot.lift x.appTop.hom t hroot
  let g : T ⟶ Spec (.of R) :=
    ΓSpec.adjunction.homEquiv T (.op (.of R)) (CommRingCat.ofHom φ).op
  have hg : (Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop = CommRingCat.ofHom φ :=
    ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _
  let α : Γ(X, ⊤) ⟶ CommRingCat.of R := CommRingCat.ofHom (algebraMap _ _)
  have hc : x ≫ X.toSpecΓ = g ≫ Spec.map α := by
    apply ext_to_Spec
    change (Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ X.toSpecΓ.appTop ≫ x.appTop =
      (Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ (Spec.map α).appTop ≫ g.appTop
    rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, hg]
    apply CommRingCat.hom_ext
    ext r
    exact (AdjoinRoot.lift_of hroot).symm
  let s : Over.mk x ⟶ artinSchreierCover n X f :=
    Over.homMk (pullback.lift x g hc) (by
      change pullback.lift x g hc ≫ pullback.fst X.toSpecΓ (Spec.map α) = x
      exact pullback.lift_fst _ _ _)
  refine ⟨s, ?_⟩
  change (pullback.lift x g hc).appTop
    ((pullback.snd X.toSpecΓ (Spec.map α)).appTop
      ((Scheme.ΓSpecIso (.of R)).inv (AdjoinRoot.root _))) = t
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_snd]
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop) (AdjoinRoot.root _) = t
  rw [hg]
  exact AdjoinRoot.lift_root hroot

private theorem linear_cover_hom_ext (n : ℕ) (X : Scheme.{u}) (f : Γ(X, ⊤))
    (Z : Scheme.{u}) (r s : Z ⟶ (artinSchreierCover n X f).left)
    (hb : r ≫ (artinSchreierCover n X f).hom =
      s ≫ (artinSchreierCover n X f).hom)
    (ht : r.appTop (artinSchreierCoverCoordinate n X f) =
      s.appTop (artinSchreierCoverCoordinate n X f)) : r = s := by
  let R := AdjoinRoot (artinSchreierCoverPolynomial n X f)
  let α : Γ(X, ⊤) ⟶ CommRingCat.of R := CommRingCat.ofHom (algebraMap _ _)
  let π := pullback.snd X.toSpecΓ (Spec.map α)
  have hb' : (r ≫ π) ≫ Spec.map α = (s ≫ π) ≫ Spec.map α := by
    have hc : r ≫ pullback.fst X.toSpecΓ (Spec.map α) ≫ X.toSpecΓ =
        s ≫ pullback.fst X.toSpecΓ (Spec.map α) ≫ X.toSpecΓ := by
      have h := congrArg (fun g ↦ g ≫ X.toSpecΓ) hb
      change (r ≫ pullback.fst X.toSpecΓ (Spec.map α)) ≫ X.toSpecΓ =
        (s ≫ pullback.fst X.toSpecΓ (Spec.map α)) ≫ X.toSpecΓ at h
      simpa only [Category.assoc] using h
    change r ≫ pullback.snd X.toSpecΓ (Spec.map α) ≫ Spec.map α =
      s ≫ pullback.snd X.toSpecΓ (Spec.map α) ≫ Spec.map α
    simpa only [pullback.condition] using hc
  apply pullback.hom_ext hb
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  apply AdjoinRoot.ringHom_ext
  · ext b
    change (α ≫ (Scheme.ΓSpecIso (.of R)).inv ≫ (r ≫ π).appTop) b =
      (α ≫ (Scheme.ΓSpecIso (.of R)).inv ≫ (s ≫ π).appTop) b
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.ΓSpecIso_inv_naturality_assoc]
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hb']
  · exact ht

private theorem linear_cover_coordinate_relation (n : ℕ) (X : Scheme.{u})
    (f : Γ(X, ⊤)) :
    artinSchreierCoverCoordinate n X f ^ n - artinSchreierCoverCoordinate n X f =
      (artinSchreierCover n X f).hom.appTop f := by
  let R := AdjoinRoot (artinSchreierCoverPolynomial n X f)
  let α : Γ(X, ⊤) ⟶ CommRingCat.of R := CommRingCat.ofHom (algebraMap _ _)
  let π := (artinSchreierCover n X f).hom
  let s := pullback.snd X.toSpecΓ (Spec.map α)
  let θ : R →+* Γ((artinSchreierCover n X f).left, ⊤) :=
    s.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  have hr : AdjoinRoot.root (artinSchreierCoverPolynomial n X f) ^ n -
      AdjoinRoot.root (artinSchreierCoverPolynomial n X f) =
        algebraMap Γ(X, ⊤) R f := by
    rw [AdjoinRoot.algebraMap_eq]
    apply sub_eq_zero.mp
    have hh := AdjoinRoot.eval₂_root (artinSchreierCoverPolynomial n X f)
    change (Polynomial.X ^ n - Polynomial.X - Polynomial.C f).eval₂
      (AdjoinRoot.of (artinSchreierCoverPolynomial n X f))
      (AdjoinRoot.root (artinSchreierCoverPolynomial n X f)) = 0 at hh
    simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] using hh
  have hc : π.appTop = α ≫ (Scheme.ΓSpecIso (.of R)).inv ≫ s.appTop := by
    have h := congrArg Scheme.Hom.appTop
      (pullback.condition (f := X.toSpecΓ) (g := Spec.map α))
    change X.toSpecΓ.appTop ≫ π.appTop = (Spec.map α).appTop ≫ s.appTop at h
    have h' := congrArg (fun b ↦ (Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ b) h
    simpa only [Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Category.assoc] using h'
  have h := congrArg θ hr
  rw [map_sub, map_pow] at h
  change artinSchreierCoverCoordinate n X f ^ n - artinSchreierCoverCoordinate n X f =
    (α ≫ (Scheme.ΓSpecIso (.of R)).inv ≫ s.appTop) f at h
  rw [← hc] at h
  exact h

private theorem nonzero_linear_cover_iso
    (n : ℕ) (K : Type u) [Field K] (a : K) (ha : a ≠ 0)
    (f : Γ(AffineSpace PUnit (Spec (.of K)), ⊤))
    (hf : f = scalar K (AffineSpace PUnit (Spec (.of K))) a *
      AffineSpace.coord (Spec (.of K)) PUnit.unit) :
    ∃ e : (artinSchreierCover n (AffineSpace PUnit (Spec (.of K))) f).left ≅
        AffineSpace PUnit (Spec (.of K)),
      e.hom.appTop (AffineSpace.coord (Spec (.of K)) PUnit.unit) =
        artinSchreierCoverCoordinate n (AffineSpace PUnit (Spec (.of K))) f ∧
      e.hom ≫ (AffineSpace PUnit (Spec (.of K)) ↘ Spec (.of K)) =
        (artinSchreierCover n (AffineSpace PUnit (Spec (.of K))) f).hom ≫
          (AffineSpace PUnit (Spec (.of K)) ↘ Spec (.of K)) := by
  let S := Spec (CommRingCat.of K)
  let X := AffineSpace PUnit S
  let x := AffineSpace.coord S PUnit.unit
  let Y := artinSchreierCover n X f
  let π := Y.hom
  let T := artinSchreierCoverCoordinate n X f
  let c : K →+* Γ(X, ⊤) :=
    (X ↘ S).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let g : X ⟶ X := AffineSpace.homOfVector (X ↘ S)
    (fun _ : PUnit ↦ c a⁻¹ * (x ^ n - x))
  have hg : g ≫ (X ↘ S) = X ↘ S := AffineSpace.homOfVector_over _ _
  have hgscalar (b : K) : g.appTop (c b) = c b := by
    change g.appTop ((X ↘ S).appTop _) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hg]
    rfl
  have hroot : x ^ n - x = g.appTop f := by
    rw [hf, map_mul]
    change x ^ n - x = g.appTop (c a) * g.appTop x
    rw [hgscalar]
    have hgx : g.appTop x = c a⁻¹ * (x ^ n - x) :=
      AffineSpace.homOfVector_appTop_coord _ _ _
    rw [hgx]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  obtain ⟨s, hs⟩ := linear_cover_root_lift n X f X g x hroot
  let h : Y.left ⟶ X := AffineSpace.homOfVector (π ≫ (X ↘ S)) (fun _ : PUnit ↦ T)
  have hh : h ≫ (X ↘ S) = π ≫ (X ↘ S) := AffineSpace.homOfVector_over _ _
  have hhscalar (b : K) : h.appTop (c b) = π.appTop (c b) := by
    change h.appTop ((X ↘ S).appTop _) = π.appTop ((X ↘ S).appTop _)
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hh,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have hT : h.appTop x = T := AffineSpace.homOfVector_appTop_coord _ _ _
  have hrel : T ^ n - T = π.appTop f := linear_cover_coordinate_relation n X f
  have hhg : h ≫ g = π := by
    apply AffineSpace.hom_ext
    · change (h ≫ g) ≫ (X ↘ S) = π ≫ (X ↘ S)
      rw [Category.assoc, hg, hh]
    · intro i
      cases i
      change h.appTop (g.appTop x) = π.appTop x
      rw [AffineSpace.homOfVector_appTop_coord, map_mul, map_sub, map_pow,
        hhscalar, hT, hrel, hf, map_mul]
      change π.appTop (c a⁻¹) * (π.appTop (c a) * π.appTop x) = π.appTop x
      rw [← mul_assoc, ← map_mul, ← c.map_mul, inv_mul_cancel₀ ha,
        c.map_one, map_one, one_mul]
  have hhs : h ≫ s.left = 𝟙 Y.left := by
    apply linear_cover_hom_ext n X f Y.left
    · rw [Category.assoc, Over.w s, Category.id_comp]
      exact hhg
    · change h.appTop (s.left.appTop (artinSchreierCoverCoordinate n X f)) = T
      rw [hs]
      exact hT
  have hsh : s.left ≫ h = 𝟙 X := by
    apply AffineSpace.hom_ext
    · rw [Category.assoc, hh, ← Category.assoc, Over.w s]
      change g ≫ (X ↘ S) = (𝟙 X) ≫ (X ↘ S)
      simpa only [Category.id_comp] using hg
    · intro i
      cases i
      change s.left.appTop (h.appTop x) = x
      rw [hT, hs]
  exact ⟨⟨h, s.left, hhs, hsh⟩, hT, hh⟩

private abbrev abelianSections (X : Scheme.{u}) :=
  Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) (Scheme.ProEt.mk (𝟙 X))

private def lowerStarAbelianSectionsIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ProEtale.lowerStar Ab.{u + 1} g ⋙ abelianSections Y ≅ abelianSections X :=
  Functor.isoWhiskerLeft _
      (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId Y)).symm ≪≫
    ProEtale.globalSectionsLowerStarIso Ab.{u + 1} g ≪≫
      Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)

private theorem abelian_constant_cohomology_iso
    (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (e : X ≅ Y) (q : ℕ) :
    Nonempty (((abelianSections X).rightDerived q).obj
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) ≅
        ((abelianSections Y).rightDerived q).obj
          (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) := by
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  let F := ProEtale.lowerStar Ab.{u + 1} e.inv
  let N := ProEtale.condensedRingObj Λ Y
  let eN : F.obj N ≅ ProEtale.condensedRingObj Λ X :=
    ((ProEtale.upperStarIsoLowerStarInv Ab.{u + 1} e).app N).symm ≪≫
      asIso (ProEtale.condensedPullbackHom Λ e.hom)
  let c := Functor.compRightDerivedObjIso F (abelianSections X)
    (fun I _ ↦ (abelianSections X).rightAcyclic_of_injective (F.obj I)) q N
  exact ⟨((abelianSections X).rightDerived q).mapIso eN.symm ≪≫ c.symm ≪≫
    Functor.rightDerivedObjIsoOfIso (lowerStarAbelianSectionsIso e.inv) q N⟩

private theorem abelian_line_positive
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (K : Type u) [Field K] [IsAlgClosed K] [CharP K p]
    (q : ℕ) (hq : q ≠ 0) :
    IsZero (((abelianSections (AffineSpace PUnit (Spec (.of K)))).rightDerived q).obj
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (AffineSpace PUnit (Spec (.of K))))) := by
  have hℓ : (ℓ : K) ≠ 0 := by
    intro h
    have hpdiv : p ∣ ℓ := (CharP.cast_eq_zero_iff K p ℓ).1 h
    exact hpℓ ((Nat.dvd_prime (Fact.out : ℓ.Prime)).1 hpdiv |>.resolve_left
      (Fact.out : p.Prime).ne_one)
  have hunit : IsUnit (ℓ : K) := isUnit_iff_ne_zero.mpr hℓ
  have h := (ProEtale.affineLine_condensedQbar_cohomology K (Or.inr inferInstance)
    ℓ hunit K).2 q (Nat.pos_of_ne_zero hq)
  let e := AffineSpace.reindexIso (Spec (.of K))
    (Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit)
  obtain ⟨eH⟩ := abelian_constant_cohomology_iso ℓ e q
  exact h.of_iso eH

private theorem ordinary_module_abelian_cohomology_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type u) [Field K] [IsAlgClosed K]
    (X : Scheme.{u}) (a : X ⟶ Spec (.of K))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) (q : ℕ) :
    Nonempty ((forget₂ (ModuleCat.{u + 1} (PadicAlgCl ℓ)) Ab.{u + 1}).obj
      ((qlbarGeometricModuleCohomology ℓ K X a q).obj N) ≅
        ((abelianSections X).rightDerived q).obj N.X) := by
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  let F := ProEtale.CondensedRing.lowerStar Λ a
  let E := ProEtale.CondensedQbarGeometricEvaluation.fieldFiber K ℓ
  let V := forget₂ (ModuleCat.{u + 1} (PadicAlgCl ℓ)) Ab.{u + 1}
  let U := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (ProEtale.condensedRingObj Λ X)
  let EY := E ⋙ V
  let eunder : F ⋙ EY ≅ U ⋙ abelianSections X :=
    Functor.isoWhiskerLeft U (lowerStarAbelianSectionsIso a)
  let c₁ : V.obj ((qlbarGeometricModuleCohomology ℓ K X a q).obj N) ≅
      EY.obj ((F.rightDerived q).obj N) :=
    V.mapIso ((E.mapDerivedCategoryHomologyFunctorIso (q : ℤ)).symm.app _ ≪≫
      E.mapIso ((F.singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso q).app N))
  let c₂ := Functor.rightDerivedCompObjIso F EY q N
  let c₃ := Functor.rightDerivedObjIsoOfIso eunder q N
  let c₄ := Functor.compRightDerivedObjIso U (abelianSections X)
    (fun I _ ↦ (abelianSections X).rightAcyclic_of_injective (U.obj I)) q N
  exact ⟨c₁ ≪≫ c₂.symm ≪≫ c₃ ≪≫ c₄⟩


private theorem module_isIso_of_split_and_line
    {R : Type} [Field R] {A B : ModuleCat.{u + 1} R}
    (f : A ⟶ B) (g : B ⟶ A) (h : f ≫ g = 𝟙 A)
    (eA : A ≅ ModuleCat.of R (ULift.{u + 1} R))
    (eB : B ≅ ModuleCat.of R (ULift.{u + 1} R)) : IsIso f := by
  let : Mono f := mono_of_mono_fac h
  let m := eA.inv ≫ f ≫ eB.hom
  have hm : Function.Injective m.hom := (ModuleCat.mono_iff_injective m).1 inferInstance
  have hs : Function.Surjective m.hom := LinearMap.surjective_of_injective hm
  let : IsIso m := (ConcreteCategory.isIso_iff_bijective m).2 ⟨hm, hs⟩
  have hf : f = eA.hom ≫ m ≫ eB.inv := by simp [m]
  rw [hf]
  infer_instance


/-- On a nonzero linear cover the whole finite pushforward has no positive
cohomology, and its trivial character summand accounts for all degree-zero
cohomology. No nontrivial character occurs in this statement.
Source: blueprint lem-fd-cohomology-affine-line-character, nonzero-function
paragraphs (blueprint: lem-fd-cohomology-affine-line-cover-constants).

Proof: the maps T↦y and x↦a inverse times (y^p-y) construct inverse maps
between the cover and the affine line, by the quotient and pullback universal
properties. Finite pushforward cohomology, clause (2) of
lem-fd-finite-pushforward-cohomology, follows from exact finite abelian direct
image, its preservation of injectives, and the module-to-abelian cohomology
comparison for the flat coefficient ring. This proves the positive-degree clause.
In degree zero, the isotypic coproduct gives a retraction of the specified
trivial-character inclusion. Its source is the regular coefficient, whose H0
is a coefficient line. The connected cover has the same one-dimensional H0.
Conjugating the split injection by those linear isomorphisms yields an injective
endomorphism of a one-dimensional space, hence an isomorphism. Conjugate back. -/
theorem qlbar_linear_cover_constant_cohomology
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (K : Type u) [Field K] [IsAlgClosed K] [CharP K p]
    (a : K) (ha : a ≠ 0)
    (f : Γ(AffineSpace PUnit (Spec (.of K)), ⊤))
    (hf : f = scalar K (AffineSpace PUnit (Spec (.of K))) a *
      AffineSpace.coord (Spec (.of K)) PUnit.unit)
    (σ : Multiplicative (ZMod p) →* Aut
      (artinSchreierCover p (AffineSpace PUnit (Spec (.of K))) f))
    (hσ : ∀ b : ZMod p,
      (σ (Multiplicative.ofAdd b)).hom.left.appTop
          (artinSchreierCoverCoordinate p (AffineSpace PUnit (Spec (.of K))) f) =
        artinSchreierCoverCoordinate p (AffineSpace PUnit (Spec (.of K))) f +
          (b.val : Γ((artinSchreierCover p (AffineSpace PUnit (Spec (.of K))) f).left, ⊤)))
    (q : ℕ) :
    let X := AffineSpace PUnit (Spec (.of K))
    let H := qlbarGeometricModuleCohomology ℓ K X (X ↘ Spec (.of K)) q
    (q = 0 → IsIso (H.map (image.ι (qlbarPrimeProjector p ℓ X f σ 1)))) ∧
      (q ≠ 0 → IsZero (H.obj
        ((ProEtale.CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
          (artinSchreierCover p X f).hom).obj
            (Mod.regular (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ)
              (artinSchreierCover p X f).left))))) := by
  classical
  let X := AffineSpace PUnit (Spec (.of K))
  let Y := artinSchreierCover p X f
  let π := Y.hom
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  let N := Mod.regular (ProEtale.condensedRingObj Λ Y.left)
  let P := (ProEtale.CondensedRing.lowerStar Λ π).obj N
  let H := qlbarGeometricModuleCohomology ℓ K X (X ↘ Spec (.of K)) q
  have hchar : (p : Γ(X, ⊤)) = 0 := by
    let g : K →+* Γ(X, ⊤) := (X ↘ Spec (.of K)).appTop.hom.comp
      (Scheme.ΓSpecIso (.of K)).inv.hom
    simpa only [map_natCast, map_zero] using congrArg g (CharP.cast_eq_zero K p)
  obtain ⟨e, heT, heK⟩ := nonzero_linear_cover_iso p K a ha f hf
  have : Nonempty X :=
    ⟨(AffineSpace.zeroSection _ _).base (Classical.arbitrary (Spec (.of K)))⟩
  have := isIntegral_of_isAffine_of_isDomain X
  have : ConnectedSpace X := inferInstance
  let : IsAffine Y.left := IsAffine.of_isIso e.hom
  let : ConnectedSpace Y.left := e.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  constructor
  · intro hq
    subst q
    obtain ⟨hc⟩ := (qlbar_artinSchreier_isotypic_properties p ℓ hpℓ X hchar f σ hσ).1
    obtain ⟨eL⟩ := (qlbar_artinSchreier_isotypic_properties p ℓ hpℓ X hchar f σ hσ).2.2.1
    let M := fun χ : AddChar (ZMod p) (PadicAlgCl ℓ) ↦
      image (qlbarPrimeProjector p ℓ X f σ χ)
    let ι := fun χ : AddChar (ZMod p) (PadicAlgCl ℓ) ↦
      image.ι (qlbarPrimeProjector p ℓ X f σ χ)
    let c : Cofan M := Cofan.mk (M 1) (fun χ ↦
      if h : χ = 1 then eqToHom (congrArg M h) else 0)
    let r : P ⟶ M 1 := hc.desc c
    have hr : ι 1 ≫ r = 𝟙 (M 1) := by
      simpa [r, c, ι] using hc.fac c (Discrete.mk 1)
    obtain ⟨eP⟩ := qlbar_connected_pushforward_zero_iso ℓ K π (X ↘ Spec (.of K))
    obtain ⟨eX⟩ := qlbar_connected_pushforward_zero_iso ℓ K (𝟙 X) (X ↘ Spec (.of K))
    let eS := H.mapIso eL ≪≫
      H.mapIso ((ProEtale.CondensedRing.lowerStarId Λ X).symm.app
        (Mod.regular (ProEtale.condensedRingObj Λ X))) ≪≫ eX
    exact module_isIso_of_split_and_line (H.map (ι 1)) (H.map r)
      (by rw [← H.map_comp, hr, H.map_id]) eS eP
  · intro hq
    let V := forget₂ (ModuleCat.{u + 1} (PadicAlgCl ℓ)) Ab.{u + 1}
    obtain ⟨eM⟩ := ordinary_module_abelian_cohomology_iso ℓ K X
      (X ↘ Spec (.of K)) P q
    let F := ProEtale.lowerStar Ab.{u + 1} π
    have hπ := artinSchreier_cover_properties p X hchar f
    let : IsFinite π := hπ.1
    let : Etale π := hπ.2.1
    let : PreservesFiniteColimits F :=
      ProEtale.preservesFiniteColimits_lowerStar_of_isFinite_ab π
    let : F.PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} π)
    let e₁ := Functor.compRightDerivedObjIso F (abelianSections X)
      (fun I _ ↦ (abelianSections X).rightAcyclic_of_injective (F.obj I)) q N.X
    let e₂ := Functor.rightDerivedObjIsoOfIso (lowerStarAbelianSectionsIso π) q N.X
    obtain ⟨e₃⟩ := abelian_constant_cohomology_iso ℓ e q
    have hz := abelian_line_positive p ℓ hpℓ K q hq
    have hzero : IsZero (V.obj (H.obj P)) := hz.of_iso (eM ≪≫ e₁.symm ≪≫ e₂ ≪≫ e₃)
    apply (IsZero.iff_id_eq_zero _).2
    apply V.map_injective
    exact hzero.eq_of_src _ _

end AlgebraicGeometry.ArtinSchreierTrace
