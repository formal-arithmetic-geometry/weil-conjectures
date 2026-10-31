/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheafConstruction
public import WeilConjectures.AlgebraicGeometry.FiniteTypeQuasiCoherentSubalgebras
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore
import WeilConjectures.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraKernelImageIdeal
import WeilConjectures.RingTheory.SymmetricAlgebraFinitePresentation
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections

/-! # Symmetric algebra images of a finitely presented module colimit

Source: Stacks Project, Properties, Tags 05JS and 05JT, the symmetric-algebra construction
and the image argument in their proofs.
(blueprint: lem-weil-pbc-symmetric-images-module-colimit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.CommAlgebraSheaf

private noncomputable def underlyingModuleMap {X : Scheme.{u}}
    {B A : X.CommAlgebraSheaf} (f : B ⟶ A) : B.toModule ⟶ A.toModule where
  val := {
    app := fun V ↦ ModuleCat.ofHom (X := B.toModule.val.obj V)
      (Y := A.toModule.val.obj V) {
      toFun := f.right.hom.app V
      map_add' := (f.right.hom.app V).hom.map_add
      map_smul' := by
        intro r a
        change B.right.obj.obj V at a
        change f.right.hom.app V (B.hom.hom.app V r * a) =
          A.hom.hom.app V r * f.right.hom.app V a
        rw [(f.right.hom.app V).hom.map_mul]
        exact congrArg (fun t ↦ t.hom.app V r * f.right.hom.app V a) f.w }
    naturality := by
      intro U V i
      ext a
      exact ConcreteCategory.congr_hom (f.right.hom.naturality i) a }

private noncomputable def underlyingModuleIso {X : Scheme.{u}}
    {B A : X.CommAlgebraSheaf} (e : B ≅ A) : B.toModule ≅ A.toModule where
  hom := underlyingModuleMap e.hom
  inv := underlyingModuleMap e.inv
  hom_inv_id := by
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    exact congrArg (fun t ↦ t.right.hom.app (op U)
      (show B.right.obj.obj (op U) from x)) e.hom_inv_id
  inv_hom_id := by
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    exact congrArg (fun t ↦ t.right.hom.app (op U)
      (show A.right.obj.obj (op U) from x)) e.inv_hom_id

private theorem image_generators {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (A : X.CommAlgebraSheaf) (φ : F ⟶ A.toModule)
    (ψ : SymmetricAlgebraSheaf.algebra F ⟶ A)
    (hψ : ∀ (U : X.Opens) (x : F.val.obj (op U)),
      ψ.right.hom.app (op U) ((SymmetricAlgebraSheaf.inclusion F).val.app (op U) x) =
        φ.val.app (op U) x)
    (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) (f : Fin n → Γ(F, U))
    (hf : Submodule.span Γ(X, U) (Set.range f) = ⊤) :
    (↑(@Algebra.adjoin Γ(X, U) (A.right.obj.obj (op U)) _ _
      (A.hom.hom.app (op U)).hom.toAlgebra
      (Set.range (fun k : Fin n ↦ φ.val.app (op U) (f k)))) :
        Set (A.right.obj.obj (op U))) = Set.range (ψ.right.hom.app (op U)) := by
  let : Algebra Γ(X, U) (A.right.obj.obj (op U)) :=
    (A.hom.hom.app (op U)).hom.toAlgebra
  let p : SymmetricAlgebra Γ(X, U) Γ(F, U) →ₐ[Γ(X, U)]
      A.right.obj.obj (op U) :=
    { toRingHom := (ψ.right.hom.app (op U)).hom.comp
        (SymmetricAlgebraSheaf.sectionMap F (op U))
      commutes' := fun r ↦ congrArg (fun t ↦ t.hom.app (op U) r) (Under.w ψ) }
  have hp (x : Γ(F, U)) : p (SymmetricAlgebra.ι _ _ x) = φ.val.app (op U) x :=
    hψ U x
  let g : Fin n → A.right.obj.obj (op U) := fun k ↦ φ.val.app (op U) (f k)
  change (↑(Algebra.adjoin Γ(X, U) (Set.range g)) :
    Set (A.right.obj.obj (op U))) = _
  have he : Set.range g =
      p '' Set.range (fun k : Fin n ↦ SymmetricAlgebra.ι Γ(X, U) Γ(F, U) (f k)) := by
    rw [← Set.range_comp]
    congr 1
    funext k
    exact (hp (f k)).symm
  have hg := (SymmetricAlgebra.generators_and_finitePresentation Γ(X, U) Γ(F, U)).1 n f hf
  have hgen : Algebra.adjoin Γ(X, U)
      (Set.range g) = p.range := by
    rw [he, Algebra.adjoin_image, hg, Algebra.map_top]
  rw [hgen]
  change Set.range p = Set.range (ψ.right.hom.app (op U))
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact ⟨SymmetricAlgebraSheaf.sectionMap F (op U) t, rfl⟩
  · rintro _ ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ :=
      (quasiCoherentSymmetricAlgebra_affine_comparison X F).2 ⟨U, hU⟩ |>.2 t
    exact ⟨s, rfl⟩

private theorem finiteType_of_generators_range {R D A : Type u}
    [CommRing R] [CommRing D] [CommRing A] (f : R →+* D) (k : D →+* A)
    (hk : Function.Injective k) (n : ℕ) (g : Fin n → A)
    (hg : (↑(@Algebra.adjoin R A _ _ (k.comp f).toAlgebra (Set.range g)) : Set A) =
      Set.range k) : f.FiniteType := by
  classical
  let : Algebra R D := f.toAlgebra
  let : Algebra R A := (k.comp f).toAlgebra
  let q : D →ₐ[R] A := { toRingHom := k, commutes' := fun _ ↦ rfl }
  have he : Algebra.adjoin R (Set.range g) = q.range := SetLike.coe_injective hg
  have hfg : q.range.FG :=
    ⟨Finset.univ.image g, by simpa only [Finset.coe_image, Finset.coe_univ,
      Set.image_univ] using he⟩
  have : Algebra.FiniteType R q.range := (Subalgebra.fg_iff_finiteType _).mp hfg
  exact Algebra.FiniteType.equiv this (AlgEquiv.ofInjective q hk).symm

/-- Symmetric algebra images of a finitely presented module system are finite type
quasi-coherent subalgebras covering affine sections of its colimit algebra.
Source: Stacks Project, Properties, Tags 05JS and 05JT, proofs.
(blueprint: lem-weil-pbc-symmetric-images-module-colimit).

Proof:
1. Apply lem-weil-pbc-quasi-coherent-finite-type-affine (0) to each finite presentation.
   Its affine clause (b) gives finitely presented section modules, hence finite generating
   lists, by taking the images of the standard basis of a finite free presentation.
2. Apply lem-weil-pbc-quasi-coherent-symmetric-algebra-core to the constructed symmetric
   algebra and degree-one map of lem-weil-pbc-symmetric-algebra-sheaf-construction.
   This gives the unique extension of each given linear map. The affine comparison of
   lem-weil-pbc-quasi-coherent-symmetric-algebra-affine is bijective and takes degree-one
   generators to the sheaf degree-one map.
3. Apply lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal (a). The local image is
   quasi-coherent and its affine sections are exactly the sectionwise image, since both
   source and target are quasi-coherent. Regard its inclusion as a subobject of the algebra.
4. By lem-weil-pbc-symmetric-algebra-finite-presentation (a), any finite module generating
   list generates the symmetric algebra in degree one. Lift an affine image section to
   the symmetric algebra using Step 3 and the affine comparison from Step 2, express it as
   a polynomial in those generators, and apply the algebra map. Thus the images of the
   given module generators generate the image algebra. Together with Step 3, this gives
   membership in def-weil-pbc-finite-type-quasi-coherent-subalgebras.
5. Apply lem-weil-pbc-quasi-coherent-module-colimit-affine-sections to the supplied cocone.
   Every affine section has a representative in one of its module stages. Step 2
   identifies its image with the corresponding symmetric algebra degree-one image, and
   Step 3 puts that section in the associated image subalgebra. -/
theorem symmetricImagesModuleColimit
    (X : Scheme.{u}) (A : X.CommAlgebraSheaf) (hA : A.toModule.IsQuasicoherent)
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ X.Modules) (hF : ∀ i : I, (F.obj i).IsFinitePresentation)
    (φ : F ⟶ (Functor.const I).obj A.toModule)
    (hc : IsColimit (Cocone.mk A.toModule φ)) :
    (∀ i : I, (F.obj i).IsQuasicoherent) ∧
      ∃ (ψ : ∀ i : I, SymmetricAlgebraSheaf.algebra (F.obj i) ⟶ A)
        (C : I → A.finiteTypeQuasiCoherentSubalgebras),
        (∀ i : I,
          (∀ (U : X.Opens) (x : (F.obj i).val.obj (op U)),
            (ψ i).right.hom.app (op U)
              ((SymmetricAlgebraSheaf.inclusion (F.obj i)).val.app (op U) x) =
                (φ.app i).val.app (op U) x) ∧
          (∀ t : SymmetricAlgebraSheaf.algebra (F.obj i) ⟶ A,
            (∀ (U : X.Opens) (x : (F.obj i).val.obj (op U)),
              t.right.hom.app (op U)
                ((SymmetricAlgebraSheaf.inclusion (F.obj i)).val.app (op U) x) =
                  (φ.app i).val.app (op U) x) → t = ψ i) ∧
          (∀ (U : X.Opens) (s : A.right.obj.obj (op U)),
            s ∈ Set.range ((C i).val.arrow.right.hom.app (op U)) ↔
              ∀ p : X, p ∈ U → ∃ (V : X.Opens) (hVU : V ≤ U), p ∈ V ∧
                A.right.obj.map (homOfLE hVU).op s ∈
                  Set.range ((ψ i).right.hom.app (op V))) ∧
          (∀ U : X.Opens, IsAffineOpen U →
            Set.range ((C i).val.arrow.right.hom.app (op U)) =
                Set.range ((ψ i).right.hom.app (op U)) ∧
            Module.FinitePresentation Γ(X, U) Γ(F.obj i, U) ∧
            ∀ (n : ℕ) (f : Fin n → Γ(F.obj i, U)),
              Submodule.span Γ(X, U) (Set.range f) = ⊤ →
              (↑(@Algebra.adjoin Γ(X, U) (A.right.obj.obj (op U)) _ _
                (A.hom.hom.app (op U)).hom.toAlgebra
                (Set.range (fun k : Fin n ↦ (φ.app i).val.app (op U) (f k)))) :
                  Set (A.right.obj.obj (op U))) =
                    Set.range ((C i).val.arrow.right.hom.app (op U)))) ∧
        (∀ (U : X.Opens), IsAffineOpen U → ∀ a : A.right.obj.obj (op U),
          ∃ (i : I) (x : Γ(F.obj i, U)),
            a = (φ.app i).val.app (op U) x ∧
            a = (ψ i).right.hom.app (op U)
              ((SymmetricAlgebraSheaf.inclusion (F.obj i)).val.app (op U) x) ∧
            a ∈ Set.range ((C i).val.arrow.right.hom.app (op U))) := by
  classical
  have hqc (i : I) : (F.obj i).IsQuasicoherent :=
    (Scheme.Modules.quasicoherent_finite_type_affine.{u, u} X).1 _ (hF i)
  have hfp (i : I) (U : X.Opens) (hU : IsAffineOpen U) :
      Module.FinitePresentation Γ(X, U) Γ(F.obj i, U) :=
    ((Scheme.Modules.quasicoherent_finite_type_affine.{u, u} X).2 _ (hqc i)).2.2 (hF i) U hU
  choose ψ hψ huniq using fun i ↦
    exists_quasiCoherentSymmetricAlgebra_core X (F.obj i) A (φ.app i)
  have hsym (i : I) := @quasiCoherentSymmetricAlgebra_affine_comparison X (F.obj i) (hqc i)
  choose D k hD hk hlocal haff using fun i ↦
    (kernel_image_quasiCoherent _ A (hsym i).1 hA (ψ i)).2
  have hmono (i : I) : Mono (k i) := by
    have (U : X.Opensᵒᵖ) : Mono ((k i).right.hom.app U) :=
      ConcreteCategory.mono_of_injective _ (hk i U.unop)
    have : Mono (k i).right.hom := NatTrans.mono_of_mono_app _
    have : Mono (k i).right := Sheaf.Hom.mono_of_presheaf_mono _ _ _
    exact (Under.forget X.sheaf).mono_of_mono_map this
  let B (i : I) : Subobject A := Subobject.mk (k i)
  let e (i : I) : (B i : X.CommAlgebraSheaf) ≅ D i := Subobject.underlyingIso (k i)
  have hB (i : I) : (B i : X.CommAlgebraSheaf).toModule.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (underlyingModuleIso (e i)).symm (hD i)
  have hrange (i : I) (U : X.Opens) :
      Set.range ((B i).arrow.right.hom.app (op U)) =
        Set.range ((k i).right.hom.app (op U)) := by
    have hw := congrArg (fun t ↦ t.right.hom.app (op U))
      (Subobject.underlyingIso_hom_comp_eq_mk (k i))
    have he : Function.Surjective ((e i).hom.right.hom.app (op U)) :=
      ConcreteCategory.bijective_of_isIso _ |>.2
    change Set.range ((B i).arrow.right.hom.app (op U)) = _
    rw [← hw]
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨(e i).hom.right.hom.app (op U) x, rfl⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := he x
      exact ⟨y, rfl⟩
  have hgen (i : I) (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ)
      (f : Fin n → Γ(F.obj i, U)) (hf : Submodule.span Γ(X, U) (Set.range f) = ⊤) :=
    @image_generators X (F.obj i) (hqc i) A (φ.app i) (ψ i) (hψ i) U hU n f hf
  have hft (i : I) (U : X.Opens) (hU : IsAffineOpen U) :
      (((B i : X.CommAlgebraSheaf).hom.hom.app (op U)).hom).FiniteType := by
    have : Module.FinitePresentation Γ(X, U) Γ(F.obj i, U) := hfp i U hU
    obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
      (Module.Finite.fg_top (R := Γ(X, U)) (M := Γ(F.obj i, U)))
    have hi : Function.Injective ((B i).arrow.right.hom.app (op U)) := by
      have hw := congrArg (fun t ↦ t.right.hom.app (op U))
        (Subobject.underlyingIso_hom_comp_eq_mk (k i))
      rw [← hw]
      exact (hk i U).comp (ConcreteCategory.bijective_of_isIso _).1
    apply finiteType_of_generators_range _ ((B i).arrow.right.hom.app (op U)).hom hi n
      (fun j ↦ (φ.app i).val.app (op U) (f j))
    have hw := congrArg (fun t ↦ t.hom.app (op U)) (Under.w (B i).arrow)
    change _ = Set.range ((B i).arrow.right.hom.app (op U))
    rw [show ((B i).arrow.right.hom.app (op U)).hom.comp
      (((B i : X.CommAlgebraSheaf).hom.hom.app (op U)).hom) =
        (A.hom.hom.app (op U)).hom from congrArg CommRingCat.Hom.hom hw]
    exact (hgen i U hU n f hf).trans ((haff i U hU).symm.trans (hrange i U).symm)
  let C (i : I) : A.finiteTypeQuasiCoherentSubalgebras := ⟨B i, hB i, hft i⟩
  refine ⟨hqc, ψ, C, ?_, ?_⟩
  · intro i
    refine ⟨hψ i, huniq i, ?_, ?_⟩
    · intro U s
      change s ∈ Set.range ((B i).arrow.right.hom.app (op U)) ↔ _
      rw [hrange]
      exact hlocal i U s
    · intro U hU
      refine ⟨(hrange i U).trans (haff i U hU), hfp i U hU, ?_⟩
      intro n f hf
      exact (hgen i U hU n f hf).trans ((haff i U hU).symm.trans (hrange i U).symm)
  · intro U hU a
    obtain ⟨i, x, hx⟩ :=
      (Scheme.Modules.quasiCoherentModuleColimitAffineSections X I F
        (Cocone.mk A.toModule φ) hc hqc).2 U hU |>.1 a
    refine ⟨i, x, hx.symm, hx.symm.trans (hψ i U x).symm, ?_⟩
    change a ∈ Set.range ((B i).arrow.right.hom.app (op U))
    rw [hrange, haff i U hU]
    exact ⟨(SymmetricAlgebraSheaf.inclusion (F.obj i)).val.app (op U) x,
      (hψ i U x).trans hx⟩

end AlgebraicGeometry.Scheme.CommAlgebraSheaf
