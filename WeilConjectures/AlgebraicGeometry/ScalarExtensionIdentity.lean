/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ScalarExtensionSiteCalculus
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Multiplication-normalized identity scalar extension

Source: Stacks Project, Tag 06YY; scalar-extension blueprint clause (4).
(blueprint: lem-sp-scalar-extension-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

/-- Scalar extension along the identity is the identity, with multiplication on every
cochain representative. Source: Stacks 06YY
(blueprint: lem-sp-scalar-extension-identity).
Proof: restriction along the identity is the identity. Uniqueness of left adjoints
compares ordinary scalar extension with the identity. The normalized adjunction sends
its comparison on 1 tensor x to x; linearity gives s tensor x to s*x. Apply this
comparison termwise. The identity derived functor is the left derived functor of the
localization itself. Uniqueness of left derived functors gives the required isomorphism,
and its factorization equation is precisely the stated equation on every complex. -/
theorem siteScalarIdentity_data (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    ∃ e : siteScalarDerivedChange T (𝟙 R) ≅ 𝟭 _,
      ∀ P : CochainComplex (siteScalarModules T R) ℤ,
        ∃ v : (siteScalarChangeComplex T (𝟙 R)).obj P ⟶ P,
          (∀ (i : ℤ) (U : T.ProEtᵒᵖ) (s : R.obj.obj U) (x : (P.X i).val.obj U),
            (v.f i).val.app U (siteScalarTensorSection T (𝟙 R) (P.X i) U s x) = s • x) ∧
          e.hom.app (DerivedCategory.Q.obj P) =
            siteScalarScalarComplexCounit T (𝟙 R) P ≫ DerivedCategory.Q.map v := by
  let E := siteScalarChange T (𝟙 R)
  let F := siteScalarDerivedChange T (𝟙 R)
  obtain ⟨a, ha⟩ := ordinaryAdjunction_exists T (𝟙 R)
  let r : siteScalarRestrict T (𝟙 R) ≅ 𝟭 (siteScalarModules T R) := Iso.refl _
  let v : E ≅ 𝟭 (siteScalarModules T R) :=
    Adjunction.leftAdjointUniq (a.ofNatIsoRight r) Adjunction.id
  have hv₁ (M : siteScalarModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
      (v.hom.app M).val.app U (siteScalarTensorSection T (𝟙 R) M U 1 x) = x := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
      (a.ofNatIsoRight r) Adjunction.id M
    rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
    have h' := congrArg (fun g : M ⟶ M ↦ g.val.app U x) h
    have hh := (eq_of_heq (ha M M (v.hom.app M) U x)).symm.trans h'
    simpa [r, Adjunction.id] using hh
  let vc : E.mapHomologicalComplex (.up ℤ) ≅ 𝟭 _ :=
    NatIso.mapHomologicalComplex v (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso (siteScalarModules T R) (.up ℤ)
  let ε := complexCounitNat E F (siteScalarDerivedCounit T (𝟙 R))
  have : F.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso (siteScalarModules T R) (.up ℤ)) :=
    complexCounitNat_kan E F (siteScalarDerivedCounit T (𝟙 R))
  let q := DerivedCategory.Q (C := siteScalarModules T R)
  let qid : q ⋙ 𝟭 _ ≅ q := Functor.rightUnitor q
  have : (𝟭 (siteScalarDerivedCategory T R)).IsLeftDerivedFunctor qid.hom
      (HomologicalComplex.quasiIso (siteScalarModules T R) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ qid
  let τ : E.mapHomologicalComplex (.up ℤ) ⋙ q ≅ q :=
    isoWhiskerRight vc q ≪≫ Functor.leftUnitor q
  let e : F ≅ 𝟭 _ := Functor.leftDerivedNatIso F (𝟭 _) ε qid.hom
    (HomologicalComplex.quasiIso (siteScalarModules T R) (.up ℤ)) τ
  refine ⟨e, fun P ↦ ⟨vc.hom.app P, ?_, ?_⟩⟩
  · intro i U s x
    change (v.hom.app (P.X i)).val.app U
      (siteScalarTensorSection T (𝟙 R) (P.X i) U s x) = s • x
    calc
      _ = (v.hom.app (P.X i)).val.app U
          (s • siteScalarTensorSection T (𝟙 R) (P.X i) U 1 x) := by
        rw [tensorSection_smul, mul_one]
      _ = s • x := by rw [_root_.map_smul, hv₁]
  · have h := Functor.leftDerivedNatTrans_app F (𝟭 _) ε qid.hom
      (HomologicalComplex.quasiIso (siteScalarModules T R) (.up ℤ)) τ.hom P
    simpa [e, Functor.leftDerivedNatIso_hom, ε, qid, q, τ,
      complexCounitNat_app, siteScalarScalarComplexCounit, E, F] using h

end AlgebraicGeometry.Scheme
