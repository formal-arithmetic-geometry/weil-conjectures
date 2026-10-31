/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSpanModuleComparisonData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncodingSupplement

/-! # Basic properties of native scalar transport
Source: Stacks Project, Tags 03CV and 070H.
(blueprint: lem-sf-finite-span-scalar-sections). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.FiniteSpanComparison

private theorem underlying (l : ℕ) [Fact l.Prime] [d : Data.{u} l] (X : Scheme.{u}) :
    (equivalence l X (d.theta X)).functor ⋙ SheafOfModules.toSheaf (ring l X) =
      Mod.forget (condensedRingObj (Profinite.padicAlgClRingObj l) X) := by
  rfl

private theorem kinjective (l : ℕ) [Fact l.Prime] [d : Data.{u} l] (X : Scheme.{u})
    (I : CochainComplex (internal l X) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((equivalence l X (d.theta X)).functor.mapHomologicalComplex (.up ℤ)).obj I) := by
  infer_instance

private theorem basis (l : ℕ) [Fact l.Prime] [d : Data.{u} l] (X : Scheme.{u})
    (V : X.ProEtᵒᵖ) (M : internal l X) (n : ℕ)
    (b : Module.Basis (Fin n)
      ((InternalModuleOperations.ring (Profinite.padicAlgClRingObj l) X).obj.obj V)
      (((InternalModuleOperations.equivalence
        (Profinite.padicAlgClRingObj l) X).functor.obj M).val.obj V)) :
    ∃ b' : Module.Basis (Fin n) ((ring l X).obj.obj V)
      (((equivalence l X (d.theta X)).functor.obj M).val.obj V),
      ∀ i : Fin n, b' i = b i := by
  let θ := d.theta X
  let f := ((CondensedRing.sectionRingMap X θ.hom).hom.app V).hom
  let g := ((CondensedRing.sectionRingMap X θ.inv).hom.app V).hom
  let e : (InternalModuleOperations.ring (Profinite.padicAlgClRingObj l) X).obj.obj V ≃+*
      (ring l X).obj.obj V := RingEquiv.ofRingHom f g
    (by
      ext x
      change (θ.hom.hom.app V).hom ((θ.inv.hom.app V).hom x) = x
      exact ConcreteCategory.congr_hom
        (congr_app (congrArg (fun q : nativeAb l X ⟶ nativeAb l X ↦ q.hom)
          θ.inv_hom_id) V) x)
    (by
      ext x
      change (θ.inv.hom.app V).hom ((θ.hom.hom.app V).hom x) = x
      exact ConcreteCategory.congr_hom
        (congr_app (congrArg (fun q : condensedRingObj (Profinite.padicAlgClRingObj l) X ⟶
          condensedRingObj (Profinite.padicAlgClRingObj l) X ↦ q.hom) θ.hom_inv_id) V) x)
  have h (r : (InternalModuleOperations.ring (Profinite.padicAlgClRingObj l) X).obj.obj V)
      (x : M.X.obj.obj V) :
      e r • (@id (((equivalence l X (d.theta X)).functor.obj M).val.obj V) x) =
        r • (@id (((InternalModuleOperations.equivalence
          (Profinite.padicAlgClRingObj l) X).functor.obj M).val.obj V) x) := by
    let J := Scheme.ProEt.topology X
    have hμ := congr_app (Functor.LaxMonoidal.μ_natural_left
      (sheafToPresheaf J Ab.{u + 1}) θ.inv M.X) V
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun t ↦ t ≫ (Mod.act M.X).hom.app V) hμ) (e r ⊗ₜ[ℤ] x)
    have hg : g (e r) = r := e.symm_apply_apply r
    change (θ.inv.hom.app V).hom (e r) = r at hg
    simp only [NatTrans.comp_app, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at hh
    erw [Monoidal.whiskerRight_app,
      AddCommGrpCat.MonoidalCategory.whiskerRight_tmul] at hh
    erw [hg] at hh
    exact hh.symm
  let : Module ((ring l X).obj.obj V)
      (((InternalModuleOperations.equivalence
        (Profinite.padicAlgClRingObj l) X).functor.obj M).val.obj V) :=
    inferInstanceAs (Module ((ring l X).obj.obj V)
      (((equivalence l X (d.theta X)).functor.obj M).val.obj V))
  refine ⟨b.mapCoeffs e h, ?_⟩
  exact b.mapCoeffs_apply (R' := (ring l X).obj.obj V) e h

/-- Scalar relabelling keeps sheaves and basis vectors and preserves K-injectives both ways.
Source: Stacks Project, Modules on Sites, Tag 03CV; Derived Categories, Tag 070H.
(blueprint: lem-sf-finite-span-scalar-sections).

Proof. Both component functors keep the underlying abelian sheaf and every arrow, so the
forgetful functors agree definitionally. Reconstruct the section ring isomorphism from
theta and its inverse. Naturality of the tensor generator identifies the two scalar
actions under this ring isomorphism. Apply Basis.mapCoeffs, which keeps each basis vector,
including the empty basis. Both additive equivalence functors preserve K-injectives by
the existing criterion for right adjoints of exact functors, applied to the two adjunctions
of the equivalence. -/
theorem finiteSpanScalarTransportSections (l : ℕ) [Fact l.Prime] [d : Data.{u} l] :
  (∀ X : Scheme.{u},
    (equivalence l X (d.theta X)).functor ⋙ SheafOfModules.toSheaf (ring l X) =
      Mod.forget (condensedRingObj (Profinite.padicAlgClRingObj l) X)) ∧
  (∀ (X : Scheme.{u}) (V : X.ProEtᵒᵖ) (M : internal l X) (n : ℕ)
    (b : Module.Basis (Fin n)
      ((InternalModuleOperations.ring (Profinite.padicAlgClRingObj l) X).obj.obj V)
      (((InternalModuleOperations.equivalence
        (Profinite.padicAlgClRingObj l) X).functor.obj M).val.obj V)),
    ∃ b' : Module.Basis (Fin n) ((ring l X).obj.obj V)
      (((equivalence l X (d.theta X)).functor.obj M).val.obj V),
      ∀ i : Fin n, b' i = b i) ∧
  (∀ (X : Scheme.{u}) (I : CochainComplex (internal l X) ℤ),
    I.IsKInjective → CochainComplex.IsKInjective
      (((equivalence l X (d.theta X)).functor.mapHomologicalComplex (.up ℤ)).obj I)) ∧
  (∀ (X : Scheme.{u}) (I : CochainComplex (modules l X) ℤ),
    I.IsKInjective → CochainComplex.IsKInjective
      (((equivalence l X (d.theta X)).inverse.mapHomologicalComplex (.up ℤ)).obj I)) := by
  refine ⟨underlying l, basis l, ?_, ?_⟩
  · intro X I hI
    let := hI
    exact kinjective l X I
  · intro X I hI
    let := hI
    infer_instance

end AlgebraicGeometry.ProEtale.FiniteSpanComparison
