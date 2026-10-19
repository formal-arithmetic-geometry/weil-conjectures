module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Tensor quotient epimorphism

Source: Bhatt--Scholze, *Pro-étale topology*, Proposition 6.8.4(1), p. 59
(blueprint: lem-sfb-integral-tensor-quotient-epimorphism).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- Naturality of the sectionwise extension--restriction unit.
Source: Stacks, Modules on Sites, Tag 03EK
(blueprint: lem-sfb-integral-tensor-quotient-epimorphism).
Proof: the extension--restriction unit sends `m` to `1 ⊗ m`. The restriction map
on the tensor presheaf restricts both factors, and ring restrictions preserve `1`.
Consequently both composites send `m` to `1 ⊗ (m restricted along f)`.
Equality on elements gives equality of these linear maps. -/
theorem integralTensorQuotientPresheafUnit_naturality
    {R₀ R : Sheaf J CommRingCat.{u}} (q : R₀ ⟶ R)
    (F : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    F.val.map f ≫
        (ModuleCat.restrictScalars
          (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀).obj.map f).hom).map
          ((ModuleCat.ExtendRestrictScalarsAdj.unit ((q.hom.app V).hom)).app
            (F.val.obj V)) =
      (ModuleCat.ExtendRestrictScalarsAdj.unit ((q.hom.app U).hom)).app
          (F.val.obj U) ≫
        ((PresheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map q).hom).obj
            (changeOfRingsPresheaf q F)).map f := by
  apply ModuleCat.hom_ext
  ext m
  change (1 : R.obj.obj V) ⊗ₜ[R₀.obj.obj V, (q.hom.app V).hom] F.val.map f m =
    changeOfRingsMap q F f ((1 : R.obj.obj U) ⊗ₜ[R₀.obj.obj U, (q.hom.app U).hom] m)
  rw [show changeOfRingsMap q F f
      ((1 : R.obj.obj U) ⊗ₜ[R₀.obj.obj U, (q.hom.app U).hom] m) =
      R.obj.map f 1 ⊗ₜ[R₀.obj.obj V, (q.hom.app V).hom] F.val.map f m from
    Classical.choose_spec (exists_changeOfRingsMap q F f) 1 m]
  rw [map_one]

/-- The sectionwise unit into the tensor presheaf, with components `m ↦ 1 ⊗ m`.
Source: Stacks, Modules on Sites, Tag 03EK
(blueprint: lem-sfb-integral-tensor-quotient-epimorphism). -/
noncomputable def integralTensorQuotientPresheafUnit
    {R₀ R : Sheaf J CommRingCat.{u}} (q : R₀ ⟶ R)
    (F : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)) :
    F.val ⟶ (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map q).hom).obj
      (changeOfRingsPresheaf q F) where
  app U := (ModuleCat.ExtendRestrictScalarsAdj.unit
    ((q.hom.app U).hom)).app (F.val.obj U)
  naturality f := integralTensorQuotientPresheafUnit_naturality q F f

/-- The canonical unit into the sheafified tensor quotient: compose `m ↦ 1 ⊗ m`
with the module-sheafification unit and restrict the target scalars along `q`.
Source: Stacks, Modules on Sites, Tags 03CY and 03EK
(blueprint: lem-sfb-integral-tensor-quotient-epimorphism). -/
noncomputable def integralTensorQuotientUnit
    {R₀ R : Sheaf J CommRingCat.{u}} (q : R₀ ⟶ R)
    (F : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)) :
    F ⟶ (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).map q)).obj (changeOfRings q F) where
  val := integralTensorQuotientPresheafUnit q F ≫
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map q).hom).map
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.app
        (changeOfRingsPresheaf q F))

/-- If a sheaf map of commutative rings is locally surjective, then the scalar-extension
unit is locally surjective and epic as a map of sheaves of modules.

Source: Bhatt--Scholze, *Pro-étale topology*, Proposition 6.8.4(1), p. 59
(blueprint: lem-sfb-integral-tensor-quotient-epimorphism).
Proof: sections of the sheafified tensor product are locally represented by finite sums of
pure tensors; local surjectivity of `q` lifts their finitely many coefficients on a common
refinement, so each local section is `1 ⊗ m`. Right cancellation follows from the sheaf
uniqueness axiom. -/
theorem integral_tensor_quotient_epimorphism
    {R₀ R : Sheaf J CommRingCat.{u}} (q : R₀ ⟶ R)
    (hq : Presheaf.IsLocallySurjective J
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map q).hom)
    (F : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)) :
    Presheaf.IsLocallySurjective J
        ((PresheafOfModules.toPresheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀).obj).map
          (integralTensorQuotientUnit q F).val) ∧
      Epi (integralTensorQuotientUnit q F) := by
  let a := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map q).hom
  let η := integralTensorQuotientPresheafUnit q F
  have hu : PresheafOfModules.IsLocallySurjective J η := by
    constructor
    intro U t
    induction t using TensorProduct.induction_on with
    | zero =>
      apply J.superset_covering (S := ⊤) ?_ (J.top_mem U)
      intro V f _
      refine ⟨0, ?_⟩
      change (η.app _).hom 0 = (changeOfRingsPresheaf q F).map f.op 0
      rw [map_zero, map_zero]
    | tmul r m =>
      apply J.superset_covering ?_ (Presheaf.imageSieve_mem J a r)
      rintro V f ⟨r', hr'⟩
      refine ⟨r' • (show F.val.obj (Opposite.op V) from F.val.map f.op m), ?_⟩
      change (η.app _).hom (r' • (show F.val.obj (Opposite.op V) from F.val.map f.op m)) =
        changeOfRingsMap q F f.op (r ⊗ₜ[R₀.obj.obj _, (q.hom.app _).hom] m)
      rw [(η.app _).hom.map_smul]
      rw [show changeOfRingsMap q F f.op
          (r ⊗ₜ[R₀.obj.obj _, (q.hom.app _).hom] m) =
          R.obj.map f.op r ⊗ₜ[R₀.obj.obj _, (q.hom.app _).hom] F.val.map f.op m from
        Classical.choose_spec (exists_changeOfRingsMap q F f.op) r m]
      change (q.hom.app (Opposite.op V) r') •
        ((1 : R.obj.obj (Opposite.op V)) ⊗ₜ[R₀.obj.obj (Opposite.op V),
          (q.hom.app (Opposite.op V)).hom]
          (show F.val.obj (Opposite.op V) from F.val.map f.op m)) = _
      rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
      exact congrArg (fun s ↦ s ⊗ₜ[R₀.obj.obj (Opposite.op V),
        (q.hom.app (Opposite.op V)).hom]
        (show F.val.obj (Opposite.op V) from F.val.map f.op m)) hr'
    | add x y hx hy =>
      apply J.superset_covering ?_ (J.intersection_covering hx hy)
      rintro V f ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
      refine ⟨m + n, ?_⟩
      change (η.app _).hom (m + n) = (changeOfRingsPresheaf q F).map f.op (x + y)
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) hm hn
  have h : PresheafOfModules.IsLocallySurjective J (integralTensorQuotientUnit q F).val := by
    change Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map η ≫
        CategoryTheory.toSheafify J (changeOfRingsPresheaf q F).presheaf)
    have hθ : Presheaf.IsLocallySurjective J
        (CategoryTheory.toSheafify J (changeOfRingsPresheaf q F).presheaf) :=
      (J.W_toSheafify (changeOfRingsPresheaf q F).presheaf).isLocallySurjective
    exact Presheaf.isLocallySurjective_comp J _ _
  refine ⟨h, ?_⟩
  have : Sheaf.IsLocallySurjective ((toSheaf _).map (integralTensorQuotientUnit q F)) := h
  have : Epi ((toSheaf _).map (integralTensorQuotientUnit q F)) :=
    Sheaf.epi_of_isLocallySurjective _
  exact (toSheaf _).epi_of_epi_map inferInstance

end SheafOfModules
