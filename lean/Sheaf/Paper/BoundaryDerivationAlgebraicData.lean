module

public import Sheaf.Paper.PQFCohomology
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.Algebra.Homology.HomologySequence

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The algebraic Čech and derivation identities for fixed compatible resolutions.
This is the local algebra step in the proof of the square-zero boundary derivation theorem.
Source: Stacks Project, Cohomology, Lemma 0B8S.
(blueprint: lem-sc-boundary-derivation-square-zero-algebraic-data) -/
theorem boundary_derivation_algebraic_data (X : Scheme.{u})
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C)
    (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (i : I ⟶ commAlgebraSheafModule X.sheaf B)
    (hw : i ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
    (_hS : (ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p) hw).ShortExact)
    (_hsq : ∀ (U : X.Opens) (x y : B.right.obj.obj (op U)),
      p.right.hom.app (op U) x = 0 → p.right.hom.app (op U) y = 0 → x * y = 0)
    (IA : InjectiveResolution I)
    (IB : InjectiveResolution (commAlgebraSheafModule X.sheaf B))
    (IC : InjectiveResolution (commAlgebraSheafModule X.sheaf C))
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (_hιA : IA.ι ≫ α = (CochainComplex.single₀ _).map i ≫ IB.ι)
    (_hιB : IB.ι ≫ β =
      (CochainComplex.single₀ _).map ((commAlgebraSheafModuleFunctor X.sheaf).map p) ≫ IC.ι)
    (_hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) k)).ShortExact)
    (hΓ : ((ShortComplex.mk α β hαβ).map
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ))).ShortExact) :
    ∃ (σ : ∀ U : X.Opens, C.right.obj.obj (op U) →+*
        Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (I.val.obj (op U)))
      (μ : C.right.obj.obj (op ⊤) →+* End I)
      (ρ : C.right.obj.obj (op ⊤) →+*
        Module.End ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
          ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I))
      (δ : C.right.obj.obj (op ⊤) →+
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I)),
      (∀ (U : X.Opens) (b : B.right.obj.obj (op U)) (x : I.val.obj (op U)),
        @id (B.right.obj.obj (op U)) (i.val.app (op U) (σ U (p.right.hom.app (op U) b) x)) =
          b * @id (B.right.obj.obj (op U)) (i.val.app (op U) x)) ∧
      (∀ (U V : X.Opens) (j : V ⟶ U) (f : C.right.obj.obj (op U)) (x : I.val.obj (op U)),
        I.val.map j.op (σ U f x) = σ V (C.right.obj.map j.op f) (I.val.map j.op x)) ∧
      (∀ (f : C.right.obj.obj (op ⊤)) (U : X.Opens) (x : I.val.obj (op U)),
        (μ f).val.app (op U) x = σ U (C.right.obj.map (homOfLE le_top).op f) x) ∧
      (∀ f : C.right.obj.obj (op ⊤), ρ f =
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).map (μ f)).hom) ∧
      (∀ f : C.right.obj.obj (op ⊤), δ f =
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
            (commAlgebraSheafModule X.sheaf C) ≫
          (IC.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 0).hom ≫
          hΓ.δ 0 1 rfl ≫
          (IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1).inv).hom
            f)) ∧
      ∀ f g : C.right.obj.obj (op ⊤), δ (f * g) = ρ f (δ g) + ρ g (δ f) := by
  sorry

end AlgebraicGeometry
