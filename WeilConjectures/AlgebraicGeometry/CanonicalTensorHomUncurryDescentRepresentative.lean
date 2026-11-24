/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Existence of representative-normalized values, without isomorphism transport
(Stacks, Tags 08DJ, 0A90 and 0A96). -/
theorem exists_tensorHomUncurry_descent_representative (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := schemeDerivedTensorMonoidal X
    ∃ t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      ∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlatTensor →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M := by
  classical
  let := schemeDerivedTensorMonoidal X
  let R (K L M : schemeDerivedCategory X)
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) (g : K ⊗ L ⟶ M) : Prop :=
    ∃ (P Lc Mc : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (hP : P.IsKFlatTensor)
      (φ : P ⟶ homComplex (R := X.sheaf) Lc
        ((schemeHomKInjectiveResolution X).obj Mc)),
      DerivedCategory.Q.obj P = K ∧ DerivedCategory.Q.obj Lc = L ∧
      DerivedCategory.Q.obj Mc = M ∧
      HEq (DerivedCategory.Q.map φ ≫
        (schemeDerivedInternalHomResolutionIso X Lc Mc).inv) f ∧
      HEq (pullbackTensorModelMap X P Lc ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P Lc Mc φ) ≫
          schemeHomResolutionInverse X Mc) g
  have unique (K L M : schemeDerivedCategory X) (f) (g g' : K ⊗ L ⟶ M)
      (hg : R K L M f g) (hg' : R K L M f g') : g = g' := by
    obtain ⟨P, Lc, Mc, hP, φ, hK, hL, hM, hφ, hψ⟩ := hg
    obtain ⟨P', Lc', Mc', hP', φ', hK', hL', hM', hφ', hψ'⟩ := hg'
    have h := tensorHomUncurry_representative_coherence X P Lc Mc P' Lc' Mc'
      hP hP' φ φ' (hK.trans hK'.symm) (hL.trans hL'.symm)
      (hM.trans hM'.symm) (hφ.trans hφ'.symm)
    exact eq_of_heq (hψ.symm.trans (h.trans hψ'))
  let t (K L M : schemeDerivedCategory X) (f) : K ⊗ L ⟶ M :=
    if h : ∃! g, R K L M f g then Classical.choose h else 0
  refine ⟨t, ?_⟩
  intro P L M hP φ
  let g := pullbackTensorModelMap X P L ≫
    DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
      schemeHomResolutionInverse X M
  have hg : R (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L)
      (DerivedCategory.Q.obj M)
      (DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv) g :=
    ⟨P, L, M, hP, φ, rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩
  have hex : ∃! g, R (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L)
      (DerivedCategory.Q.obj M)
      (DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv) g :=
    ⟨g, hg, fun g' hg' ↦ unique _ _ _ _ _ _ hg' hg⟩
  dsimp only [t]
  rw [dite_eq_left hex]
  exact unique _ _ _ _ _ g (Classical.choose_spec hex).1 hg

end AlgebraicGeometry
