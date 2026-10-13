/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy

/-! # Resolution homology square for the identity scheme morphism

Source: Stacks Project, Cohomology of Sheaves, Remark 01FB; Derived Categories, Tag 013S.
(blueprint: lem-weil-pbc-module-cohomology-fmap-identity-resolution-homology).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

set_option maxHeartbeats 800000 in
-- Identity pushforward and the sections functor require substantial definitional reduction.
set_option backward.isDefEq.respectTransparency.types false in
/-- The horizontal map in the identity-scheme construction factors on sections homology
through the ordinary resolution descent and the vertical comparison. No derived-functor
resolution transports are part of this conclusion.
Source: Stacks Project, Cohomology of Sheaves, Remark 01FB; Derived Categories, Tag 013S.
(blueprint: lem-weil-pbc-module-cohomology-fmap-identity-resolution-homology).

Proof:
1. Let alpha be the ordinary resolution descent of psi from D.J to D.I. The inverse
   pushforward-identity comparison, applied degreewise, identifies D.I with its identity
   pushforward. Follow it by D.lambda to obtain l : D.I.cocomplex ⟶ D.K.
2. The descent augmentation equation and D.compatible imply that D.beta and alpha
   followed by l have equal composites with the augmentation of D.J. The latter is a
   quasi-isomorphism; D.K has injective terms and is bounded below. Extend by zero to
   integer indices and apply uniqueness up to homotopy (013S), then restrict back to
   natural indices. Thus beta and alpha followed by l are homotopic.
3. Apply additive global sections and then homology. This gives H(beta) = H(alpha)H(l).
   The component formula D.sections identifies D.a with global sections of the inverse
   pushforward-identity comparison: both are identity on sections, using the canonical
   restriction along id^{-1}(Z) = Z. Hence sections of l are D.a followed by sections
   of D.lambda. Substitute this equality to get the asserted factorization. The proof
   works for every D, so no independence theorem is needed.
-/
theorem moduleCohomologyFMap_identity_resolution_homology {Z : Scheme.{u}}
    (G F : SheafOfModules.{u} Z.ringCatSheaf) (ψ : G ⟶ F)
    (D : ModuleCohomologyFMapData (𝟙 Z) G F ψ) (p : ℕ) :
    let Γ := RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}
    let Γc := Γ.mapHomologicalComplex (ComplexShape.up ℕ)
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
    H.map (Γc.map D.β) =
      H.map (Γc.map (InjectiveResolution.desc ψ D.I D.J)) ≫
        H.map (D.a.hom ≫ Γc.map D.lambda) := by
  dsimp only
  let Γ := RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}
  let Γc := Γ.mapHomologicalComplex (ComplexShape.up ℕ)
  let c : D.I.cocomplex ⟶
      ((pushforward (𝟙 Z)).mapHomologicalComplex (ComplexShape.up ℕ)).obj D.I.cocomplex :=
    { f := fun n ↦ (pushforwardId Z).inv.app (D.I.cocomplex.X n)
      comm' := by
        intro n m _
        exact (pushforwardId Z).inv.naturality (D.I.cocomplex.d n m) }
  let α := InjectiveResolution.desc ψ D.I D.J
  have hc : Γc.map c = D.a.hom := by
    rw [← cancel_epi D.a.inv, Iso.inv_hom_id]
    apply HomologicalComplex.hom_ext
    intro n
    rw [HomologicalComplex.comp_f, D.sections]
    change (presheaf (D.I.cocomplex.X n)).map _ ≫
      ((pushforwardId Z).inv.app (D.I.cocomplex.X n)).app ⊤ = 𝟙 _
    simp
  have haug : D.J.ι ≫ D.β = D.J.ι ≫ (α ≫ c ≫ D.lambda) := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f]
    rw [D.compatible]
    dsimp [α, c]
    rw [← Category.assoc, ← Category.assoc, InjectiveResolution.desc_commutes_zero]
    congr 1
  let : ∀ n, Injective (D.K.X n) := D.injective
  let e := ComplexShape.embeddingUpNat
  let E := e.extendFunctor Z.Modules
  have : QuasiIso (E.map D.J.ι) :=
    (HomologicalComplex.quasiIso_extendMap_iff D.J.ι e).2 inferInstance
  have haugE : Nonempty (Homotopy (E.map D.J.ι ≫ E.map D.β)
      (E.map D.J.ι ≫ E.map (α ≫ c ≫ D.lambda))) := by
    rw [← E.map_comp, ← E.map_comp]
    exact ⟨(Homotopy.ofEq haug).extend e⟩
  obtain ⟨hhE⟩ := CochainComplex.homotopy_of_comp_quasiIso_of_injective
    (I := D.K.extend e)
    ⟨0, fun n hn ↦ CochainComplex.isZero_of_isStrictlyGE _ 0 n hn⟩
    (E.map D.J.ι) (E.map D.β) (E.map (α ≫ c ≫ D.lambda)) haugE
  have hh : Homotopy D.β (α ≫ c ≫ D.lambda) := hhE.ofExtend
  have hm := Γ.mapHomotopy hh
  change Homotopy (Γc.map D.β) (Γc.map (α ≫ c ≫ D.lambda)) at hm
  have hsec : Homotopy (Γc.map D.β) (Γc.map α ≫ D.a.hom ≫ Γc.map D.lambda) := by
    simpa only [Functor.map_comp, hc] using hm
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
  have hhom := hsec.homologyMap_eq p
  change H.map (Γc.map D.β) = H.map (Γc.map α ≫ D.a.hom ≫ Γc.map D.lambda) at hhom
  simpa only [Functor.map_comp, Category.assoc] using hhom

end AlgebraicGeometry.Scheme.Modules
