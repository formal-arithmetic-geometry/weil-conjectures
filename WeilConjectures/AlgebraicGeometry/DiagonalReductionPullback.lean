/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all WeilConjectures.ProperBaseChange.ConstantCompletionCore

/-! # Whole-system comparison for simultaneous reduction

Source: blueprint diagonal coefficient changes, paragraph (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

section Ordinary
variable {A B C D : Type*}
  [Category A] [Abelian A] [Category B] [Abelian B]
  [Category C] [Abelian C] [Category D] [Abelian D]
  (l : ℕ) (L : A ⥤ B) (L' : C ⥤ D)
  (F : A ⥤ C) (G : B ⥤ D) [G.Additive] [PreservesFiniteColimits G]
  (s : L ⋙ G ≅ F ⋙ L')
  (O : DiagonalReductionPresentation l L) (P : DiagonalReductionPresentation l L')

private def reductionLevelIso (n : ℕ) (M : A) :
    G.obj ((O.E.obj M).obj (op n)) ≅ (P.E.obj (F.obj M)).obj (op n) := by
  let f := l ^ (n + 1) • 𝟙 (L.obj M)
  let f' := l ^ (n + 1) • 𝟙 (L'.obj (F.obj M))
  let c := (O.quotient n M).coconePointUniqueUpToIso (cokernelIsCokernel f)
  let d := (cokernelIsCokernel f').coconePointUniqueUpToIso (P.quotient n (F.obj M))
  let e := cokernel.mapIso (G.map f) f' (s.app M) (s.app M) (by
    simp only [f, f', G.map_nsmul, G.map_id,
      Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp, Category.comp_id])
  exact G.mapIso c ≪≫ (asIso (cokernelComparison f G)).symm ≪≫ e ≪≫ d

private theorem reductionLevelIso_normalization (n : ℕ) (M : A) :
    G.map ((O.π n).app M) ≫ (reductionLevelIso l L L' F G s O P n M).hom =
      s.hom.app M ≫ (P.π n).app (F.obj M) := by
  let f := l ^ (n + 1) • 𝟙 (L.obj M)
  let f' := l ^ (n + 1) • 𝟙 (L'.obj (F.obj M))
  have hO : (O.π n).app M ≫
      ((O.quotient n M).coconePointUniqueUpToIso (cokernelIsCokernel f)).hom =
        cokernel.π f :=
    (O.quotient n M).comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel f) WalkingParallelPair.one
  have hP : cokernel.π f' ≫
      ((cokernelIsCokernel f').coconePointUniqueUpToIso (P.quotient n (F.obj M))).hom =
        (P.π n).app (F.obj M) :=
    (cokernelIsCokernel f').comp_coconePointUniqueUpToIso_hom
      (P.quotient n (F.obj M)) WalkingParallelPair.one
  have hG : G.map (cokernel.π f) ≫ inv (cokernelComparison f G) =
      cokernel.π (G.map f) := by
    apply (cancel_mono (cokernelComparison f G)).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      π_comp_cokernelComparison]
  dsimp only [reductionLevelIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    asIso_inv, cokernel.mapIso_hom]
  rw [← G.map_comp_assoc, hO, ← Category.assoc, hG]
  simp only [cokernel.mapIso_hom, cokernel.map]
  dsimp only [f, f'] at hP ⊢
  rw [cokernel.π_desc_assoc, Category.assoc, hP]
  rfl

/-- Exact inverse image commutes with the whole ordinary quotient system, with
its prescribed quotient maps and all transition morphisms.
Source: blueprint diagonal coefficient changes, paragraph (3)
(blueprint: lem-diagonal-reduction-pullback).
Proof: inverse image preserves the cokernel of each prime-power multiplication.
The supplied scalar comparison conjugates this multiplication to the corresponding
multiplication on the new base. The cokernel universal property gives an
isomorphism preserving its quotient map. Since these quotient maps are epic,
cancellation identifies the transition squares and naturality in the input.
Thus the level comparisons assemble to one isomorphism of strict systems; no
detection of derived arrows by finite evaluations is asserted. -/
theorem diagonalOrdinaryReduction_pullback :
    ∃ e : O.E ⋙ (Functor.whiskeringRight ℕᵒᵖ B D).obj G ≅ F ⋙ P.E,
      ∀ (n : ℕ) (M : A),
        G.map ((O.π n).app M) ≫ (e.hom.app M).app (op n) =
          s.hom.app M ≫ (P.π n).app (F.obj M) := by
  let e (M : A) (n : ℕ) := reductionLevelIso l L L' F G s O P n M
  have he (M : A) (n : ℕ) : G.map ((O.π n).app M) ≫ (e M n).hom =
      s.hom.app M ≫ (P.π n).app (F.obj M) :=
    reductionLevelIso_normalization l L L' F G s O P n M
  have epiπ (M : A) (n : ℕ) : Epi (G.map ((O.π n).app M)) := by
    have : Epi ((O.π n).app M) := Cofork.IsColimit.epi (O.quotient n M)
    infer_instance
  let t (M : A) : (O.E.obj M) ⋙ G ⟶ P.E.obj (F.obj M) := by
    exact NatTrans.ofOpSequence (fun n ↦ (e M n).hom) (by
      intro n
      let := epiπ M (n + 1)
      apply (cancel_epi (G.map ((O.π (n + 1)).app M))).1
      change G.map ((O.π (n + 1)).app M) ≫
          (G.map ((O.E.obj M).map (homOfLE (Nat.le_succ n)).op) ≫ (e M n).hom) =
        G.map ((O.π (n + 1)).app M) ≫
          ((e M (n + 1)).hom ≫ (P.E.obj (F.obj M)).map
            (homOfLE (Nat.le_succ n)).op)
      rw [← G.map_comp_assoc, O.transition, he, ← Category.assoc, he,
        Category.assoc, P.transition])
  have ht (M : A) : IsIso (t M) := by
    have (n : ℕᵒᵖ) : IsIso ((t M).app n) :=
      inferInstanceAs (IsIso (e M n.unop).hom)
    exact NatIso.isIso_of_isIso_app _
  let := ht
  refine ⟨NatIso.ofComponents (fun M ↦ asIso (t M)) ?_, fun n M ↦ he M n⟩
  intro M N f
  apply NatTrans.ext
  funext n
  let := epiπ M n.unop
  apply (cancel_epi (G.map ((O.π n.unop).app M))).1
  change G.map ((O.π n.unop).app M) ≫
      (G.map ((O.E.map f).app n) ≫ (e N n.unop).hom) =
    G.map ((O.π n.unop).app M) ≫
      ((e M n.unop).hom ≫ (P.E.map (F.map f)).app n)
  have hO : L.map f ≫ (O.π n.unop).app N =
      (O.π n.unop).app M ≫ (O.E.map f).app n := (O.π n.unop).naturality f
  have hP : L'.map (F.map f) ≫ (P.π n.unop).app (F.obj N) =
      (P.π n.unop).app (F.obj M) ≫ (P.E.map (F.map f)).app n :=
    (P.π n.unop).naturality (F.map f)
  rw [← G.map_comp_assoc, ← hO, G.map_comp_assoc, he]
  rw [reassoc_of% (he M n.unop)]
  change G.map (L.map f) ≫ s.hom.app N ≫ (P.π n.unop).app (F.obj N) = _
  calc
    _ = s.hom.app M ≫ L'.map (F.map f) ≫ (P.π n.unop).app (F.obj N) := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun z ↦ z ≫ (P.π n.unop).app (F.obj N)) (s.hom.naturality f)
    _ = _ := by rw [hP]

end Ordinary

/-- The ordinary quotient square descends to a comparison of derived strict systems.
Source: blueprint diagonal coefficient changes, paragraph (3)
(blueprint: lem-diagonal-reduction-pullback).
Proof: choose a common resolving representative on which both supplied reduction
counits are invertible. Exact inverse image is already computed on every complex.
Apply the ordinary strict-system comparison on that representative, and conjugate
by the two computation counits. Resolving-class localization extends this comparison
uniquely to a natural isomorphism on the entire derived category. Its stated equation
is its representative normalization, so it fixes all coherence data. -/
theorem diagonalDerivedReduction_pullback
    {A B C D : Type*}
    [Category A] [Abelian A] [Category B] [Abelian B]
    [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory C]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (l : ℕ) (L : A ⥤ B) (L' : C ⥤ D)
    (F : A ⥤ C) (G : B ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (s : L ⋙ G ≅ F ⋙ L')
    (K : DiagonalDerivedReduction l L) (K' : DiagonalDerivedReduction l L')
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ X : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (p : P ⟶ X), good P ∧ QuasiIso p)
    (hK : ∀ P, good P → IsIso (K.ε.app P))
    (hK' : ∀ P, good P → IsIso
      (K'.ε.app ((F.mapHomologicalComplex (.up ℤ)).obj P))) :
    let V := (Functor.whiskeringRight ℕᵒᵖ B D).obj G
    ∃ (e : K.ordinary.E ⋙ V ≅ F ⋙ K'.ordinary.E)
      (q : K.T ⋙ V.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ K'.T),
      (∀ (n : ℕ) (M : A),
        G.map ((K.ordinary.π n).app M) ≫ (e.hom.app M).app (op n) =
          s.hom.app M ≫ (K'.ordinary.π n).app (F.obj M)) ∧
      ∀ P, good P →
        V.mapDerivedCategory.map (K.ε.app P) ≫
            V.mapDerivedCategoryFactors.hom.app
              ((K.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) =
          q.hom.app (DerivedCategory.Q.obj P) ≫
            K'.T.map (F.mapDerivedCategoryFactors.hom.app P) ≫
            K'.ε.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  let V := (Functor.whiskeringRight ℕᵒᵖ B D).obj G
  obtain ⟨e, he⟩ := diagonalOrdinaryReduction_pullback l L L' F G s
    K.ordinary K'.ordinary
  obtain ⟨q, hq, _⟩ := CategoryTheory.ConstantCompletion.resolving_square_iso
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (K.ordinary.E.mapHomologicalComplex (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ))
    (V.mapHomologicalComplex (.up ℤ))
    (K'.ordinary.E.mapHomologicalComplex (.up ℤ))
    K.T F.mapDerivedCategory V.mapDerivedCategory K'.T
    K.ε V.mapDerivedCategoryFactors.hom (NatIso.mapHomologicalComplex e (.up ℤ))
    F.mapDerivedCategoryFactors.hom K'.ε good res hK
    (fun _ _ ↦ inferInstance) (fun _ _ ↦ inferInstance) hK'
  exact ⟨e, q, he, hq⟩

end AlgebraicGeometry.ProEtale
