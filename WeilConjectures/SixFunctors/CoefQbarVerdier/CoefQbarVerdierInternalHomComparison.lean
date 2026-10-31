/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import WeilConjectures.SixFunctors.CoefQbarVerdier.HomComparison.CoefQbarVerdierHomComparisonExtension

/-! Finite-origin comparison descent for the common-stage internal Hom.

Source: blueprint thm-coef-qbar-verdier, proof step 5
(blueprint: lem-coef-qbar-verdier-internal-hom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

private theorem square_inv {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) {X Y : C} (eX : F.obj X ≅ G.obj X) (eY : F.obj Y ≅ G.obj Y)
    (s : X ≅ Y) (h : F.map s.hom ≫ eY.hom = eX.hom ≫ G.map s.hom) :
    F.map s.inv ≫ eX.hom = eY.hom ≫ G.map s.inv := by
  apply (cancel_epi (F.map s.hom)).mp
  rw [← Category.assoc, ← F.map_comp, s.hom_inv_id, F.map_id, Category.id_comp]
  rw [← Category.assoc, h, Category.assoc, ← G.map_comp,
    s.hom_inv_id, G.map_id, Category.comp_id]

private theorem square_comp {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) {X Y Z : C} (eX : F.obj X ≅ G.obj X)
    (eY : F.obj Y ≅ G.obj Y) (eZ : F.obj Z ≅ G.obj Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : F.map f ≫ eY.hom = eX.hom ≫ G.map f)
    (hg : F.map g ≫ eZ.hom = eY.hom ≫ G.map g) :
    F.map (f ≫ g) ≫ eZ.hom = eX.hom ≫ G.map (f ≫ g) := by
  rw [F.map_comp, G.map_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

private noncomputable def isoOfStageSquares
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)] (S : StageSystem C)
    {A : Type*} [Category A] (F G : S.PairCategoryᵒᵖ ⥤ A)
    (e : ∀ K : S.PairCategory, F.obj (op K) ≅ G.obj (op K))
    (hs : ∀ i (K M : C i) (f : K ⟶ M),
      F.map ((S.ι i).map f).op ≫ (e ((S.ι i).obj K)).hom =
        (e ((S.ι i).obj M)).hom ≫ G.map ((S.ι i).map f).op)
    (ht : ∀ (K : S.PairCategory) (L : I) (h : K.stage ≤ L),
      F.map (S.isoToStage K h).hom.op ≫ (e K).hom =
        (e ((S.ι L).obj (K.toStage h))).hom ≫ G.map (S.isoToStage K h).hom.op) :
    F ≅ G :=
  NatIso.ofComponents (fun K ↦ e K.unop) (fun {K M} f ↦ by
    obtain ⟨L, -, hM, hK, a, ha⟩ :=
      StageSystem.PairCategory.exists_le_mkHom_eq f.unop K.unop.stage
    have hf : f = (StageSystem.PairCategory.mkHom L hM hK a).op := by
      simpa using congrArg Quiver.Hom.op ha
    rw [hf]
    have hi := square_inv F G (e ((S.ι L).obj (K.unop.toStage hK))) (e K.unop)
      (S.isoToStage K.unop hK).op (ht K.unop L hK)
    have h₁ := square_comp F G (e K.unop) (e ((S.ι L).obj (K.unop.toStage hK)))
      (e ((S.ι L).obj (M.unop.toStage hM)))
      (S.isoToStage K.unop hK).inv.op ((S.ι L).map a).op hi (hs L _ _ a)
    have h₂ := square_comp F G (e K.unop) (e ((S.ι L).obj (M.unop.toStage hM)))
      (e M.unop) _ (S.isoToStage M.unop hM).hom.op h₁ (ht M.unop L hM)
    simpa only [StageSystem.mkHom_eq_isoToStage, op_comp, Functor.map_comp,
      Category.assoc] using h₂)

namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The finite-origin duality comparisons glue to the common-stage Hom functor.
Source: blueprint thm-coef-qbar-verdier, proof step 5
(blueprint: lem-coef-qbar-verdier-internal-hom).
(blueprint: lem-coef-qbar-verdier-internal-hom-comparison).
Proof: choose a literal compositum for each pair. The finite HomIdentification
comparison is compatible with every scalar transition by the recorded beta and
normalization equations. Eventual equality of representatives therefore gives a
natural isomorphism from the descended dual to `homDual`. -/
theorem internal_hom_comparison_exists (B : Duality D l hl Ω X) :
    ∃ permitted : ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω X,
      commonStageHomPairs l Ω X (op K, B.omega),
      Nonempty (B.duality.dual ≅ homDual l Ω X B.omega permitted) := by
  let permitted := fun K ↦ HomComparison.allPairs l Ω X D hl B.finite K B.omega
  refine ⟨permitted, ⟨isoOfStageSquares
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)
    B.duality.dual (homDual l Ω X B.omega permitted)
    (HomComparison.component l Ω X D hl B) ?_ ?_⟩⟩
  · intro E K M f
    exact HomComparison.component_naturality_stage l Ω X D hl B E f
  · intro K L h
    exact HomComparison.component_extension D l hl Ω X B K L h

end WeilConjectures.CoefQbarVerdier
