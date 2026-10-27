module

public import Mathlib.CategoryTheory.NatIso

/-! # Inverse comparisons and counit transport

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md, first paragraph,
inverse automorphism squares and identity pasting.
(blueprint: lem-pod-inverse-comparison-counit-transport)
-/

@[expose] public section

set_option autoImplicit false

universe vCE vDE vCL vDL uCE uDE uCL uDL

namespace CategoryTheory

/-- The component `v = u H(κ⁻¹) ρ⁻¹`, in diagrammatic composition order.
Source: lem-fix-weil-operations.proof.md, first paragraph, the categorical extraction
of inverse comparison and counit pasting in the node statement.
(blueprint: lem-pod-inverse-comparison-counit-transport) -/
def inverseComparisonCounitApp
    {C : Type uCE} [Category.{vCE} C] {D : Type uDE} [Category.{vDE} D]
    {P G : C ⥤ D} {Q H : D ⥤ C}
    (κ : G ≅ P) (ρ : H ≅ Q) (u : G ⋙ H ≅ 𝟭 C) (K : C) :
    Q.obj (P.obj K) ⟶ K :=
  ρ.inv.app (P.obj K) ≫ H.map (κ.inv.app K) ≫ u.hom.app K

/-- Inverting the two compatible comparison squares transports the expanded counit,
naturally in the source object.
Source: lem-fix-weil-operations.proof.md, first paragraph, inverse automorphism squares
and identity pasting; the node's categorical extraction uses only the displayed data.
(blueprint: lem-pod-inverse-comparison-counit-transport)

Proof plan, following the six steps of the node:
1. Cancel κ on both sides of the first supplied square, using inverse identities and
   functoriality, to obtain the square for λ = κ⁻¹.
2. Cancel ρ in the second square in the same way to obtain the square for ν = ρ⁻¹.
3. Cancel κ and ρ in their naturality equations to obtain naturality of λ and ν.
4. Expand v on the left of the counit formula and move ν past Q(a) by naturality.
   Functoriality combines the resulting H factors into H(a followed by λ).
5. Substitute the two inverse squares, the second at P_E(K). Apply naturality of e
   to λ_E(K), then combine the final T_C factors by functoriality. This gives exactly
   the expanded right side, with source T_C Q_E P_E(K) and target T_C(K).
6. Naturality of ν, λ and u gives naturality of v. Naturality of a and d then gives
   the final displayed naturality equation for the left side. The pointwise equality
   transfers this equation to the right side. Every step uses only category laws
   (def-nagata-category); no relation between u_E and u_L is needed. -/
theorem inverseComparisonCounitTransport
    {CE : Type uCE} [Category.{vCE} CE] {DE : Type uDE} [Category.{vDE} DE]
    {CL : Type uCL} [Category.{vCL} CL] {DL : Type uDL} [Category.{vDL} DL]
    (TC : CE ⥤ CL) (TD : DE ⥤ DL)
    (PE GE : CE ⥤ DE) (QE HE : DE ⥤ CE)
    (PL GL : CL ⥤ DL) (QL HL : DL ⥤ CL)
    (κE : GE ≅ PE) (ρE : HE ≅ QE) (_uE : GE ⋙ HE ≅ 𝟭 CE)
    (κL : GL ≅ PL) (ρL : HL ≅ QL) (uL : GL ⋙ HL ≅ 𝟭 CL)
    (a : PE ⋙ TD ≅ TC ⋙ PL) (d : QE ⋙ TC ≅ TD ⋙ QL)
    (b : GE ⋙ TD ≅ TC ⋙ GL) (e : HE ⋙ TC ≅ TD ⋙ HL)
    (hκ : ∀ K : CE, TD.map (κE.hom.app K) ≫ a.hom.app K =
      b.hom.app K ≫ κL.hom.app (TC.obj K))
    (hρ : ∀ M : DE, TC.map (ρE.hom.app M) ≫ d.hom.app M =
      e.hom.app M ≫ ρL.hom.app (TD.obj M)) :
    (∀ K : CE, a.hom.app K ≫ κL.inv.app (TC.obj K) =
      TD.map (κE.inv.app K) ≫ b.hom.app K) ∧
    (∀ M : DE, d.hom.app M ≫ ρL.inv.app (TD.obj M) =
      TC.map (ρE.inv.app M) ≫ e.hom.app M) ∧
    (∀ K : CE,
      d.hom.app (PE.obj K) ≫ QL.map (a.hom.app K) ≫
          inverseComparisonCounitApp κL ρL uL (TC.obj K) =
        TC.map (ρE.inv.app (PE.obj K) ≫ HE.map (κE.inv.app K)) ≫
          (e.hom.app (GE.obj K) ≫ HL.map (b.hom.app K) ≫ uL.hom.app (TC.obj K))) ∧
    (∀ (K K' : CE) (t : K ⟶ K'),
      TC.map (QE.map (PE.map t)) ≫
          (d.hom.app (PE.obj K') ≫ QL.map (a.hom.app K') ≫
            inverseComparisonCounitApp κL ρL uL (TC.obj K')) =
        (d.hom.app (PE.obj K) ≫ QL.map (a.hom.app K) ≫
          inverseComparisonCounitApp κL ρL uL (TC.obj K)) ≫ TC.map t) := by
  have hκi (K : CE) : a.hom.app K ≫ κL.inv.app (TC.obj K) =
      TD.map (κE.inv.app K) ≫ b.hom.app K := by
    have h := congrArg
      (fun f ↦ TD.map (κE.inv.app K) ≫ f ≫ κL.inv.app (TC.obj K)) (hκ K)
    simpa [Category.assoc, ← Functor.map_comp_assoc] using h
  have hρi (M : DE) : d.hom.app M ≫ ρL.inv.app (TD.obj M) =
      TC.map (ρE.inv.app M) ≫ e.hom.app M := by
    have h := congrArg
      (fun f ↦ TC.map (ρE.inv.app M) ≫ f ≫ ρL.inv.app (TD.obj M)) (hρ M)
    simpa [Category.assoc, ← Functor.map_comp_assoc] using h
  refine ⟨hκi, hρi, ?_, ?_⟩
  · intro K
    unfold inverseComparisonCounitApp
    have nρ := ρL.inv.naturality (a.hom.app K)
    dsimp only [Functor.comp_obj, Functor.comp_map] at nρ
    rw [reassoc_of% nρ]
    rw [← Category.assoc (d.hom.app _) (ρL.inv.app _), hρi]
    simp only [Category.assoc]
    rw [← HL.map_comp_assoc, hκi, HL.map_comp, Category.assoc]
    have ne := e.hom.naturality (κE.inv.app K)
    dsimp only [Functor.comp_obj, Functor.comp_map] at ne
    rw [← reassoc_of% ne]
    simp only [Functor.map_comp, Category.assoc]
  · intro K K' t
    unfold inverseComparisonCounitApp
    simp only [Category.assoc]
    have nd := d.hom.naturality (PE.map t)
    dsimp only [Functor.comp_obj, Functor.comp_map] at nd
    rw [reassoc_of% nd]
    have na := a.hom.naturality t
    dsimp only [Functor.comp_obj, Functor.comp_map] at na
    rw [← QL.map_comp_assoc, na]
    simp only [Functor.map_comp, Category.assoc]
    rw [ρL.inv.naturality_assoc (PL.map (TC.map t))]
    rw [← HL.map_comp_assoc, κL.inv.naturality (TC.map t), HL.map_comp]
    simp only [Category.assoc]
    have nu := uL.hom.naturality (TC.map t)
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at nu
    rw [nu]

end CategoryTheory
