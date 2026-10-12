module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.PicardH1LocalDescent
import Sheaf.AlgebraicGeometry.ProductUniversalStructurePushforward
import Sheaf.AlgebraicGeometry.ProductResidueH1Injective
import Mathlib.Tactic.FinCases

/-! Explicit-isomorphism form of the geometric Picard product openness construction.

Source: Stacks Project, More on Morphisms, Lemma pic-of-product, Tag 0BF3
(blueprint: lem-sc-picard-product-open-data).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

private noncomputable def tensorPullbackIsoPullback {A B : Scheme.{u}} (g : A ⟶ B) :
    Modules.tensorPullback g ≅ Modules.pullback g :=
  (Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction g)

private theorem descended_iso_unit_of_section
    {P S : Scheme.{u}} (p : P ⟶ S) (r : S ⟶ P) (hr : r ≫ p = 𝟙 S)
    (L : P.Modules)
    (he : Nonempty ((Modules.pullback r).obj L ≅ SheafOfModules.unit S.ringCatSheaf))
    (U : S.Opens) (N : U.toScheme.Modules)
    (e : (Modules.tensorPullback (pullback.fst p U.ι)).obj L ≅
      (Modules.tensorPullback (pullback.snd p U.ι)).obj N) :
    Nonempty ((Modules.tensorPullback (pullback.fst p U.ι)).obj L ≅
      SheafOfModules.unit (pullback p U.ι).ringCatSheaf) := by
  obtain ⟨er⟩ := he
  let q := pullback.fst p U.ι
  let b := pullback.snd p U.ι
  let t : U.toScheme ⟶ pullback p U.ι :=
    pullback.lift (U.ι ≫ r) (𝟙 _) (by simp [hr])
  have htq : t ≫ q = U.ι ≫ r := pullback.lift_fst _ _ _
  have htb : t ≫ b = 𝟙 _ := pullback.lift_snd _ _ _
  let e' : (Modules.pullback q).obj L ≅ (Modules.pullback b).obj N :=
    (tensorPullbackIsoPullback q).symm.app L ≪≫ e ≪≫
      (tensorPullbackIsoPullback b).app N
  let eN : N ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
    ((Modules.pullbackId _).app N).symm ≪≫
      (Modules.pullbackCongr htb).symm.app N ≪≫
      (Modules.pullbackComp t b).symm.app N ≪≫
      (Modules.pullback t).mapIso e'.symm ≪≫
      (Modules.pullbackComp t q).app L ≪≫
      (Modules.pullbackCongr htq).app L ≪≫
      (Modules.pullbackComp U.ι r).symm.app L ≪≫
      (Modules.pullback U.ι).mapIso er ≪≫ Modules.pullbackObjUnitIso U.ι
  exact ⟨(tensorPullbackIsoPullback q).app L ≪≫ e' ≪≫
    (Modules.pullback b).mapIso eN ≪≫ Modules.pullbackObjUnitIso b⟩

set_option linter.unusedVariables false in
/-- The geometric construction returns explicit isomorphisms for both factors.
Source: Stacks Project, Tag 0BF3, Picard-locus construction.
The explicit-isomorphism output is the data-level form used to compose the auxiliary
module trivialization in `picard_product_open_core`.
(blueprint: lem-sc-picard-product-open-data). -/
theorem picard_product_open_data
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [Flat g] [IsProper g] [LocallyOfFinitePresentation g]
    (σ : S ⟶ X) (τ : S ⟶ Y)
    (hσ : σ ≫ f = 𝟙 S) (hτ : τ ≫ g = 𝟙 S)
    (s : S) (L : (pullback f g).Modules) [L.IsInvertible]
    (hO : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f t))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hO' : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd g t))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (h₁ : Nonempty ((Scheme.Modules.tensorPullback
      (pullback.lift (𝟙 X) (f ≫ τ) (by simp [hτ]))).obj L ≅
        SheafOfModules.unit X.ringCatSheaf))
    (h₂ : Nonempty ((Scheme.Modules.tensorPullback
      (pullback.lift (g ≫ σ) (𝟙 Y) (by simp [hσ]))).obj L ≅
        SheafOfModules.unit Y.ringCatSheaf))
    (hs : Nonempty ((Scheme.Modules.tensorPullback
      ((pullback.fst f g ≫ f).fiberι s)).obj L ≅ SheafOfModules.unit _)) :
    ∃ U : S.Opens, s ∈ U ∧ ∃ N : (pullback (pullback.fst f g ≫ f) U.ι).Modules,
      ∃ eL : (Scheme.Modules.tensorPullback
        (pullback.fst (pullback.fst f g ≫ f) U.ι)).obj L ≅ N,
      ∃ eN : N ≅ SheafOfModules.unit
        (pullback (pullback.fst f g ≫ f) U.ι).ringCatSheaf, True := by
  let p := pullback.fst f g ≫ f
  let iX : X ⟶ pullback f g := pullback.lift (𝟙 X) (f ≫ τ) (by simp [hτ])
  let iY : Y ⟶ pullback f g := pullback.lift (g ≫ σ) (𝟙 Y) (by simp [hσ])
  have hiX : iX ≫ p = f := by
    dsimp only [p]
    rw [← Category.assoc, pullback.lift_fst, Category.id_comp]
  have hiY : iY ≫ p = g := by
    dsimp only [p]
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, hσ, Category.comp_id]
  let Xi : Fin 2 → Scheme.{u} := Fin.cases X (fun _ ↦ Y)
  let fi : ∀ i, Xi i ⟶ S := Fin.cases f (fun _ ↦ g)
  let ui : ∀ i, Xi i ⟶ pullback f g := Fin.cases iX (fun _ ↦ iY)
  have hui : ∀ i, ui i ≫ p = fi i := by
    intro i
    fin_cases i
    · exact hiX
    · exact hiY
  have : ∀ i, Flat (fi i) := by intro i; fin_cases i <;> assumption
  have : ∀ i, IsProper (fi i) := by intro i; fin_cases i <;> assumption
  have : ∀ i, LocallyOfFinitePresentation (fi i) := by
    intro i; fin_cases i <;> assumption
  have hOi : ∀ i, ∀ {T : Scheme.{u}} (t : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd (fi i) t))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)) := by
    intro i
    fin_cases i
    · exact hO
    · exact hO'
  have hLi : ∀ i, Nonempty ((Modules.tensorPullback (ui i)).obj L ≅
      SheafOfModules.unit (Xi i).ringCatSheaf) := by
    intro i
    fin_cases i
    · exact h₁
    · exact h₂
  have hpair := product_residue_h1_injective f g σ τ hσ hτ hO hO' s
  have hH : Function.Injective (fun x :
        Sheaf.H (structureSheafAb (pullback p (S.fromSpecResidueField s))) 1 ↦ fun i ↦
      structureSheafCohomologyPullback
        (((Over.pullback (S.fromSpecResidueField s)).map
          (Over.homMk (U := Over.mk (fi i)) (V := Over.mk p) (ui i) (hui i))).left) 1 x) := by
    intro x y hxy
    apply hpair
    apply Prod.ext
    · exact congrFun hxy 0
    · exact congrFun hxy 1
  obtain ⟨U, hsU, N, _, ⟨e⟩⟩ := picard_h1_local_descent p Xi fi ui hui
    (product_universal_structure_pushforward f g hO hO') hOi L hLi s hs hH
  let r := σ ≫ iX
  have hr : r ≫ p = 𝟙 S := by rw [Category.assoc, hiX]; exact hσ
  obtain ⟨eX⟩ := h₁
  have er : Nonempty ((Modules.pullback r).obj L ≅ SheafOfModules.unit S.ringCatSheaf) :=
    ⟨(Modules.pullbackComp σ iX).symm.app L ≪≫
      (Modules.pullback σ).mapIso
        ((tensorPullbackIsoPullback iX).symm.app L ≪≫ eX) ≪≫
      Modules.pullbackObjUnitIso σ⟩
  obtain ⟨eL⟩ := descended_iso_unit_of_section p r hr L er U N e
  exact ⟨U, hsU, SheafOfModules.unit _, eL, Iso.refl _, trivial⟩

end AlgebraicGeometry.Scheme
