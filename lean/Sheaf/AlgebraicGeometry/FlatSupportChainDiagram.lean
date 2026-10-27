module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.FromJoel.Algebra.Homology.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Flat-term tensor and the strict open-kernel cochain diagram

Source: Stacks Project, sites-cohomology.tex, Tags 093X and 07A4; sites-modules.tex,
Tags 03DA, 03DB and 03ER. This is the agent-written cochain refinement of the Locality
support-row argument (blueprint: lem-pur-flat-support-chain-diagram).

All complexes and arrows are ordinary constant-coefficient module sheaves. The existing
`supportsShortComplex` is the actual kernel row, without an injectivity hypothesis.
The tensor comparison below totals the canonical ordinary monoidal comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] HomologicalComplex.monoidalCategoryStruct

universe u w uC uD
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale.OpenSupport

variable {C : Type uC} {D : Type uD}
  [Category.{w + 1} C] [Category.{w + 1} D] [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [BraidedCategory C] [BraidedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [F.IsLeftAdjoint] [F.Monoidal]

/-- The existing total tensor comparison of a strong monoidal left adjoint.
Source: Stacks 07A4 (blueprint: lem-pur-flat-support-chain-diagram). -/
def comparison (Q K : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (Q ⊗ K) ≅
      (F.mapHomologicalComplex (.up ℤ)).obj Q ⊗
        (F.mapHomologicalComplex (.up ℤ)).obj K :=
  asIso (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app Q).app K)

/-- The ordinary adjunction unit applied termwise.
Source: Stacks 03DA (blueprint: lem-pur-flat-support-chain-diagram). -/
abbrev restriction (adj : F ⊣ G) (I : CochainComplex C ℤ) :=
  (adj.mapHomologicalComplex (.up ℤ)).unit.app I

/-- Mathlib's existing kernel sequence of the termwise ordinary unit. At the etale
adjunction this is definitionally the upstream supportsShortComplex.
Source: Stacks 03DA (blueprint: lem-pur-flat-support-chain-diagram). -/
abbrev row (adj : F ⊣ G) (I : CochainComplex C ℤ) :=
  ShortComplex.kernelSequence (restriction adj I)

/-- The displayed h, using the ordinary counit and the canonical total comparison.
Source: Stacks 07A4 (blueprint: lem-pur-flat-support-chain-diagram). -/
def transpose (adj : F ⊣ G) (Q I J : CochainComplex C ℤ) (a : Q ⊗ I ⟶ J) :
    (F.mapHomologicalComplex (.up ℤ)).obj (Q ⊗ (row adj I).X₃) ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj J :=
  (comparison (F := F) Q (row adj I).X₃).hom ≫
    ((F.mapHomologicalComplex (.up ℤ)).obj Q ◁
      (adj.mapHomologicalComplex (.up ℤ)).counit.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I)) ≫
    (comparison (F := F) Q I).inv ≫ (F.mapHomologicalComplex (.up ℤ)).map a

/-- The specified adjunct v, constructed without commuting G with coproducts.
Source: Stacks 07A4 (blueprint: lem-pur-flat-support-chain-diagram). -/
def rightMap (adj : F ⊣ G) (Q I J : CochainComplex C ℤ) (a : Q ⊗ I ⟶ J) :
    Q ⊗ (row adj I).X₃ ⟶ (row adj J).X₃ :=
  (adj.mapHomologicalComplex (.up ℤ)).unit.app _ ≫
    (G.mapHomologicalComplex (.up ℤ)).map (transpose adj Q I J a)

/-- Functoriality of the existing kernel, applied to unit naturality.
Source: Stacks 03DA (blueprint: lem-pur-flat-support-chain-diagram). -/
def kernelMap (adj : F ⊣ G) {I J : CochainComplex C ℤ} (f : I ⟶ J) :
    (row adj I).X₁ ⟶ (row adj J).X₁ :=
  kernel.map (restriction adj I) (restriction adj J) f
    ((F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ)).map f)
    ((adj.mapHomologicalComplex (.up ℤ)).unit.naturality f).symm

@[reassoc]
private theorem comparison_naturality (Q : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℤ)).map (Q ◁ f) ≫ (comparison (F := F) Q L).hom =
      (comparison (F := F) Q K).hom ≫
        ((F.mapHomologicalComplex (.up ℤ)).obj Q ◁
          (F.mapHomologicalComplex (.up ℤ)).map f) := by
  exact (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app Q).naturality f)

@[reassoc]
private theorem comparison_inv_naturality (Q : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    ((F.mapHomologicalComplex (.up ℤ)).obj Q ◁
        (F.mapHomologicalComplex (.up ℤ)).map f) ≫ (comparison (F := F) Q L).inv =
      (comparison (F := F) Q K).inv ≫
        (F.mapHomologicalComplex (.up ℤ)).map (Q ◁ f) := by
  apply (cancel_epi (comparison (F := F) Q K).hom).1
  rw [← Category.assoc, ← comparison_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem rightMap_square (adj : F ⊣ G) (Q I J : CochainComplex C ℤ)
    (a : Q ⊗ I ⟶ J) :
    (Q ◁ (row adj I).g) ≫ rightMap adj Q I J a = a ≫ (row adj J).g := by
  let L := F.mapHomologicalComplex (.up ℤ)
  let R := G.mapHomologicalComplex (.up ℤ)
  let e := adj.mapHomologicalComplex (.up ℤ)
  have ht : L.map (Q ◁ e.unit.app I) ≫ transpose adj Q I J a = L.map a := by
    dsimp only [transpose, row, restriction, ShortComplex.kernelSequence]
    dsimp only [L, e]
    rw [comparison_naturality_assoc (F := F) Q
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app I),
      ← whiskerLeft_comp_assoc,
      (adj.mapHomologicalComplex (.up ℤ)).left_triangle_components I]
    erw [whiskerLeft_id]
    simp only [Category.id_comp, Functor.id_obj,
      Iso.hom_inv_id_assoc]
  change (Q ◁ e.unit.app I) ≫ (e.unit.app _ ≫ R.map _) = a ≫ e.unit.app J
  calc
    _ = e.unit.app _ ≫ R.map (L.map (Q ◁ e.unit.app I)) ≫
        R.map (transpose adj Q I J a) := by
      simpa only [Category.assoc, Functor.id_map, Functor.comp_map] using
        congrArg (fun t ↦ t ≫ R.map (transpose adj Q I J a))
          (e.unit.naturality (Q ◁ e.unit.app I))
    _ = e.unit.app _ ≫ R.map (L.map a) := by
      rw [← R.map_comp, ht]
      rfl
    _ = _ := (e.unit.naturality a).symm

private theorem rightMap_naturality (adj : F ⊣ G) (Q I J I' J' : CochainComplex C ℤ)
    (a : Q ⊗ I ⟶ J) (a' : Q ⊗ I' ⟶ J') (f : I ⟶ I') (g : J ⟶ J')
    (h : a ≫ g = (Q ◁ f) ≫ a') :
    rightMap adj Q I J a ≫
        ((F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ)).map g) =
      (Q ◁ ((F.mapHomologicalComplex (.up ℤ) ⋙
        G.mapHomologicalComplex (.up ℤ)).map f)) ≫ rightMap adj Q I' J' a' := by
  let L := F.mapHomologicalComplex (.up ℤ)
  let R := G.mapHomologicalComplex (.up ℤ)
  let e := adj.mapHomologicalComplex (.up ℤ)
  have ht : transpose adj Q I J a ≫ L.map g =
      L.map (Q ◁ R.map (L.map f)) ≫ transpose adj Q I' J' a' := by
    dsimp only [transpose, row, restriction, ShortComplex.kernelSequence]
    dsimp only [L, R, e, Functor.comp_obj]
    erw [comparison_naturality_assoc (F := F) Q (R.map (L.map f))]
    have hc := e.counit.naturality (L.map f)
    dsimp only [Functor.comp_map, Functor.id_map] at hc
    erw [← whiskerLeft_comp_assoc, hc, whiskerLeft_comp_assoc,
      comparison_inv_naturality_assoc (F := F) Q f]
    simp only [Category.assoc, ← Functor.map_comp, h]
    rfl
  dsimp only [rightMap, Functor.comp_map]
  change (e.unit.app _ ≫ R.map _) ≫ R.map (L.map g) =
    (Q ◁ R.map (L.map f)) ≫ (e.unit.app _ ≫ R.map _)
  rw [Category.assoc, ← R.map_comp, ht, R.map_comp]
  simpa only [Category.assoc, Functor.id_map, Functor.comp_map] using
    congrArg (fun t ↦ t ≫ R.map (transpose adj Q I' J' a'))
      (e.unit.naturality (Q ◁ R.map (L.map f))).symm

private theorem rightMap_summand (adj : F ⊣ G) (Q I J : CochainComplex C ℤ)
    (a : Q ⊗ I ⟶ J) (p q n : ℤ) (hpq : p + q = n) :
    HomologicalComplex.ιTensorObj Q (row adj I).X₃ p q n hpq ≫
        (rightMap adj Q I J a).f n =
      adj.homEquiv _ _
        (Functor.OplaxMonoidal.δ F (Q.X p) ((row adj I).X₃.X q) ≫
          (F.obj (Q.X p) ◁ adj.counit.app (F.obj (I.X q))) ≫
          Functor.LaxMonoidal.μ F (Q.X p) (I.X q) ≫
          F.map (HomologicalComplex.ιTensorObj Q I p q n hpq ≫ a.f n)) := by
  let ι := HomologicalComplex.ιTensorObj Q (row adj I).X₃ p q n hpq
  let t := (transpose adj Q I J a).f n
  have hμ : (comparison (F := F) Q I).inv = (F.mapCochainComplexμIso Q I).hom := by
    apply (Iso.inv_eq_inv _ (F.mapCochainComplexμIso Q I).symm).2
    rfl
  have ht : F.map ι ≫ t =
      Functor.OplaxMonoidal.δ F (Q.X p) ((row adj I).X₃.X q) ≫
        (F.obj (Q.X p) ◁ adj.counit.app (F.obj (I.X q))) ≫
        Functor.LaxMonoidal.μ F (Q.X p) (I.X q) ≫
        F.map (HomologicalComplex.ιTensorObj Q I p q n hpq ≫ a.f n) := by
    dsimp only [t, ι, transpose, row, restriction, ShortComplex.kernelSequence]
    rw [hμ]
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    dsimp only [comparison, asIso_hom]
    simp only [Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
      HomologicalComplex.mapBifunctorComparison_f]
    erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
    erw [CochainComplex.ιTensorObj_whiskerLeft_f_assoc]
    erw [F.ιTensorObj_mapCochainComplexμIso_hom_f_assoc]
    simp only [Adjunction.mapHomologicalComplex_counit_app_f,
      HomologicalComplex.mapBifunctorComparisonApp, Functor.OplaxMonoidal.δNatTrans,
      F.map_comp]
    rfl
  calc
    _ = ι ≫ adj.homEquiv _ _ t := rfl
    _ = adj.homEquiv _ _ (F.map ι ≫ t) :=
      (adj.homEquiv_naturality_left ι t).symm
    _ = _ := congrArg (adj.homEquiv _ _) ht

private theorem kernel_factor (adj : F ⊣ G) (Q I J : CochainComplex C ℤ)
    (a : Q ⊗ I ⟶ J) :
    ∃! u : Q ⊗ (row adj I).X₁ ⟶ (row adj J).X₁,
      u ≫ (row adj J).f = (Q ◁ (row adj I).f) ≫ a := by
  have hw : ((Q ◁ (row adj I).f) ≫ a) ≫ restriction adj J = 0 := by
    change ((Q ◁ (row adj I).f) ≫ a) ≫ (row adj J).g = 0
    rw [Category.assoc, ← rightMap_square adj Q I J a, ← Category.assoc,
      ← whiskerLeft_comp, (row adj I).zero, MonoidalPreadditive.whiskerLeft_zero,
      Limits.zero_comp]
  refine ⟨kernel.lift _ _ hw, kernel.lift_ι _ _ hw, ?_⟩
  intro u hu
  apply (cancel_mono (row adj J).f).1
  erw [hu, kernel.lift_ι]

omit [IsGrothendieckAbelian.{w + 1} D] [MonoidalCategory D] [MonoidalClosed D]
  [MonoidalPreadditive D] [BraidedCategory D] [F.IsLeftAdjoint] [F.Monoidal] in
private theorem kernel_naturality (adj : F ⊣ G) (Q I J I' J' : CochainComplex C ℤ)
    (a : Q ⊗ I ⟶ J) (a' : Q ⊗ I' ⟶ J') (f : I ⟶ I') (g : J ⟶ J')
    (h : a ≫ g = (Q ◁ f) ≫ a')
    (u : Q ⊗ (row adj I).X₁ ⟶ (row adj J).X₁)
    (u' : Q ⊗ (row adj I').X₁ ⟶ (row adj J').X₁)
    (hu : u ≫ (row adj J).f = (Q ◁ (row adj I).f) ≫ a)
    (hu' : u' ≫ (row adj J').f = (Q ◁ (row adj I').f) ≫ a') :
    u ≫ kernelMap adj g = (Q ◁ kernelMap adj f) ≫ u' := by
  apply (cancel_mono (row adj J').f).1
  dsimp only [row, ShortComplex.kernelSequence] at hu hu'
  dsimp only [kernelMap, row, ShortComplex.kernelSequence]
  simp only [Category.assoc, kernel.lift_ι]
  rw [← Category.assoc, hu, Category.assoc, h, ← Category.assoc,
    ← whiskerLeft_comp]
  erw [hu', ← Category.assoc, ← whiskerLeft_comp]
  congr 1
  simp only [kernel.lift_ι]

omit [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] in
private theorem functor_shortExact {E : Type*} [Category* E]
    (S : ShortComplex (E ⥤ C))
    (hS : ∀ i, (S.map ((CategoryTheory.evaluation E C).obj i)).ShortExact) :
    S.ShortExact := by
  have hf (i : E) : Mono (S.f.app i) := (hS i).mono_f
  have hg (i : E) : Epi (S.g.app i) := (hS i).epi_g
  have : Mono S.f := NatTrans.mono_of_mono_app S.f
  have : Epi S.g := NatTrans.epi_of_epi_app S.g
  refine ⟨?_⟩
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  ext i
  exact (IsZero.of_iso
    ((ShortComplex.exact_iff_isZero_homology _).1 (hS i).exact)
    (S.mapHomologyIso ((CategoryTheory.evaluation E C).obj i)).symm).eq_of_src _ _

private theorem total_tensor_shortExact (S : ShortComplex (CochainComplex C ℤ))
    (Q : CochainComplex C ℤ)
    (hS : ∀ q, (S.map (HomologicalComplex.eval C (.up ℤ) q)).ShortExact)
    (hQ : ∀ p : ℤ, exactFunctor _ _ (tensorRight (Q.X p))) (n : ℤ) :
    ((S.map (tensorLeft Q)).map (HomologicalComplex.eval C (.up ℤ) n)).ShortExact := by
  let E := {ij : ℤ × ℤ // ij.1 + ij.2 = n}
  let f : Discrete.functor (fun ij : E ↦ Q.X ij.1.1 ⊗ S.X₁.X ij.1.2) ⟶
      Discrete.functor (fun ij : E ↦ Q.X ij.1.1 ⊗ S.X₂.X ij.1.2) :=
    Discrete.natTrans (fun ij ↦ Q.X ij.as.1.1 ◁ S.f.f ij.as.1.2)
  let g : Discrete.functor (fun ij : E ↦ Q.X ij.1.1 ⊗ S.X₂.X ij.1.2) ⟶
      Discrete.functor (fun ij : E ↦ Q.X ij.1.1 ⊗ S.X₃.X ij.1.2) :=
    Discrete.natTrans (fun ij ↦ Q.X ij.as.1.1 ◁ S.g.f ij.as.1.2)
  have w : f ≫ g = 0 := by
    ext ij
    change (Q.X ij.as.1.1 ◁ S.f.f ij.as.1.2) ≫
      (Q.X ij.as.1.1 ◁ S.g.f ij.as.1.2) = 0
    rw [← whiskerLeft_comp]
    have hw := congrArg (fun t ↦ t.f ij.as.1.2) S.zero
    change S.f.f ij.as.1.2 ≫ S.g.f ij.as.1.2 = 0 at hw
    rw [hw, MonoidalPreadditive.whiskerLeft_zero]
  let T := ShortComplex.mk f g w
  have hT : T.ShortExact := by
    apply functor_shortExact
    intro ij
    have : PreservesFiniteLimits (tensorRight (Q.X ij.as.1.1)) := (hQ _).1
    have : PreservesFiniteColimits (tensorRight (Q.X ij.as.1.1)) := (hQ _).2
    have : PreservesFiniteLimits (tensorLeft (Q.X ij.as.1.1)) :=
      preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (Q.X ij.as.1.1)).symm
    exact (hS ij.as.1.2).map_of_exact (tensorLeft (Q.X ij.as.1.1))
  have ht := hT.map_of_exact (colim (J := Discrete E) (C := C))
  let V := (S.map (tensorLeft Q)).map (HomologicalComplex.eval C (.up ℤ) n)
  apply ShortComplex.shortExact_of_iso (S₁ := T.map colim) (S₂ := V) _ ht
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · dsimp only [V, ShortComplex.map_f, Iso.refl_hom, Category.comp_id, Category.id_comp]
    apply Sigma.hom_ext
    intro ij
    simp only [Category.comp_id, Category.id_comp]
    change HomologicalComplex.ιTensorObj Q S.X₁ ij.1.1 ij.1.2 n ij.2 ≫
      (Q ◁ S.f).f n = colimit.ι _ (Discrete.mk ij) ≫ colimMap f
    rw [ι_colimMap, CochainComplex.ιTensorObj_whiskerLeft_f]
    rfl
  · dsimp only [V, ShortComplex.map_g, Iso.refl_hom, Category.comp_id, Category.id_comp]
    apply Sigma.hom_ext
    intro ij
    simp only [Category.comp_id, Category.id_comp]
    change HomologicalComplex.ιTensorObj Q S.X₂ ij.1.1 ij.1.2 n ij.2 ≫
      (Q ◁ S.g).f n = colimit.ι _ (Discrete.mk ij) ≫ colimMap g
    rw [ι_colimMap, CochainComplex.ιTensorObj_whiskerLeft_f]
    rfl

omit [IsGrothendieckAbelian.{w + 1} D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] [MonoidalPreadditive C] [MonoidalPreadditive D]
  [BraidedCategory C] [BraidedCategory D] [F.IsLeftAdjoint] [F.Monoidal] in
private theorem row_shortExact (adj : F ⊣ G) (I : CochainComplex C ℤ)
    (hI : ∀ n : ℤ, Epi ((restriction adj I).f n)) (n : ℤ) :
    ((row adj I).map (HomologicalComplex.eval C (.up ℤ) n)).ShortExact := by
  have : Epi (restriction adj I) := HomologicalComplex.epi_of_epi_f _ hI
  have : Epi (row adj I).g := inferInstanceAs (Epi (restriction adj I))
  have hs : (row adj I).ShortExact := ⟨ShortComplex.kernelSequence_exact _⟩
  exact hs.map_of_exact (HomologicalComplex.eval C (.up ℤ) n)

/-- The complete strict diagram assertion, including summands, uniqueness, conditional
short exactness and naturality, with shared category structures throughout.
Source: Stacks 03DA, 03DB, 03ER, 07A4 and 093X; the agent-written cochain refinement
(blueprint: lem-pur-flat-support-chain-diagram). -/
def Diagram (adj : F ⊣ G) (Q I J : CochainComplex C ℤ) (a : Q ⊗ I ⟶ J) : Prop :=
    (Q ◁ (row adj I).g) ≫
        rightMap adj Q I J a =
      a ≫ (row adj J).g ∧
    (∀ (p q n : ℤ) (hpq : p + q = n),
      HomologicalComplex.ιTensorObj Q
          (row adj I).X₃ p q n hpq ≫
          (rightMap adj Q I J a).f n =
        adj.homEquiv _ _
          (Functor.OplaxMonoidal.δ F
              (Q.X p)
              ((row adj I).X₃.X q) ≫
            (F.obj (Q.X p) ◁
              adj.counit.app
                (F.obj (I.X q))) ≫
            Functor.LaxMonoidal.μ F (Q.X p) (I.X q) ≫
            F.map
              (HomologicalComplex.ιTensorObj Q I p q n hpq ≫ a.f n))) ∧
    (∃! u : Q ⊗ (row adj I).X₁ ⟶
        (row adj J).X₁,
      u ≫ (row adj J).f =
        (Q ◁ (row adj I).f) ≫ a) ∧
    ((∀ n : ℤ, Epi ((restriction adj I).f n)) →
      (∀ n : ℤ, Epi ((restriction adj J).f n)) →
      (∀ n : ℤ,
        (((row adj I).map (tensorLeft Q)).map
          (HomologicalComplex.eval _ (.up ℤ) n)).ShortExact ∧
        ((row adj J).map
          (HomologicalComplex.eval _ (.up ℤ) n)).ShortExact)) ∧
    (∀ (I' J' : CochainComplex C ℤ)
      (a' : Q ⊗ I' ⟶ J') (f : I ⟶ I') (g : J ⟶ J'), a ≫ g = (Q ◁ f) ≫ a' →
      (rightMap adj Q I J a ≫
          ((F.mapHomologicalComplex (.up ℤ) ⋙
            G.mapHomologicalComplex (.up ℤ)).map g) =
        (Q ◁ ((F.mapHomologicalComplex (.up ℤ) ⋙
          G.mapHomologicalComplex (.up ℤ)).map f)) ≫
            rightMap adj Q I' J' a') ∧
      (∀ (u : Q ⊗ (row adj I).X₁ ⟶
          (row adj J).X₁)
        (u' : Q ⊗ (row adj I').X₁ ⟶
          (row adj J').X₁),
        u ≫ (row adj J).f =
          (Q ◁ (row adj I).f) ≫ a →
        u' ≫ (row adj J').f =
          (Q ◁ (row adj I').f) ≫ a' →
        u ≫ kernelMap adj g = (Q ◁ kernelMap adj f) ≫ u'))

private theorem diagram_of_flat (adj : F ⊣ G) (Q I J : CochainComplex C ℤ)
    (hQ : ∀ p : ℤ, exactFunctor _ _ (tensorRight (Q.X p))) (a : Q ⊗ I ⟶ J) :
    Diagram adj Q I J a := by
  refine ⟨rightMap_square adj Q I J a, rightMap_summand adj Q I J a,
    kernel_factor adj Q I J a, ?_, ?_⟩
  · intro hI hJ n
    exact ⟨total_tensor_shortExact _ Q (row_shortExact adj I hI) hQ n,
      row_shortExact adj J hJ n⟩
  · intro I' J' a' f g h
    exact ⟨rightMap_naturality adj Q I J I' J' a a' f g h,
      kernel_naturality adj Q I J I' J' a a' f g h⟩

end AlgebraicGeometry.Etale.OpenSupport

namespace AlgebraicGeometry.Etale

/-- Flat-term total tensor gives the strict natural morphism of open-kernel rows,
 with the specified quotient map, its ordinary summand adjuncts, and a unique first map.
Source: Stacks 093X (support input), 03DA, 03DB, 03ER, and 07A4; agent-written Locality
 cochain refinement (blueprint: lem-pur-flat-support-chain-diagram).

Proof:
1. Work with the existing termwise adjunction and the kernel sequence of its unit.
   The argument applies to any additive strong monoidal left adjoint between braided
   monoidal closed Grothendieck abelian categories.
2. Naturality of the canonical total tensor comparison and the adjunction triangle
   identity show that the transpose of the proposed right square is F.map a.
   Unit naturality gives the right square itself.
3. Evaluate the transpose on a total-degree summand, using the ordinary comparison's
   summand formula and its inverse tensorator formula. Naturality of homEquiv gives
   the displayed ordinary adjunct, without commuting the right adjoint with sums.
4. The right square makes a after 1 tensor s_I vanish under r_J. The kernel universal
   property in the category of complexes gives the unique chain map u.
5. When the units are degreewise epic, their kernel rows are degreewise short exact.
   Flatness and braiding preserve these rows under Q.X p tensor -. Form the diagram
   indexed by p+q=n and apply the exact coproduct functor in the Grothendieck abelian
   category. Its arrows agree with the total tensor arrows on every summand.
6. Comparison and counit naturality give right-map naturality. Composing the proposed
   kernel naturality equation with the final kernel inclusion reduces it to the
   hypothesis on a,f,g,a'; cancel this monomorphism. -/
theorem flatSupportChainDiagram
    (A : Type (u + 1)) [CommRing A] [Finite A] {U P : Scheme.{u}}
    (j : U ⟶ P) [IsOpenImmersion j]
    (Q I J : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hQ : ∀ p : ℤ, exactFunctor _ _ (tensorRight (Q.X p))) (a : Q ⊗ I ⟶ J) :
    OpenSupport.Diagram (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j) Q I J a := by
  exact OpenSupport.diagram_of_flat
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j) Q I J _hQ a

attribute [instance] HomologicalComplex.monoidalCategoryStruct
end AlgebraicGeometry.Etale
