/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.CategoryTheory.RingedExtendedCech
public import Sheaf.Algebra.Homology.HomComplex
public import Sheaf.CategoryTheory.RingedCompletionUnit
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
public import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor

/-!
# The finite Koszul system on a ringed site

Source: Stacks Project, More on Algebra, Tag 0913; Cohomology on Sites, Tag 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false




universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem koszulBifunctor_comp
    {A B D : Type*} [Category A] [Category B] [Category D]
    (T : A ⥤ B ⥤ D) {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
    (f : a₁ ⟶ a₂) (g : b₁ ⟶ b₂) (p : a₂ ⟶ a₃) (q : b₂ ⟶ b₃) :
    (T.map f).app b₁ ≫ (T.obj a₂).map g ≫
        (T.map p).app b₂ ≫ (T.obj a₃).map q =
      (T.map (f ≫ p)).app b₁ ≫ (T.obj a₃).map (g ≫ q) := by
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [(T.map p).naturality_assoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem koszulLimit_lift_map
    {I A : Type*} [Category I] [Category A] [HasLimitsOfShape I A]
    {F G : I ⥤ A} (s : Cone F) (t : Cone G) (a : F ⟶ G) (f : s.pt ⟶ t.pt)
    (h : ∀ j, s.π.app j ≫ a.app j = f ≫ t.π.app j) :
    limit.lift F s ≫ lim.map a = f ≫ limit.lift G t := by
  apply limit.hom_ext
  intro j
  change (limit.lift F s ≫ limMap a) ≫ limit.π G j = _
  rw [Category.assoc, limMap_π, ← Category.assoc, limit.lift_π,
    Category.assoc, limit.lift_π]
  exact h j

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

/-- Reuse the canonical preservation-of-sheaves instance during elaboration.
Source: Mathlib, `GrothendieckTopology.HasSheafCompose`.
(blueprint: def-weil-pbc-ringed-koszul-system). -/
local instance ringedKoszulHasSheafCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance

/-- Reuse zero preservation of the inverse-limit functor.
Source: Mathlib, additivity of limits.
(blueprint: def-weil-pbc-ringed-koszul-system). -/
local instance ringedKoszulLimitPreservesZeroMorphisms :
    Functor.PreservesZeroMorphisms (lim : (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤
        SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) := inferInstance

/-- Multiplication by a global section on the rank-one module sheaf.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulScalar (s : (O.obj ⋙ forget CommRingCat).sections) :
    End (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  SheafOfModules.unitHomEquiv _ |>.symm ⟨s.val, s.property⟩

/-- The positive Koszul factor [O --s^(m+1)--> O] in degrees zero and one.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulFactor (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    ringedSiteComplex O :=
  HomologicalComplex.double ((ringedKoszulScalar O s) ^ (m + 1))
    (by decide : (ComplexShape.up ℤ).Rel 0 1)

/-- Components of the forward map (1,s), zero outside degrees zero and one.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulFactorStepF (s : (O.obj ⋙ forget CommRingCat).sections)
    (m : ℕ) (n : ℤ) :
    (ringedKoszulFactor O s m).X n ⟶ (ringedKoszulFactor O s (m + 1)).X n :=
  if h : n = 0 then
    eqToHom (congrArg (ringedKoszulFactor O s m).X h) ≫
      (HomologicalComplex.doubleXIso₀ _ _).hom ≫
      (HomologicalComplex.doubleXIso₀ _ _).inv ≫
      eqToHom (congrArg (ringedKoszulFactor O s (m + 1)).X h.symm)
  else if h : n = 1 then
    eqToHom (congrArg (ringedKoszulFactor O s m).X h) ≫
      (HomologicalComplex.doubleXIso₁ _ _ (by decide)).hom ≫
      ringedKoszulScalar O s ≫
      (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫
      eqToHom (congrArg (ringedKoszulFactor O s (m + 1)).X h.symm)
  else 0

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The components (1,s) commute with the differential.
Proof: the sole nonzero square is s^(m+1) s = s^(m+2); elsewhere both sides vanish.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
theorem ringedKoszulFactorStepF_comm
    (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) (n k : ℤ)
    (h : (ComplexShape.up ℤ).Rel n k) :
    ringedKoszulFactorStepF O s m n ≫ (ringedKoszulFactor O s (m + 1)).d n k =
      (ringedKoszulFactor O s m).d n k ≫ ringedKoszulFactorStepF O s m k := by
  have hnk : n + 1 = k := h
  clear h
  by_cases hn : n = 0
  · subst n
    have hk : k = 1 := hnk.symm
    subst k
    simp [ringedKoszulFactorStepF, ringedKoszulFactor,
      HomologicalComplex.double_d, Category.assoc]
    have hp : ringedKoszulScalar O s ^ (m + 1 + 1) =
        (ringedKoszulScalar O s ^ (m + 1)) ≫ ringedKoszulScalar O s := by
      simpa only [End.mul_def] using pow_succ' (ringedKoszulScalar O s) (m + 1)
    simpa only [Category.assoc] using hp =≫
      (HomologicalComplex.doubleXIso₁ (ringedKoszulScalar O s ^ (m + 1 + 1))
        (by decide : (ComplexShape.up ℤ).Rel 0 1) (by decide)).inv
  · simp [ringedKoszulFactor, HomologicalComplex.double_d_eq_zero₀, hn]


/-- The forward Koszul chain map with components (1,s).
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulFactorStep (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    ringedKoszulFactor O s m ⟶ ringedKoszulFactor O s (m + 1) where
  f := ringedKoszulFactorStepF O s m
  comm' := ringedKoszulFactorStepF_comm O s m

/-- The total tensor bifunctor of module-sheaf complexes, with its Koszul signs.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulTensor : ringedSiteComplex O ⥤ ringedSiteComplex O ⥤
    ringedSiteComplex O :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  (CategoryTheory.MonoidalCategory.curriedTensor _).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

attribute [local irreducible] ringedKoszulTensor


/-- The strict sequential diagram of the positive one-section Koszul factors.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulFactors (s : (O.obj ⋙ forget CommRingCat).sections) :
    ℕ ⥤ ringedSiteComplex O :=
  Functor.ofSequence (ringedKoszulFactorStep O s)

/-- The ordered total tensor of the positive Koszul systems.
The empty tensor is the constant diagram O[0]. The index m denotes exponent m+1.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulDiagram : (r : ℕ) →
    (Fin r → (O.obj ⋙ forget CommRingCat).sections) → ℕ ⥤ ringedSiteComplex O :=
  fun r ↦ Nat.rec
    (fun _ ↦ (Functor.const ℕ).obj (ringedSiteRingComplex O))
    (fun _ ih b ↦
      (ringedKoszulFactors O (b 0)).prod' (ih (fun i ↦ b i.succ)) ⋙
        Functor.uncurry.obj (ringedKoszulTensor O)) r

/-- The strict dual inverse tower Hom(P_m,O[0]), including its dual chain maps.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulDualTower (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    ℕᵒᵖ ⥤ ringedSiteComplex O :=
  (ringedKoszulDiagram O r b).op ⋙
    (homComplexFunctor (R := O)).flip.obj (ringedSiteRingComplex O)

/-- Components of the degree-zero projection of a positive Koszul factor.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulFactorProjectionF (s : (O.obj ⋙ forget CommRingCat).sections)
    (m : ℕ) (n : ℤ) :
    (ringedKoszulFactor O s m).X n ⟶ (ringedSiteRingComplex O).X n :=
  if h : n = 0 then
    eqToHom (congrArg (ringedKoszulFactor O s m).X h) ≫
      (HomologicalComplex.doubleXIso₀ _ _).hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv ≫
      eqToHom (congrArg (ringedSiteRingComplex O).X h.symm)
  else 0

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero projection commutes with the differential.
Proof: the target differential is zero and the source differential lands in degree one,
where the projection vanishes. All other squares have a zero component.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
theorem ringedKoszulFactorProjectionF_comm
    (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) (n k : ℤ)
    (h : (ComplexShape.up ℤ).Rel n k) :
    ringedKoszulFactorProjectionF O s m n ≫ (ringedSiteRingComplex O).d n k =
      (ringedKoszulFactor O s m).d n k ≫ ringedKoszulFactorProjectionF O s m k := by
  by_cases hk : k = 0
  · have hn : n ≠ 0 := by
      have hnk : n + 1 = k := h
      omega
    rw [hk]
    simp [ringedKoszulFactor, HomologicalComplex.double_d_eq_zero₀, hn]
  · simp [ringedKoszulFactorProjectionF, hk]


/-- The augmented positive Koszul factor.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulFactorProjection (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    ringedKoszulFactor O s m ⟶ ringedSiteRingComplex O where
  f := ringedKoszulFactorProjectionF O s m
  comm' := ringedKoszulFactorProjectionF_comm O s m

set_option synthInstance.maxSize 2048 in
attribute [local semireducible] ringedKoszulTensor in
/-- The ordinary unit identification O[0] tensor O[0] = O[0].
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulUnitTensorIso :
    ((ringedKoszulTensor O).obj (ringedSiteRingComplex O)).obj (ringedSiteRingComplex O) ≅
      ringedSiteRingComplex O :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  HomologicalComplex.leftUnitor _

/-- Tensor the degree-zero projections, using the ordinary unit identification.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulProjection : (r : ℕ) →
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) →
      (m : ℕ) → (ringedKoszulDiagram O r b).obj m ⟶ ringedSiteRingComplex O :=
  fun r ↦ Nat.rec
    (fun _ _ ↦ 𝟙 _)
    (fun _ ih b m ↦
      ((ringedKoszulTensor O).map (ringedKoszulFactorProjection O (b 0) m)).app _ ≫
        ((ringedKoszulTensor O).obj _).map (ih (fun i ↦ b i.succ) m) ≫
        (ringedKoszulUnitTensorIso O).hom) r

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The Koszul projections are compatible with the forward transitions.
Proof: in one factor, the forward map is identity in degree zero. Tensor this identity
and induct on the number of factors; composition gives the identity for every transition.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
theorem ringedKoszulProjection_naturality (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (m n : ℕ) (f : m ⟶ n) :
    (ringedKoszulDiagram O r b).map f ≫ ringedKoszulProjection O r b n =
      ringedKoszulProjection O r b m := by
  have hfactor (s : (O.obj ⋙ forget CommRingCat).sections) :
      (ringedKoszulFactors O s).map f ≫ ringedKoszulFactorProjection O s n =
        ringedKoszulFactorProjection O s m := by
    let α : ringedKoszulFactors O s ⟶
        (Functor.const ℕ).obj (ringedSiteRingComplex O) :=
      NatTrans.ofSequence (ringedKoszulFactorProjection O s) (fun j ↦ by
        simp only [ringedKoszulFactors, Functor.ofSequence_map_homOfLE_succ,
          Functor.const_obj_map]
        apply HomologicalComplex.Hom.ext
        funext i
        change (ringedKoszulFactorStepF O s j i ≫
            ringedKoszulFactorProjectionF O s (j + 1) i) =
          ringedKoszulFactorProjectionF O s j i ≫ 𝟙 _
        by_cases hi : i = 0
        · subst i
          simp [ringedKoszulFactorStepF, ringedKoszulFactorProjectionF, Category.assoc]
        · simp [ringedKoszulFactorProjectionF, hi])
    have hh := α.naturality f
    change (ringedKoszulFactors O s).map f ≫ ringedKoszulFactorProjection O s n =
      ringedKoszulFactorProjection O s m ≫ 𝟙 _ at hh
    exact hh.trans (Category.comp_id _)
  induction r with
  | zero => simp [ringedKoszulDiagram, ringedKoszulProjection]
  | succ r ih =>
    change (((ringedKoszulTensor O).map ((ringedKoszulFactors O (b 0)).map f)).app _ ≫
        ((ringedKoszulTensor O).obj _).map
          ((ringedKoszulDiagram O r (fun i ↦ b i.succ)).map f)) ≫
        (((ringedKoszulTensor O).map (ringedKoszulFactorProjection O (b 0) n)).app _ ≫
        ((ringedKoszulTensor O).obj _).map
          (ringedKoszulProjection O r (fun i ↦ b i.succ) n) ≫
        (ringedKoszulUnitTensorIso O).hom) =
      ((ringedKoszulTensor O).map (ringedKoszulFactorProjection O (b 0) m)).app _ ≫
        ((ringedKoszulTensor O).obj _).map
          (ringedKoszulProjection O r (fun i ↦ b i.succ) m) ≫
        (ringedKoszulUnitTensorIso O).hom
    have hh := koszulBifunctor_comp (ringedKoszulTensor O)
      ((ringedKoszulFactors O (b 0)).map f)
      ((ringedKoszulDiagram O r (fun i ↦ b i.succ)).map f)
      (ringedKoszulFactorProjection O (b 0) n)
      (ringedKoszulProjection O r (fun i ↦ b i.succ) n)
    simpa only [Category.assoc, hfactor, ih] using
      hh =≫ (ringedKoszulUnitTensorIso O).hom


/-- The compatible Koszul projections as an actual cocone.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulAugmentationCocone (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    Cocone (ringedKoszulDiagram O r b) where
  pt := ringedSiteRingComplex O
  ι :=
    { app := ringedKoszulProjection O r b
      naturality := ringedKoszulProjection_naturality O r b }

/-- The strict tensor tower N tensor Hom(P_m,O), functorial in N.
Its morphisms are total tensors with the dual transitions.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulTensorTower (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    ringedSiteComplex O ⥤ (ℕᵒᵖ ⥤ ringedSiteComplex O) :=
  ringedKoszulTensor O ⋙
    (Functor.whiskeringLeft ℕᵒᵖ (ringedSiteComplex O) (ringedSiteComplex O)).obj
      (ringedKoszulDualTower O r b)


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The strict-tower differentials square to zero.
Proof: evaluate at every tower index and use the square-zero identity of its complex.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
theorem ringedKoszulTensorTower_d_comp (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteComplex O)
    (n : ℤ) :
    Functor.whiskerLeft ((ringedKoszulTensorTower O r b).obj N)
        (HomologicalComplex.dNatTrans _ (ComplexShape.up ℤ) n (n + 1)) ≫
      Functor.whiskerLeft ((ringedKoszulTensorTower O r b).obj N)
        (HomologicalComplex.dNatTrans _ (ComplexShape.up ℤ) (n + 1) (n + 1 + 1)) = 0 := by
  apply NatTrans.ext
  funext m
  exact (((ringedKoszulTensorTower O r b).obj N).obj m).d_comp_d n (n + 1) (n + 1 + 1)

/-- The strict tensor tower, transposed into a complex in the abelian category of towers.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulTensorTowerComplex (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteComplex O) :
    CochainComplex (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ :=
  CochainComplex.of
    (fun n ↦ (ringedKoszulTensorTower O r b).obj N ⋙
      HomologicalComplex.eval _ (ComplexShape.up ℤ) n)
    (fun n ↦ Functor.whiskerLeft ((ringedKoszulTensorTower O r b).obj N)
      (HomologicalComplex.dNatTrans _ (ComplexShape.up ℤ) n (n + 1)))
    (ringedKoszulTensorTower_d_comp O r b N)

/-- Degreewise components of the strict tensor-tower map induced by a chain map.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulTensorTowerComplexMapF (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {N M : ringedSiteComplex O} (f : N ⟶ M) (n : ℤ) :
    (ringedKoszulTensorTowerComplex O r b N).X n ⟶
      (ringedKoszulTensorTowerComplex O r b M).X n :=
  Functor.whiskerRight ((ringedKoszulTensorTower O r b).map f)
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Tensor-tower maps commute with the differentials.
Proof: evaluate at each tower index and use the chain-map identity of the tensor map.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
theorem ringedKoszulTensorTowerComplexMapF_comm (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {N M : ringedSiteComplex O} (f : N ⟶ M) (n k : ℤ)
    (h : (ComplexShape.up ℤ).Rel n k) :
    ringedKoszulTensorTowerComplexMapF O r b f n ≫
        (ringedKoszulTensorTowerComplex O r b M).d n k =
      (ringedKoszulTensorTowerComplex O r b N).d n k ≫
        ringedKoszulTensorTowerComplexMapF O r b f k := by
  have hk : k = n + 1 := h.symm
  subst k
  apply NatTrans.ext
  funext m
  simp only [ringedKoszulTensorTowerComplex, CochainComplex.of_d]
  exact (((ringedKoszulTensorTower O r b).map f).app m).comm n (n + 1)

/-- The actual strict map of tower complexes induced by a chain map.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulTensorTowerComplexMap (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {N M : ringedSiteComplex O} (f : N ⟶ M) :
    ringedKoszulTensorTowerComplex O r b N ⟶ ringedKoszulTensorTowerComplex O r b M where
  f := ringedKoszulTensorTowerComplexMapF O r b f
  comm' := ringedKoszulTensorTowerComplexMapF_comm O r b f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The strict tensor-tower construction preserves identity maps.
Proof: evaluate in each tower index and degree and use the identity law of the tensor functor.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
theorem ringedKoszulTensorTowerComplexMap_id (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteComplex O) :
    ringedKoszulTensorTowerComplexMap O r b (𝟙 N) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply NatTrans.ext
  funext m
  change ((((ringedKoszulTensorTower O r b).map (𝟙 N)).app m).f n) = 𝟙 _
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The strict tensor-tower construction preserves composition.
Proof: evaluate in each tower index and degree and use functoriality of total tensor.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
theorem ringedKoszulTensorTowerComplexMap_comp (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {N M L : ringedSiteComplex O} (f : N ⟶ M) (g : M ⟶ L) :
    ringedKoszulTensorTowerComplexMap O r b (f ≫ g) =
      ringedKoszulTensorTowerComplexMap O r b f ≫
        ringedKoszulTensorTowerComplexMap O r b g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply NatTrans.ext
  funext m
  change ((((ringedKoszulTensorTower O r b).map (f ≫ g)).app m).f n) =
    ((((ringedKoszulTensorTower O r b).map f).app m).f n) ≫
      ((((ringedKoszulTensorTower O r b).map g).app m).f n)
  simp

/-- The functor from module complexes to strict tensor-tower complexes.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulTensorTowerFunctor (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    ringedSiteComplex O ⥤ CochainComplex (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ where
  obj := ringedKoszulTensorTowerComplex O r b
  map := ringedKoszulTensorTowerComplexMap O r b
  map_id := ringedKoszulTensorTowerComplexMap_id O r b
  map_comp := ringedKoszulTensorTowerComplexMap_comp O r b

/-- The degree-zero unit O[0] to the dual Koszul complex,
obtained by dualizing the projection P_m to O[0] and evaluation at one.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulDualUnit (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    ringedSiteRingComplex O ⟶ (ringedKoszulDualTower O r b).obj (op m) :=
  (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv ≫
    ((homComplexFunctor (R := O)).map (ringedKoszulProjection O r b m).op).app _

set_option synthInstance.maxSize 2048 in
attribute [local semireducible] ringedKoszulTensor in
/-- The canonical total-tensor right unit isomorphism.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulRightUnitIso (N : ringedSiteComplex O) :
    ((ringedKoszulTensor O).obj N).obj (ringedSiteRingComplex O) ≅ N :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  HomologicalComplex.rightUnitor _

/-- The actual map N to N tensor Q_m induced by its degree-zero unit.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulTensorUnitComponent (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (N : ringedSiteComplex O) (m : ℕᵒᵖ) :
    N ⟶ ((ringedKoszulTensorTower O r b).obj N).obj m :=
  (ringedKoszulRightUnitIso O N).inv ≫
    ((ringedKoszulTensor O).obj N).map (ringedKoszulDualUnit O r b m.unop)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero units form a cone over the strict tensor tower.
Proof: dualize compatibility of the Koszul projections with transitions, then tensor by N.
Taking the component in degree n gives the asserted equality.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
theorem ringedKoszulTensorUnitComponent_naturality (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (N : ringedSiteComplex O) (n : ℤ) {m k : ℕᵒᵖ} (f : m ⟶ k) :
    ((Functor.const ℕᵒᵖ).obj (N.X n)).map f ≫
        (ringedKoszulTensorUnitComponent O r b N k).f n =
      (ringedKoszulTensorUnitComponent O r b N m).f n ≫
        ((ringedKoszulTensorTowerComplex O r b N).X n).map f := by
  have hp := ringedKoszulProjection_naturality O r b k.unop m.unop f.unop
  let D : (ringedSiteComplex O)ᵒᵖ ⥤ ringedSiteComplex O :=
    (homComplexFunctor (R := O)).flip.obj (ringedSiteRingComplex O)
  have hdual : D.map (ringedKoszulProjection O r b k.unop).op =
      D.map (ringedKoszulProjection O r b m.unop).op ≫
        D.map ((ringedKoszulDiagram O r b).map f.unop).op := by
    rw [← D.map_comp, ← op_comp, hp]
  have hd : ringedKoszulDualUnit O r b k.unop =
      ringedKoszulDualUnit O r b m.unop ≫ (ringedKoszulDualTower O r b).map f := by
    change (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv ≫
        D.map (ringedKoszulProjection O r b k.unop).op =
      ((ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv ≫
        D.map (ringedKoszulProjection O r b m.unop).op) ≫
          D.map ((ringedKoszulDiagram O r b).map f.unop).op
    rw [Category.assoc, hdual]
  have ht : ringedKoszulTensorUnitComponent O r b N k =
      ringedKoszulTensorUnitComponent O r b N m ≫
        ((ringedKoszulTensorTower O r b).obj N).map f := by
    change (ringedKoszulRightUnitIso O N).inv ≫
        ((ringedKoszulTensor O).obj N).map (ringedKoszulDualUnit O r b k.unop) =
      ((ringedKoszulRightUnitIso O N).inv ≫
        ((ringedKoszulTensor O).obj N).map (ringedKoszulDualUnit O r b m.unop)) ≫
        ((ringedKoszulTensor O).obj N).map ((ringedKoszulDualTower O r b).map f)
    rw [hd, Functor.map_comp, Category.assoc]
  change 𝟙 (N.X n) ≫ (ringedKoszulTensorUnitComponent O r b N k).f n =
    (ringedKoszulTensorUnitComponent O r b N m).f n ≫
      (((ringedKoszulTensorTower O r b).obj N).map f).f n
  rw [Category.id_comp]
  exact congrArg (fun g ↦ g.f n) ht


/-- The compatible degree-zero maps as a degreewise cone over the strict tensor tower.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulTensorUnitCone (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (N : ringedSiteComplex O) (n : ℤ) :
    Cone ((ringedKoszulTensorTowerComplex O r b N).X n) where
  pt := N.X n
  π :=
    { app := fun m ↦ (ringedKoszulTensorUnitComponent O r b N m).f n
      naturality := fun {_m _k} f ↦
        ringedKoszulTensorUnitComponent_naturality O r b N n f }

/-- The canonical degreewise map to the ordinary strict inverse limit.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulLimitUnitF (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (N : ringedSiteComplex O) (n : ℤ) :
    N.X n ⟶ ((lim : (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤ _).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (ringedKoszulTensorTowerComplex O r b N) |>.X n :=
  @id (N.X n ⟶ limit ((ringedKoszulTensorTowerComplex O r b N).X n))
    (limit.lift _ (ringedKoszulTensorUnitCone O r b N n))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The map to the ordinary inverse limit is a chain map.
Proof: compose with each limit projection and use the chain-map identity of the degree-zero
unit into each tensor complex. Joint monicity of limit projections gives the equality.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
theorem ringedKoszulLimitUnitF_comm (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (N : ringedSiteComplex O) (n k : ℤ) (h : (ComplexShape.up ℤ).Rel n k) :
    ringedKoszulLimitUnitF O r b N n ≫
        (((lim : (ℕᵒᵖ ⥤ SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤ _).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (ringedKoszulTensorTowerComplex O r b N)).d n k =
      N.d n k ≫ ringedKoszulLimitUnitF O r b N k := by
  change limit.lift _ (ringedKoszulTensorUnitCone O r b N n) ≫
      lim.map ((ringedKoszulTensorTowerComplex O r b N).d n k) =
    N.d n k ≫ limit.lift _ (ringedKoszulTensorUnitCone O r b N k)
  apply koszulLimit_lift_map
  intro m
  have hk : k = n + 1 := h.symm
  subst k
  simp only [ringedKoszulTensorUnitCone, ringedKoszulTensorTowerComplex,
    CochainComplex.of_d]
  exact (ringedKoszulTensorUnitComponent O r b N m).comm n (n + 1)


/-- The canonical ordinary strict-limit unit, before deriving inverse limit.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulLimitUnit (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteComplex O) :
    N ⟶ ((lim : (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤ _).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (ringedKoszulTensorTowerComplex O r b N) where
  f := ringedKoszulLimitUnitF O r b N
  comm' := ringedKoszulLimitUnitF_comm O r b N

/-- Restrict a global section to the slice site by its underlying compatible sections.
Source: Stacks Project, Tags 0913 and 0A0A
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulSliceSection (s : (O.obj ⋙ forget CommRingCat).sections) (U : C) :
    ((O.over U).obj ⋙ forget CommRingCat).sections :=
  ⟨fun V ↦ s.val (op V.unop.left), fun f ↦ s.property f.unop.left.op⟩


/-- Derived restriction between the two slice sites, along the actual overMap functor.
Source: Stacks Project, Tag 08JB
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulDerivedOverMap {U V : C} (f : V ⟶ U)
    [hU : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    [hV : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))] :
    ringedSiteDerived (O.over U) ⥤ ringedSiteDerived (O.over V) :=
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) := hU
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over V)) := hV
  (SheafOfModules.overMap.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) f).mapDerivedCategory

/-- The canonical composition isomorphism between successive and direct slice restrictions.
Source: Stacks Project, Tag 08JB
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def ringedKoszulDerivedOverComparison {U V : C} (f : V ⟶ U)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [hU : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    [hV : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))] :
    ringedDerivedRestriction O U ⋙ ringedKoszulDerivedOverMap O f ≅
      ringedDerivedRestriction O V :=
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) := hU
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over V)) := hV
  (Functor.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U)
    (SheafOfModules.overMap.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) f)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) f)

/-- A presentation of derived Koszul completion by a strict tensor tower and total right
derived inverse limit. The factorization fixes the strict tower including its transitions.
The right-derived universal property and computation on K-injective towers fix inverse
limit up to its unique normalized comparison isomorphism.
Source: Stacks Project, Tags 0913, 0A0A and 0941
(blueprint: def-weil-pbc-ringed-koszul-system). -/
structure RingedKoszulLimitPresentation (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))] where
  tensorTower : ringedSiteDerived O ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  tensorFactors : DerivedCategory.Q ⋙ tensorTower ≅
    ringedKoszulTensorTowerFunctor O r b ⋙ DerivedCategory.Q
  inverseLimit : DerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤ ringedSiteDerived O
  comparison :
    (lim : (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤ _).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ inverseLimit
  isRightDerived : inverseLimit.IsRightDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) (ComplexShape.up ℤ))
  comparison_isIso : ∀ I, CochainComplex.IsKInjective I → IsIso (comparison.app I)

variable {O}

namespace RingedKoszulLimitPresentation

variable {r : ℕ} {b : Fin r → (O.obj ⋙ forget CommRingCat).sections}
variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
variable (D : RingedKoszulLimitPresentation O r b)

/-- Compose the descended strict tensor-tower functor with total derived inverse limit.
Source: Stacks Project, Tags 0913, 0A0A and 0941
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def completion : ringedSiteDerived O ⥤ ringedSiteDerived O :=
  D.tensorTower ⋙ D.inverseLimit

/-- The canonical strict derived-limit unit on a representative complex.
Apply the derived-functor comparison to the actual map into the ordinary inverse limit,
then use the specified localization factorization of the strict tensor tower.
Source: Stacks Project, Tags 0913, 0A0A and 0941
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def unitOnComplex (N : ringedSiteComplex O) :
    DerivedCategory.Q.obj N ⟶ D.completion.obj (DerivedCategory.Q.obj N) :=
  DerivedCategory.Q.map (ringedKoszulLimitUnit O r b N) ≫
    D.comparison.app (ringedKoszulTensorTowerComplex O r b N) ≫
    D.inverseLimit.map (D.tensorFactors.app N).inv

/-- The canonical strict derived-limit unit on a derived object, using its localization
representative and transporting back along its specified representative isomorphism.
Source: Stacks Project, Tags 0913, 0A0A and 0941
(blueprint: def-weil-pbc-ringed-koszul-system). -/
def unit (E : ringedSiteDerived O) : E ⟶ D.completion.obj E :=
  (DerivedCategory.Q.objObjPreimageIso E).inv ≫
    D.unitOnComplex (DerivedCategory.Q.objPreimage E) ≫
    D.completion.map (DerivedCategory.Q.objObjPreimageIso E).hom

end RingedKoszulLimitPresentation

end CategoryTheory
