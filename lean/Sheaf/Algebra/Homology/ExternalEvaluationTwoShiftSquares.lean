/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
import all Sheaf.SecSmoothPurity.CochainInverseComparison

/-! # Both coefficient shift squares for external chain evaluations

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, Tag 0A90
(lemma-compose), and lemma-RHom-triangulated; the two-variable sign calculation
from steps 8 and 9 of lem-pur-external-rhom-cone-pairing
(blueprint: lem-pur-external-evaluation-two-shift-squares).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.checkUnivs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct

namespace CategoryTheory.ExternalEvaluation

variable {C : Type u} [Category.{v} C] (S : GrothendieckTopology C)
  (A : Type (max u v)) [CommRing A]


/-- The recorded constant-ring module category, in its commutative presentation.
Source: Stacks 03CY and 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
abbrev Modules := realizationModules S A

/-- Cochain complexes in the recorded module-sheaf category.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
abbrev Complex := CochainComplex (Modules S A) ℤ

/-- Coefficient complexes over the original ring.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
abbrev Coeff (R : Type w) [CommRing R] := CochainComplex (ModuleCat.{w} R) ℤ

/-- Coefficient complexes admit the direct-sum tensor totalization.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
instance coefficientHasTensor (R : Type w) [CommRing R] (U V : Coeff R) :
    CochainComplex.HasMapBifunctor U V (curriedTensor (ModuleCat.{w} R)) := by
  dsimp only [CochainComplex.HasMapBifunctor, HomologicalComplex.HasMapBifunctor]
  infer_instance

/-- Termwise constant realization, using the existing sheafification construction.
Source: Stacks 03CY (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
@[instance_reducible]
def constantComplex : Coeff A ⥤ Complex S A :=
  (commutativeSiteConstantModuleFunctor S A).mapHomologicalComplex (.up ℤ)

/-- Forget scalars on a coefficient complex; no component or differential is changed.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
@[instance_reducible]
def underlying (R : Type w) [CommRing R] : Coeff R ⥤ CochainComplex AddCommGrpCat ℤ :=
  (forget₂ (ModuleCat.{w} R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)

private instance constantComplexCommShift : (constantComplex S A).CommShift ℤ := by
  unfold constantComplex
  infer_instance

/-- Forgetting module scalars commutes with cochain shifts term by term.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
instance underlyingCommShift (R : Type w) [CommRing R] :
    (underlying R).CommShift ℤ := by
  unfold underlying
  infer_instance

/-- A constant local section is the image of the module-sheafification unit.
Source: Stacks 03CY (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def constantSection (Q : ModuleCat.{max u v} A) (W : Cᵒᵖ) (x : Q) :
    ((commutativeSiteConstantModuleFunctor S A).obj Q).val.obj W :=
  (toSheafify S ((siteConstantModulePresheafGeneral (C := C) A).obj Q).presheaf).app W x

/-- A local pure tensor in the existing sheaf tensor, via its sheafification comparison.
Source: Stacks 03EK (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def tensorSection (P Q : Modules S A) (W : Cᵒᵖ) (x : P.val.obj W) (y : Q.val.obj W) :
    (P ⊗ Q).val.obj W :=
  ((SheafOfModules.tensorObjIsoSheafification (R := realizationRing S A) P Q).inv.val.app W)
    ((((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
      (P.val ⊗ Q.val)).app W) (TensorProduct.tmul _ x y))

/-- The direct-sum tensor totalization exists for the recorded module-sheaf complexes.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
instance complexHasTensor (P Q : Complex S A) :
    CochainComplex.HasMapBifunctor P Q (curriedTensor (Modules S A)) := by
  dsimp only [CochainComplex.HasMapBifunctor, HomologicalComplex.HasMapBifunctor]
  infer_instance

/-- The recorded direct-sum total tensor, with the usual signed differential.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
@[instance_reducible]
def tensorComplex (P Q : Complex S A) : Complex S A :=
  CochainComplex.mapBifunctor P Q (curriedTensor (Modules S A))

/-- Include a local pure tensor in its direct-sum total-complex summand.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def tensorComplexSection (P Q : Complex S A) (r s n : ℤ) (h : r + s = n)
    (W : Cᵒᵖ) (x : (P.X r).val.obj W) (y : (Q.X s).val.obj W) :
    ((tensorComplex S A P Q).X n).val.obj W :=
  ((CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules S A)) r s n h).val.app W)
    (tensorSection S A (P.X r) (Q.X s) W x y)

/-- Include a coefficient pure tensor in the direct-sum total tensor.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def coefficientTensor (R : Type w) [CommRing R] (U V : Coeff R) (r s : ℤ)
    (w : U.X r) (z : V.X s) :
    (U ⊗ V).X (r + s) :=
  (HomologicalComplex.ιTensorObj U V r s (r + s) rfl).hom (TensorProduct.tmul R w z)

/-- Evaluate an ordinary chain map on a coefficient and a homogeneous local section.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def evaluate (U : Coeff A) (E N : Complex S A)
    (f : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N) (r q : ℤ) (W : Cᵒᵖ)
    (w : U.X r) (e : (E.X q).val.obj W) : (N.X (r + q)).val.obj W :=
  ((f.f (r + q)).val.app W)
    (tensorComplexSection S A ((constantComplex S A).obj U) E r q (r + q) rfl W
      (constantSection S A (U.X r) W w) e)

/-- The unsigned external evaluation, transported only along equality of total degrees.
Source: Stacks 0A90 (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def unsignedEvaluation (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J) (r s q t k : ℤ)
    (hk : (r + q) + (s + t) = k) (W : Cᵒᵖ) (w : U.X r) (z : V.X s)
    (e : (E.X q).val.obj W) (h : (H.X t).val.obj W) : (J.X k).val.obj W :=
  ((J.XIsoOfEq hk).hom.val.app W)
    (((i.f ((r + q) + (s + t))).val.app W)
      (tensorComplexSection S A N M (r + q) (s + t) ((r + q) + (s + t)) rfl W
        (evaluate S A U E N u r q W w e) (evaluate S A V H M v s t W z h)))

/-- Scalar linearity for a map to global Hom, expressed on all local components.
This equips the additive global Hom presentation with exactly its original A-linearity;
the scalar is sent to the constant ring sheaf by the prescribed sheafification unit.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def IsLinearHomMap (T : Coeff A) (B J : Complex S A)
    (p : (underlying A).obj T ⟶ CochainComplex.HomComplex B J) : Prop :=
  ∀ (n : ℤ) (a : A) (x : T.X n) (j k : ℤ) (hjk : j + n = k)
    (W : Cᵒᵖ) (y : (B.X j).val.obj W),
    (((((p.f n) (a • x)).v j k hjk).val.app W) y) =
      ((realizationRingUnit S A).app W a) •
        (((((p.f n) x).v j k hjk).val.app W) y)

/-- The displayed signed pairing on all homogeneous local pure tensors.
The global Hom complex is Mathlib's product of sheaf morphisms; forgetting scalars on
its source does not change a component. The formula fixes the pairing on generators.
Source: Stacks 0A8X and 0A90
(blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def IsExternalPairing (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J)
    (p : (underlying A).obj (U ⊗ V) ⟶
      CochainComplex.HomComplex (tensorComplex S A E H) J) : Prop :=
  IsLinearHomMap S A (U ⊗ V) (tensorComplex S A E H) J p ∧
  ∀ (r s q t : ℤ) (W : Cᵒᵖ) (w : U.X r) (z : V.X s)
    (e : (E.X q).val.obj W) (h : (H.X t).val.obj W),
    (((((p.f (r + s)) (coefficientTensor A U V r s w z)).v
      (q + t) ((q + t) + (r + s)) rfl).val.app W)
        (tensorComplexSection S A E H q t (q + t) rfl W e h)) =
      (s * q).negOnePow • unsignedEvaluation S A U V E H N M J u v i
        r s q t ((q + t) + (r + s)) (by omega) W w z e h

/-- The balancing shift comparison has the specified sign in the shifted first degree.
Source: Stacks 0A8X and the two-variable sign calculation
(blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def IsBalancingShift (U : Coeff A) (E : Complex S A)
    (η : tensorComplex S A ((constantComplex S A).obj (U⟦(-1 : ℤ)⟧)) (E⟦(1 : ℤ)⟧) ≅
      tensorComplex S A ((constantComplex S A).obj U) E) : Prop :=
  ∀ (r q : ℤ) (W : Cᵒᵖ) (w : (U⟦(-1 : ℤ)⟧).X r)
    (e : ((E⟦(1 : ℤ)⟧).X q).val.obj W),
    ((η.hom.f (r + q)).val.app W)
      (tensorComplexSection S A ((constantComplex S A).obj (U⟦(-1 : ℤ)⟧))
        (E⟦(1 : ℤ)⟧) r q (r + q) rfl W
        (constantSection S A ((U⟦(-1 : ℤ)⟧).X r) W w) e) =
      r.negOnePow • tensorComplexSection S A ((constantComplex S A).obj U) E
        (r + -1) (q + 1) (r + q) (by omega) W
        (constantSection S A (U.X (r + -1)) W w) e

/-- The first-variable Hom shift is normalized by `(-1)^n` in Hom degree `n`.
Source: Stacks 0A8X and lemma-RHom-triangulated
(blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def IsHomShift (B J : Complex S A)
    (θ : CochainComplex.HomComplex (B⟦(1 : ℤ)⟧) J ≅
      (CochainComplex.HomComplex B J)⟦(-1 : ℤ)⟧) : Prop :=
  ∀ (n : ℤ) (f : CochainComplex.HomComplex.Cochain (B⟦(1 : ℤ)⟧) J n)
    (j k : ℤ) (hjk : j + (n + -1) = k),
    ((θ.hom.f n) f).v j k hjk =
      n.negOnePow • ((B.shiftFunctorObjXIso 1 (j - 1) j (by omega)).inv ≫
        f.v (j - 1) k (by omega))

/-- Precompose a global Hom cochain with a chain map, component by component.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def precomposeCochain {B B' J : Complex S A} (f : B' ⟶ B) {n : ℤ}
    (g : CochainComplex.HomComplex.Cochain B J n) :
    CochainComplex.HomComplex.Cochain B' J n :=
  (CochainComplex.HomComplex.Cochain.ofHom f).comp g (zero_add n)

/-- The unsigned first tensor-shift comparison for module sheaves.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def tensorShift₁ (E H : Complex S A) (a : ℤ) :
    tensorComplex S A (E⟦a⟧) H ≅ (tensorComplex S A E H)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₁Iso E H (curriedTensor (Modules S A)) a

/-- The second tensor-shift comparison, with sign `(-1)^(a*q)` in first degree `q`.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def tensorShift₂ (E H : Complex S A) (a : ℤ) :
    tensorComplex S A E (H⟦a⟧) ≅ (tensorComplex S A E H)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₂Iso E H (curriedTensor (Modules S A)) a

/-- The unsigned first tensor-shift comparison for coefficient complexes.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def coefficientShift₁ (R : Type w) [CommRing R] (U V : Coeff R) (a : ℤ) :
    (U⟦a⟧ ⊗ V) ≅ (U ⊗ V)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₁Iso U V (curriedTensor (ModuleCat.{w} R)) a

/-- The coefficient comparison with sign `(-1)^(a*r)` in first degree `r`.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def coefficientShift₂ (R : Type w) [CommRing R] (U V : Coeff R) (a : ℤ) :
    (U ⊗ V⟦a⟧) ≅ (U ⊗ V)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₂Iso U V (curriedTensor (ModuleCat.{w} R)) a

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] Adjunction.rightAdjointLaxMonoidal
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification

private def scalarEnd (P : Modules S A) (a : A) : P ⟶ P where
  val := PresheafOfModules.sectionsSMul (S := (realizationRing S A).obj) P.val
    ⟨fun W ↦ (realizationRingUnit S A).app W a, by
      intro W V f
      exact (ConcreteCategory.congr_hom ((realizationRingUnit S A).naturality f) a).symm⟩

private theorem scalarEnd_naturality {P Q : Modules S A} (f : P ⟶ Q) (a : A) :
    f ≫ scalarEnd S A Q a = scalarEnd S A P a ≫ f := by
  apply SheafOfModules.hom_ext
  ext W x
  exact ((f.val.app W).hom.map_smul _ x).symm

private def scalarComplex (J : Complex S A) (a : A) : J ⟶ J where
  f n := scalarEnd S A (J.X n) a
  comm' n m _ := (scalarEnd_naturality S A (J.d n m) a).symm

set_option backward.isDefEq.respectTransparency false in
private def postcomposeHom {D : Type*} [Category* D] [Preadditive D]
    {B J J' : CochainComplex D ℤ} (f : J ⟶ J') :
    CochainComplex.HomComplex B J ⟶ CochainComplex.HomComplex B J' where
  f n := AddCommGrpCat.ofHom
    { toFun := fun g ↦ g.comp (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n)
      map_zero' := by simp
      map_add' := fun _ _ ↦ CochainComplex.HomComplex.Cochain.add_comp _ _ _ _ }
  comm' n m _ := by
    ext g
    exact CochainComplex.HomComplex.δ_comp_ofHom g f m

set_option backward.isDefEq.respectTransparency false in
private def homShiftIso {D : Type*} [Category* D] [Preadditive D]
    (B J : CochainComplex D ℤ) :
    CochainComplex.HomComplex (B⟦(1 : ℤ)⟧) J ≅
      (CochainComplex.HomComplex B J)⟦(-1 : ℤ)⟧ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (CochainComplex.HomComplex.Cochain.leftShiftAddEquiv B J
      (n + -1) 1 n (by omega)).symm.toAddCommGrpIso) (by
    intro n m hnm
    ext f
    change (-1 : ℤ).negOnePow • CochainComplex.HomComplex.δ (n + -1) (m + -1)
        (f.leftUnshift (n + -1) (by omega)) =
      (CochainComplex.HomComplex.δ n m f).leftUnshift (m + -1) (by omega)
    rw [CochainComplex.HomComplex.Cochain.δ_leftUnshift f (n + -1) (by omega)
      (m + -1) m (by omega)]
    simp)

private theorem homShiftIso_spec (B J : Complex S A) :
    IsHomShift S A B J (homShiftIso B J) := by
  intro n f j k hjk
  change (f.leftUnshift (n + -1) (by omega)).v j k hjk = _
  rw [CochainComplex.HomComplex.Cochain.leftUnshift_v f (n + -1)
    (by omega) j k hjk (j - 1) (by omega)]
  simp only [one_mul, sub_self, mul_zero, Int.zero_ediv, add_zero]

set_option backward.isDefEq.respectTransparency false in
private def precomposeHom {D : Type*} [Category* D] [Preadditive D]
    {B B' J : CochainComplex D ℤ} (f : B' ⟶ B) :
    CochainComplex.HomComplex B J ⟶ CochainComplex.HomComplex B' J where
  f n := AddCommGrpCat.ofHom
    { toFun := fun g ↦ (CochainComplex.HomComplex.Cochain.ofHom f).comp g (zero_add n)
      map_zero' := by simp
      map_add' := fun _ _ ↦ CochainComplex.HomComplex.Cochain.comp_add _ _ _ _ }
  comm' n m _ := by
    ext g
    exact CochainComplex.HomComplex.δ_ofHom_comp f g m

set_option backward.isDefEq.respectTransparency false in
private theorem precomposeHom_comp {D : Type*} [Category* D] [Preadditive D]
    {B B' B'' J : CochainComplex D ℤ} (f : B' ⟶ B) (g : B'' ⟶ B') :
    precomposeHom (J := J) f ≫ precomposeHom g = precomposeHom (g ≫ f) := by
  ext n c
  change CochainComplex.HomComplex.Cochain B J n at c
  change (CochainComplex.HomComplex.Cochain.ofHom g).comp
      ((CochainComplex.HomComplex.Cochain.ofHom f).comp c (zero_add n)) (zero_add n) =
    (CochainComplex.HomComplex.Cochain.ofHom (g ≫ f)).comp c (zero_add n)
  rw [CochainComplex.HomComplex.Cochain.ofHom_comp]
  exact (CochainComplex.HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain
    (CochainComplex.HomComplex.Cochain.ofHom g)
    (CochainComplex.HomComplex.Cochain.ofHom f) c (zero_add n)).symm

set_option backward.isDefEq.respectTransparency false in
private def precomposeHomIso {D : Type*} [Category* D] [Preadditive D]
    {B B' : CochainComplex D ℤ} (e : B ≅ B') (J : CochainComplex D ℤ) :
    CochainComplex.HomComplex B J ≅ CochainComplex.HomComplex B' J where
  hom := precomposeHom e.inv
  inv := precomposeHom e.hom
  hom_inv_id := by
    rw [precomposeHom_comp, e.hom_inv_id]
    ext n c
    exact CochainComplex.HomComplex.Cochain.id_comp c
  inv_hom_id := by
    rw [precomposeHom_comp, e.inv_hom_id]
    ext n c
    exact CochainComplex.HomComplex.Cochain.id_comp c

section GenericBalance

variable {D : Type*} [Category* D] [Preadditive D]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [∀ (X Y : GradedObject ℤ D), X.HasTensor Y]

private def balanceTensorIso (P E : CochainComplex D ℤ) :
    HomologicalComplex.tensorObj (P⟦(-1 : ℤ)⟧) (E⟦(1 : ℤ)⟧) ≅
      HomologicalComplex.tensorObj P E :=
  CochainComplex.mapBifunctorShift₂Iso (P⟦(-1 : ℤ)⟧) E (curriedTensor D) 1 ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso
      (CochainComplex.mapBifunctorShift₁Iso P E (curriedTensor D) (-1)) ≪≫
    (shiftFunctorCompIsoId _ (-1 : ℤ) (1 : ℤ) (by omega)).app _

set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in
private theorem balanceTensorIso_ι (P E : CochainComplex D ℤ) (r q : ℤ) :
    HomologicalComplex.ιTensorObj (P⟦(-1 : ℤ)⟧) (E⟦(1 : ℤ)⟧)
        r q (r + q) rfl ≫ (balanceTensorIso P E).hom.f (r + q) =
      r.negOnePow • HomologicalComplex.ιTensorObj P E
        (r + -1) (q + 1) (r + q) (by omega) := by
  dsimp only [balanceTensorIso, Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.comp_f]
  rw [← Category.assoc, ← Category.assoc]
  erw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ _ 1 r q (r + q) rfl
    (q + 1) (r + q + 1) rfl rfl]
  simp only [mul_one, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id,
    Linear.units_smul_comp, whiskerLeft_id]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, CochainComplex.shiftFunctor_map_f',
    Linear.units_smul_comp, Category.assoc]
  erw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ _ (-1) r (q + 1)
    (r + q + 1) (by omega) (r + -1) (r + q) rfl (by omega)]
  simp [shiftFunctorCompIsoId, CochainComplex.shiftFunctorAdd'_hom_app_f',
    CochainComplex.shiftFunctorZero_hom_app_f, CochainComplex.shiftFunctorObjXIso,
    id_whiskerRight]
  erw [id_whiskerRight]
  simp [CochainComplex.shiftFunctorAdd'_inv_app_f', HomologicalComplex.XIsoOfEq]
  erw [Category.id_comp]

private def balanceTensorIsoOfIso (P E P' : CochainComplex D ℤ)
    (e : P' ≅ P⟦(-1 : ℤ)⟧) :
    HomologicalComplex.tensorObj P' (E⟦(1 : ℤ)⟧) ≅ HomologicalComplex.tensorObj P E :=
  ((curriedTensor D).map₂CochainComplex.flip.obj (E⟦(1 : ℤ)⟧)).mapIso e ≪≫
    balanceTensorIso P E

set_option backward.isDefEq.respectTransparency false in
private theorem balanceTensorIsoOfIso_ι (P E P' : CochainComplex D ℤ)
    (e : P' ≅ P⟦(-1 : ℤ)⟧) (r q : ℤ) :
    HomologicalComplex.ιTensorObj P' (E⟦(1 : ℤ)⟧) r q (r + q) rfl ≫
      (balanceTensorIsoOfIso P E P' e).hom.f (r + q) =
    (e.hom.f r ▷ (E⟦(1 : ℤ)⟧).X q) ≫
      (r.negOnePow • HomologicalComplex.ιTensorObj P E
        (r + -1) (q + 1) (r + q) (by omega)) := by
  dsimp only [balanceTensorIsoOfIso, Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.comp_f]
  rw [← Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.comp_id, Category.assoc]
  rw [balanceTensorIso_ι]
  erw [Category.id_comp]
  rfl

end GenericBalance

private def balancingIso (U : Coeff A) (E : Complex S A) :
    tensorComplex S A ((constantComplex S A).obj (U⟦(-1 : ℤ)⟧)) (E⟦(1 : ℤ)⟧) ≅
      tensorComplex S A ((constantComplex S A).obj U) E :=
  balanceTensorIsoOfIso ((constantComplex S A).obj U) E
    ((constantComplex S A).obj (U⟦(-1 : ℤ)⟧))
    (((constantComplex S A).commShiftIso (-1)).app U)

private theorem units_smul_app {P Q : Modules S A} (f : P ⟶ Q) (a : ℤˣ)
    (W : Cᵒᵖ) (x : P.val.obj W) :
    (a • f).val.app W x = a • f.val.app W x := by
  rcases Int.units_eq_one_or a with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul]
    rfl

private theorem map_units_smul {M N F : Type*} [AddGroup M] [AddGroup N]
    [FunLike F M N] [AddMonoidHomClass F M N] (f : F) (a : ℤˣ) (x : M) :
    f (a • x) = a • f x := by
  simp only [Units.smul_def, map_zsmul]

set_option backward.isDefEq.respectTransparency false in
private theorem balancingIso_ι (U : Coeff A) (E : Complex S A) (r q : ℤ) :
    CochainComplex.ιMapBifunctor ((constantComplex S A).obj (U⟦(-1 : ℤ)⟧))
        (E⟦(1 : ℤ)⟧) (curriedTensor (Modules S A)) r q (r + q) rfl ≫
      (balancingIso S A U E).hom.f (r + q) =
    r.negOnePow • CochainComplex.ιMapBifunctor ((constantComplex S A).obj U) E
      (curriedTensor (Modules S A)) (r + -1) (q + 1) (r + q) (by omega) := by
  have he := balanceTensorIsoOfIso_ι ((constantComplex S A).obj U) E
    ((constantComplex S A).obj (U⟦(-1 : ℤ)⟧))
    (((constantComplex S A).commShiftIso (-1)).app U) r q
  change _ = (𝟙 _ ▷ _) ≫ _ at he
  erw [id_whiskerRight, Category.id_comp] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
private theorem balancingIso_spec (U : Coeff A) (E : Complex S A) :
    IsBalancingShift S A U E (balancingIso S A U E) := by
  intro r q W w e
  have h := congrArg (fun f ↦ f.val.app W
    (tensorSection S A ((constantComplex S A).obj (U⟦(-1 : ℤ)⟧) |>.X r)
      ((E⟦(1 : ℤ)⟧).X q) W
        (constantSection S A ((U⟦(-1 : ℤ)⟧).X r) W w) e))
    (balancingIso_ι S A U E r q)
  change _ = _ at h
  rw [units_smul_app] at h
  exact h

private theorem constantSection_smul (Q : ModuleCat.{max u v} A) (W : Cᵒᵖ)
    (a : A) (x : Q) :
    constantSection S A Q W (a • x) =
      (realizationRingUnit S A).app W a • constantSection S A Q W x := by
  let := (realizationRingUnit_locallyBijective S A).1
  let := (realizationRingUnit_locallyBijective S A).2
  exact ((PresheafOfModules.toSheafify (realizationRingUnit S A)
    (toSheafify S ((siteConstantModulePresheafGeneral (C := C) A).obj Q).presheaf)).app W
      ).hom.map_smul a x

private theorem constantSection_map {Q Q' : ModuleCat.{max u v} A} (f : Q ⟶ Q')
    (W : Cᵒᵖ) (x : Q) :
    ((commutativeSiteConstantModuleFunctor S A).map f).val.app W
      (constantSection S A Q W x) = constantSection S A Q' W (f x) := by
  exact (ConcreteCategory.congr_hom (congr_app (toSheafify_naturality S
    ((PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := C) A).map f))) W) x).symm

set_option backward.isDefEq.respectTransparency false in
private def insertSection (P Q : Modules S A) (x : ∀ W, P.val.obj W)
    (hx : ∀ (W V : Cᵒᵖ) (f : W ⟶ V), P.val.map f (x W) = x V) :
    Q ⟶ P ⊗ Q where
  val :=
    { app := fun W ↦ ModuleCat.ofHom
        (SheafOfModules.CochainScalarConstruction.pureBilin
          (realizationRing S A) P Q W (x W))
      naturality := by
        intro W V f
        ext e
        have hp := SheafOfModules.CochainScalarConstruction.pure_restrict
          (realizationRing S A) P Q f (x W) e
        exact (congrArg (fun z ↦ SheafOfModules.CochainScalarConstruction.pure
          (realizationRing S A) P Q V z (Q.val.map f e)) (hx W V f).symm).trans hp.symm }

set_option backward.isDefEq.respectTransparency false in
private def insertConstant (Q : ModuleCat.{max u v} A) (P : Modules S A) (w : Q) :
    P ⟶ (commutativeSiteConstantModuleFunctor S A).obj Q ⊗ P :=
  insertSection S A ((commutativeSiteConstantModuleFunctor S A).obj Q) P
    (fun W ↦ constantSection S A Q W w) (by
      intro W V f
      exact (NatTrans.naturality_apply
        (toSheafify S ((siteConstantModulePresheafGeneral (C := C) A).obj Q).presheaf)
        f w).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem insertSection_map {P P' Q : Modules S A} (f : P ⟶ P')
    (x : ∀ W, P.val.obj W) (x' : ∀ W, P'.val.obj W)
    (hx : ∀ (W V : Cᵒᵖ) (g : W ⟶ V), P.val.map g (x W) = x V)
    (hx' : ∀ (W V : Cᵒᵖ) (g : W ⟶ V), P'.val.map g (x' W) = x' V)
    (h : ∀ W, f.val.app W (x W) = x' W) :
    insertSection S A P Q x hx ≫ f ▷ Q = insertSection S A P' Q x' hx' := by
  apply SheafOfModules.hom_ext
  ext W e
  have hp := SheafOfModules.CochainScalarConstruction.pure_map (realizationRing S A)
    f (𝟙 Q) W (x W) e
  change (f ▷ Q).val.app W
      (SheafOfModules.CochainScalarConstruction.pure (realizationRing S A) P Q W (x W) e) =
    SheafOfModules.CochainScalarConstruction.pure (realizationRing S A) P' Q W (x' W) e
  simpa only [tensorHom_id, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply, h] using hp

set_option backward.isDefEq.respectTransparency false in
private theorem insertSection_naturality (P : Modules S A) {Q Q' : Modules S A}
    (f : Q ⟶ Q') (x : ∀ W, P.val.obj W)
    (hx : ∀ (W V : Cᵒᵖ) (g : W ⟶ V), P.val.map g (x W) = x V) :
    f ≫ insertSection S A P Q' x hx = insertSection S A P Q x hx ≫ P ◁ f := by
  apply SheafOfModules.hom_ext
  ext W e
  have hp := SheafOfModules.CochainScalarConstruction.pure_map (realizationRing S A)
    (𝟙 P) f W (x W) e
  change SheafOfModules.CochainScalarConstruction.pure (realizationRing S A) P Q' W
      (x W) (f.val.app W e) =
    (P ◁ f).val.app W
      (SheafOfModules.CochainScalarConstruction.pure (realizationRing S A) P Q W (x W) e)
  simpa only [id_tensorHom, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] using hp.symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem insertConstant_map {Q Q' : ModuleCat.{max u v} A}
    (f : Q ⟶ Q') (P : Modules S A) (w : Q) :
    insertConstant S A Q P w ≫
        (commutativeSiteConstantModuleFunctor S A).map f ▷ P =
      insertConstant S A Q' P (f w) := by
  apply insertSection_map
  intro W
  exact constantSection_map S A f W w

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem insertConstant_naturality (Q : ModuleCat.{max u v} A)
    {P P' : Modules S A} (f : P ⟶ P') (w : Q) :
    f ≫ insertConstant S A Q P' w =
      insertConstant S A Q P w ≫ (commutativeSiteConstantModuleFunctor S A).obj Q ◁ f := by
  apply insertSection_naturality

attribute [local irreducible] commutativeSiteConstantModuleFunctor

private def evaluationMorphism (U : Coeff A) (E N : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (r q : ℤ) (w : U.X r) : E.X q ⟶ N.X (r + q) :=
  insertConstant S A (U.X r) (E.X q) w ≫
    CochainComplex.ιMapBifunctor ((constantComplex S A).obj U) E
      (curriedTensor (Modules S A)) r q (r + q) rfl ≫ u.f (r + q)

set_option backward.isDefEq.respectTransparency false in
private def evaluationCochain (U : Coeff A) (E N : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (r : ℤ) (w : U.X r) : CochainComplex.HomComplex.Cochain E N r :=
  CochainComplex.HomComplex.Cochain.mk fun q k hqk ↦
    insertConstant S A (U.X r) (E.X q) w ≫
      CochainComplex.ιMapBifunctor ((constantComplex S A).obj U) E
        (curriedTensor (Modules S A)) r q k (by omega) ≫ u.f k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem evaluationCochain_δ (U : Coeff A) (E N : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (r : ℤ) (w : U.X r) :
    CochainComplex.HomComplex.δ r (r + 1) (evaluationCochain S A U E N u r w) =
      evaluationCochain S A U E N u (r + 1) (U.d r (r + 1) w) := by
  dsimp only [constantComplex, Functor.mapHomologicalComplex_obj_X,
    Functor.mapHomologicalComplex_obj_d] at u ⊢
  apply CochainComplex.HomComplex.Cochain.ext
  intro q k hqk
  rw [CochainComplex.HomComplex.δ_v r (r + 1) rfl _ q k hqk (q + r) (q + 1)
    (by omega) rfl]
  simp only [evaluationCochain, CochainComplex.HomComplex.Cochain.mk_v, Category.assoc]
  rw [u.comm, ← Category.assoc _ _ (u.f k)]
  erw [CochainComplex.ιTensorObj_d_assoc ((constantComplex S A).obj U) E
    r q (q + r) k (by omega) (by omega)]
  simp only [constantComplex, Functor.mapHomologicalComplex_obj_X,
    Functor.mapHomologicalComplex_obj_d,
    Preadditive.comp_add, Linear.comp_units_smul, Category.assoc]
  erw [Preadditive.add_comp, Preadditive.comp_add]
  simp only [Category.assoc]
  erw [Linear.units_smul_comp]
  erw [Linear.comp_units_smul]
  erw [insertConstant_map_assoc]
  simp only [Category.assoc]
  erw [← insertConstant_naturality_assoc]
  simp only [Int.negOnePow_succ, Units.neg_smul, neg_smul, one_smul]
  abel

attribute [local semireducible] commutativeSiteConstantModuleFunctor

set_option backward.isDefEq.respectTransparency false in
private theorem evaluationMorphism_add (U : Coeff A) (E N : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (r q : ℤ) (w w' : U.X r) :
    evaluationMorphism S A U E N u r q (w + w') =
      evaluationMorphism S A U E N u r q w +
        evaluationMorphism S A U E N u r q w' := by
  apply SheafOfModules.hom_ext
  ext W e
  change evaluate S A U E N u r q W (w + w') e =
    evaluate S A U E N u r q W w e + evaluate S A U E N u r q W w' e
  unfold evaluate tensorComplexSection constantSection
  change _ = _
  rw [map_add]
  change _ = _
  rw [show tensorSection S A _ _ W (_ + _) e = _ from
    SheafOfModules.CochainScalarConstruction.pure_add_left (realizationRing S A)
      _ _ W _ _ e]
  rw [map_add, map_add]
  rfl

attribute [local irreducible] commutativeSiteConstantModuleFunctor

set_option backward.isDefEq.respectTransparency false in
private theorem evaluate_smul (U : Coeff A) (E N : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (r q : ℤ) (W : Cᵒᵖ) (a : A) (w : U.X r) (e : (E.X q).val.obj W) :
    evaluate S A U E N u r q W (a • w) e =
      (realizationRingUnit S A).app W a • evaluate S A U E N u r q W w e := by
  unfold evaluate tensorComplexSection
  rw [constantSection_smul]
  have hp := SheafOfModules.CochainScalarConstruction.pure_smul_left
    (realizationRing S A) ((commutativeSiteConstantModuleFunctor S A).obj (U.X r))
    (E.X q) W ((realizationRingUnit S A).app W a)
    (constantSection S A (U.X r) W w) e
  change tensorSection S A _ _ W (_ • _) e = _ at hp
  change (u.f (r + q)).val.app W
      ((CochainComplex.ιMapBifunctor ((constantComplex S A).obj U) E
        (curriedTensor (Modules S A)) r q (r + q) rfl).val.app W
        (tensorSection S A ((commutativeSiteConstantModuleFunctor S A).obj (U.X r))
          (E.X q) W _ e)) = _
  rw [hp, map_smul, map_smul]
  rfl

section GenericTensorCochains

open CochainComplex HomologicalComplex CochainComplex.HomComplex

variable {D : Type*} [Category* D] [Preadditive D]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [∀ (X Y : GradedObject ℤ D), X.HasTensor Y]
private def tensorCochain {E H N M : CochainComplex D ℤ} {r s : ℤ}
    (f : Cochain E N r) (g : Cochain H M s) (n : ℤ) (hn : r + s = n) :
    Cochain (HomologicalComplex.tensorObj E H) (HomologicalComplex.tensorObj N M) n :=
  Cochain.mk fun j k hjk ↦ mapBifunctorDesc fun q t (hqt : q + t = j) ↦
    (s * q).negOnePow • ((f.v q (q + r) rfl ⊗ₘ g.v t (t + s) rfl) ≫
      ιTensorObj N M (q + r) (t + s) k (by omega))
@[reassoc]
private theorem ι_tensorCochain {E H N M : CochainComplex D ℤ} {r s : ℤ}
    (f : Cochain E N r) (g : Cochain H M s) (n : ℤ) (hn : r + s = n)
    (q t j k a b : ℤ) (hqt : q + t = j) (hjk : j + n = k)
    (ha : q + r = a) (hb : t + s = b) :
    ιTensorObj E H q t j hqt ≫ (tensorCochain f g n hn).v j k hjk =
      (s * q).negOnePow • ((f.v q a ha ⊗ₘ g.v t b hb) ≫
        ιTensorObj N M a b k (by omega)) := by
  subst a b
  simp only [tensorCochain, Cochain.mk_v, ι_mapBifunctorDesc]
private theorem smul_tensor {X Y Z W : D} (f : X ⟶ Y) (g : Z ⟶ W) (a : ℤˣ) :
    (a • f) ⊗ₘ g = a • (f ⊗ₘ g) := by
  rcases Int.units_eq_one_or a with rfl | rfl
  · simp
  · simp only [Units.neg_smul, one_smul]
    rw [tensorHom_def, tensorHom_def]
    change (tensorRight Z).map (-f) ≫ Y ◁ g =
      -((tensorRight Z).map f ≫ Y ◁ g)
    rw [Functor.map_neg, Preadditive.neg_comp]
private theorem tensor_smul {X Y Z W : D} (f : X ⟶ Y) (g : Z ⟶ W) (a : ℤˣ) :
    f ⊗ₘ (a • g) = a • (f ⊗ₘ g) := by
  rcases Int.units_eq_one_or a with rfl | rfl
  · simp
  · simp only [Units.neg_smul, one_smul]
    rw [tensorHom_def, tensorHom_def]
    change f ▷ Z ≫ (tensorLeft Y).map (-g) =
      -(f ▷ Z ≫ (tensorLeft Y).map g)
    rw [Functor.map_neg, Preadditive.comp_neg]
@[reassoc]
private theorem tensor_ι_d (P K : CochainComplex D ℤ) (p q r r' : ℤ)
    (h : p + q = r) (h' : r + 1 = r') :
    ιTensorObj P K p q r h ≫ (HomologicalComplex.tensorObj P K).d r r' =
      P.d p (p + 1) ▷ K.X q ≫ ιTensorObj P K (p + 1) q r' (by omega) +
        p.negOnePow • (P.X p ◁ K.d q (q + 1) ≫
          ιTensorObj P K p (q + 1) r' (by omega)) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (rfl : (ComplexShape.up ℤ).Rel p (p + 1)) _ _ (show p + 1 + q = r' by omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
      (rfl : (ComplexShape.up ℤ).Rel q (q + 1)) _ (show p + (q + 1) = r' by omega)]
  simp

private theorem tensorCochain_δ {E H N M : CochainComplex D ℤ} {r s : ℤ}
    (f : Cochain E N r) (g : Cochain H M s) :
    δ (r + s) (r + s + 1) (tensorCochain f g (r + s) rfl) =
      tensorCochain (δ r (r + 1) f) g (r + s + 1) (by omega) +
        r.negOnePow • tensorCochain f (δ s (s + 1) g) (r + s + 1) (by omega) := by
  apply Cochain.ext
  intro j k hjk
  rw [δ_v _ _ rfl _ j k hjk (j + (r + s)) (j + 1) (by omega) rfl]
  simp only [Cochain.add_v, Cochain.units_smul_v]
  apply mapBifunctor.hom_ext
  intro q t hqt
  have hqt' : q + t = j := hqt
  rw [Preadditive.comp_add, Linear.comp_units_smul]
  rw [← Category.assoc, ι_tensorCochain f g _ _ q t j (j + (r + s)) (q + r) (t + s)
    hqt rfl rfl rfl]
  rw [Linear.units_smul_comp, Category.assoc]
  erw [tensor_ι_d N M (q + r) (t + s) (j + (r + s)) k
    (by omega) (by omega)]
  rw [← Category.assoc]
  erw [tensor_ι_d E H q t j (j + 1) hqt rfl]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc]
  rw [ι_tensorCochain f g _ _ (q + 1) t (j + 1) k (q + r + 1) (t + s)
    (by omega) (by omega) (by omega) rfl]
  rw [ι_tensorCochain f g _ _ q (t + 1) (j + 1) k (q + r) (t + s + 1)
    (by omega) (by omega) rfl (by omega)]
  rw [ι_tensorCochain (δ r (r + 1) f) g _ _ q t j k (q + r + 1) (t + s)
    hqt hjk (by omega) rfl]
  rw [ι_tensorCochain f (δ s (s + 1) g) _ _ q t j k (q + r) (t + s + 1)
    hqt hjk rfl (by omega)]
  rw [δ_v r (r + 1) rfl f q (q + r + 1) (by omega) (q + r) (q + 1)
    (by omega) rfl]
  rw [δ_v s (s + 1) rfl g t (t + s + 1) (by omega) (t + s) (t + 1)
    (by omega) rfl]
  simp only [MonoidalPreadditive.add_tensor, MonoidalPreadditive.tensor_add,
    smul_tensor, tensor_smul, Preadditive.comp_add, Preadditive.add_comp,
    Linear.units_smul_comp, Linear.comp_units_smul, smul_add, smul_smul,
    tensorHom_comp_whiskerRight_assoc, tensorHom_comp_whiskerLeft_assoc,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc]
  have hs₂ : (s * q).negOnePow * (q + r).negOnePow =
      r.negOnePow * ((s + 1) * q).negOnePow := by
    simp only [add_mul, one_mul, Int.negOnePow_add]
    ac_rfl
  have hs₃ : (r + s + 1).negOnePow * (q.negOnePow * (s * q).negOnePow) =
      r.negOnePow * (((s + 1) * q).negOnePow * (s + 1).negOnePow) := by
    simp only [add_mul, one_mul, Int.negOnePow_add]
    ac_rfl
  have hs₁ : (r + s + 1).negOnePow * (s * (q + 1)).negOnePow =
      (s * q).negOnePow * (r + 1).negOnePow := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_add]
    apply (Int.negOnePow_eq_iff _ _).2
    refine ⟨s, ?_⟩
    ring
  rw [hs₁, hs₂, hs₃]
  abel

@[reassoc]
private theorem ιTensor_XIso (P Q : CochainComplex D ℤ) (p q n m : ℤ)
    (hn : p + q = n) (hm : n = m) :
    ιTensorObj P Q p q n hn ≫
        ((HomologicalComplex.tensorObj P Q).XIsoOfEq hm).hom =
      ιTensorObj P Q p q m (hn.trans hm) := by
  subst m
  simp

end GenericTensorCochains

section PairingData

variable (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J)

set_option backward.isDefEq.respectTransparency false in
private def pairingCochain (r s n : ℤ) (hn : r + s = n)
    (w : U.X r) (z : V.X s) :
    CochainComplex.HomComplex.Cochain (tensorComplex S A E H) J n :=
  CochainComplex.HomComplex.Cochain.mk fun j k hjk ↦
    HomologicalComplex.mapBifunctorDesc fun q t (hqt : q + t = j) ↦
      (s * q).negOnePow •
        ((evaluationMorphism S A U E N u r q w ⊗ₘ
          evaluationMorphism S A V H M v s t z) ≫
          CochainComplex.ιMapBifunctor N M (curriedTensor (Modules S A))
            (r + q) (s + t) ((r + q) + (s + t)) rfl ≫
          i.f ((r + q) + (s + t)) ≫ (J.XIsoOfEq (by omega)).hom)

set_option backward.isDefEq.respectTransparency false in
private theorem pairingCochain_as_tensor (r s n : ℤ) (hn : r + s = n)
    (w : U.X r) (z : V.X s) :
    pairingCochain S A U V E H N M J u v i r s n hn w z =
      (tensorCochain (evaluationCochain S A U E N u r w)
        (evaluationCochain S A V H M v s z) n hn).comp
          (CochainComplex.HomComplex.Cochain.ofHom i) (add_zero n) := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro j k hjk
  rw [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro q t hqt
  have hqt' : q + t = j := hqt
  rw [← Category.assoc, ι_tensorCochain (evaluationCochain S A U E N u r w)
    (evaluationCochain S A V H M v s z) n hn q t j k (r + q) (s + t)
      hqt hjk (by omega) (by omega)]
  simp only [pairingCochain, CochainComplex.HomComplex.Cochain.mk_v,
    HomologicalComplex.ι_mapBifunctorDesc, Linear.units_smul_comp, Category.assoc]
  congr 1
  change (evaluationMorphism S A U E N u r q w ⊗ₘ
      evaluationMorphism S A V H M v s t z) ≫
      CochainComplex.ιMapBifunctor N M (curriedTensor (Modules S A))
        (r + q) (s + t) _ rfl ≫ i.f _ ≫ (J.XIsoOfEq _).hom = _
  rw [HomologicalComplex.XIsoOfEq_hom_naturality]
  rw [← Category.assoc _ _ (i.f k)]
  erw [ιTensor_XIso]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pairingCochain_δ (r s : ℤ) (w : U.X r) (z : V.X s) :
    CochainComplex.HomComplex.δ (r + s) (r + s + 1)
        (pairingCochain S A U V E H N M J u v i r s (r + s) rfl w z) =
      pairingCochain S A U V E H N M J u v i (r + 1) s (r + s + 1)
        (by omega) (U.d r (r + 1) w) z +
      r.negOnePow • pairingCochain S A U V E H N M J u v i r (s + 1) (r + s + 1)
        (by omega) w (V.d s (s + 1) z) := by
  simp only [pairingCochain_as_tensor, CochainComplex.HomComplex.δ_comp_ofHom,
    tensorCochain_δ, evaluationCochain_δ, CochainComplex.HomComplex.Cochain.add_comp,
    CochainComplex.HomComplex.Cochain.units_smul_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem pairingCochain_add_left (r s n : ℤ) (hn : r + s = n)
    (w w' : U.X r) (z : V.X s) :
    pairingCochain S A U V E H N M J u v i r s n hn (w + w') z =
      pairingCochain S A U V E H N M J u v i r s n hn w z +
        pairingCochain S A U V E H N M J u v i r s n hn w' z := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro j k hjk
  simp only [pairingCochain, CochainComplex.HomComplex.Cochain.mk_v,
    CochainComplex.HomComplex.Cochain.add_v]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro q t hqt
  simp only [Preadditive.comp_add, HomologicalComplex.ι_mapBifunctorDesc,
    evaluationMorphism_add, tensorHom_def, MonoidalPreadditive.add_whiskerRight,
    Preadditive.add_comp,
    smul_add]

set_option backward.isDefEq.respectTransparency false in
private theorem pairingCochain_add_right (r s n : ℤ) (hn : r + s = n)
    (w : U.X r) (z z' : V.X s) :
    pairingCochain S A U V E H N M J u v i r s n hn w (z + z') =
      pairingCochain S A U V E H N M J u v i r s n hn w z +
        pairingCochain S A U V E H N M J u v i r s n hn w z' := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro j k hjk
  simp only [pairingCochain, CochainComplex.HomComplex.Cochain.mk_v,
    CochainComplex.HomComplex.Cochain.add_v]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro q t hqt
  simp only [Preadditive.comp_add, HomologicalComplex.ι_mapBifunctorDesc,
    evaluationMorphism_add, tensorHom_def, MonoidalPreadditive.whiskerLeft_add,
    Preadditive.add_comp,
    smul_add]

set_option backward.isDefEq.respectTransparency false in
private theorem pairing_hom_ext (U V : Coeff A) (E H J : Complex S A) (a : ℤ)
    (p p' : (underlying A).obj (U ⊗ V) ⟶
      (CochainComplex.HomComplex (tensorComplex S A E H) J)⟦a⟧)
    (h : ∀ (r s q t : ℤ) (W : Cᵒᵖ) (w : U.X r) (z : V.X s)
      (e : (E.X q).val.obj W) (h : (H.X t).val.obj W),
      (((((p.f (r + s)) (coefficientTensor A U V r s w z)).v
        (q + t) ((q + t) + ((r + s) + a)) rfl).val.app W)
          (tensorComplexSection S A E H q t (q + t) rfl W e h)) =
      (((((p'.f (r + s)) (coefficientTensor A U V r s w z)).v
        (q + t) ((q + t) + ((r + s) + a)) rfl).val.app W)
          (tensorComplexSection S A E H q t (q + t) rfl W e h))) : p = p' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map
    (K₁ := U) (K₂ := V) (F := curriedTensor (ModuleCat.{max u v} A))
    (c := ComplexShape.up ℤ) (forget₂ (ModuleCat A) AddCommGrpCat)
  intro r s hrs
  have hrs' : r + s = n := hrs
  subst n
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul w z =>
    apply CochainComplex.HomComplex.Cochain.ext
    intro j k hjk
    subst k
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro q t hqt
    have hqt' : q + t = j := hqt
    subst j
    apply SheafOfModules.CochainScalarConstruction.pure_hom_ext (realizationRing S A)
    intro W e h'
    exact h r s q t W w z e h'

set_option backward.isDefEq.respectTransparency false in
private theorem pairingCochain_section (r s n : ℤ) (hn : r + s = n)
    (q t j k : ℤ) (hqt : q + t = j) (hjk : j + n = k)
    (W : Cᵒᵖ) (w : U.X r) (z : V.X s)
    (e : (E.X q).val.obj W) (h : (H.X t).val.obj W) :
    (((pairingCochain S A U V E H N M J u v i r s n hn w z).v j k hjk).val.app W)
        (tensorComplexSection S A E H q t j hqt W e h) =
      (s * q).negOnePow • unsignedEvaluation S A U V E H N M J u v i r s q t k
        (by omega) W w z e h := by
  have he : CochainComplex.ιMapBifunctor E H (curriedTensor (Modules S A))
      q t j hqt ≫ (pairingCochain S A U V E H N M J u v i r s n hn w z).v j k hjk =
      (s * q).negOnePow •
        ((evaluationMorphism S A U E N u r q w ⊗ₘ
          evaluationMorphism S A V H M v s t z) ≫
          CochainComplex.ιMapBifunctor N M (curriedTensor (Modules S A))
            (r + q) (s + t) ((r + q) + (s + t)) rfl ≫
          i.f ((r + q) + (s + t)) ≫ (J.XIsoOfEq (by omega)).hom) :=
    by
      simp only [pairingCochain, CochainComplex.HomComplex.Cochain.mk_v,
        HomologicalComplex.ι_mapBifunctorDesc]
  have he' := congrArg (fun f ↦ f.val.app W
    (tensorSection S A (E.X q) (H.X t) W e h)) he
  rw [units_smul_app] at he'
  change _ = _ at he'
  refine he'.trans ?_
  congr 1
  have hp := SheafOfModules.CochainScalarConstruction.pure_map (realizationRing S A)
    (evaluationMorphism S A U E N u r q w)
    (evaluationMorphism S A V H M v s t z) W e h
  change _ = tensorSection S A _ _ W _ _ at hp
  unfold unsignedEvaluation tensorComplexSection
  exact congrArg (fun x ↦ (J.XIsoOfEq _).hom.val.app W
    ((i.f _).val.app W ((CochainComplex.ιMapBifunctor N M
      (curriedTensor (Modules S A)) _ _ _ rfl).val.app W x))) hp

set_option backward.isDefEq.respectTransparency false in
private theorem unsignedEvaluation_smul_left (U V : Coeff A)
    (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J) (r s q t k : ℤ)
    (hk : (r + q) + (s + t) = k) (W : Cᵒᵖ) (a : A)
    (w : U.X r) (z : V.X s) (e : (E.X q).val.obj W) (h : (H.X t).val.obj W) :
    unsignedEvaluation S A U V E H N M J u v i r s q t k hk W (a • w) z e h =
      (realizationRingUnit S A).app W a •
        unsignedEvaluation S A U V E H N M J u v i r s q t k hk W w z e h := by
  unfold unsignedEvaluation tensorComplexSection
  rw [evaluate_smul]
  have hp := SheafOfModules.CochainScalarConstruction.pure_smul_left
    (realizationRing S A) (N.X (r + q)) (M.X (s + t)) W
    ((realizationRingUnit S A).app W a)
    (evaluate S A U E N u r q W w e) (evaluate S A V H M v s t W z h)
  change tensorSection S A _ _ W (_ • _) _ = _ at hp
  rw [hp, map_smul, map_smul, map_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pairingCochain_smul (r s n : ℤ) (hn : r + s = n)
    (a : A) (w : U.X r) (z : V.X s) :
    pairingCochain S A U V E H N M J u v i r s n hn (a • w) z =
      (postcomposeHom (scalarComplex S A J a)).f n
        (pairingCochain S A U V E H N M J u v i r s n hn w z) := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro j k hjk
  change _ = ((pairingCochain S A U V E H N M J u v i r s n hn w z).comp
    (CochainComplex.HomComplex.Cochain.ofHom (scalarComplex S A J a)) (add_zero n)).v
      j k hjk
  rw [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro q t hqt
  apply SheafOfModules.CochainScalarConstruction.pure_hom_ext (realizationRing S A)
  intro W e h
  change (((pairingCochain S A U V E H N M J u v i r s n hn (a • w) z).v
    j k hjk).val.app W) (tensorComplexSection S A E H q t j hqt W e h) =
    (realizationRingUnit S A).app W a •
      (((pairingCochain S A U V E H N M J u v i r s n hn w z).v
        j k hjk).val.app W) (tensorComplexSection S A E H q t j hqt W e h)
  rw [pairingCochain_section, pairingCochain_section, unsignedEvaluation_smul_left]
  exact smul_comm _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem pairingCochain_balanced (r s n : ℤ) (hn : r + s = n)
    (a : A) (w : U.X r) (z : V.X s) :
    pairingCochain S A U V E H N M J u v i r s n hn (a • w) z =
      pairingCochain S A U V E H N M J u v i r s n hn w (a • z) := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro j k hjk
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro q t hqt
  apply SheafOfModules.CochainScalarConstruction.pure_hom_ext (realizationRing S A)
  intro W e h
  change (((pairingCochain S A U V E H N M J u v i r s n hn (a • w) z).v
      j k hjk).val.app W) (tensorComplexSection S A E H q t j hqt W e h) =
    (((pairingCochain S A U V E H N M J u v i r s n hn w (a • z)).v
      j k hjk).val.app W) (tensorComplexSection S A E H q t j hqt W e h)
  rw [pairingCochain_section, pairingCochain_section]
  congr 1
  unfold unsignedEvaluation
  rw [evaluate_smul, evaluate_smul]
  unfold tensorComplexSection
  have hl := SheafOfModules.CochainScalarConstruction.pure_smul_left
    (realizationRing S A) (N.X (r + q)) (M.X (s + t)) W
    ((realizationRingUnit S A).app W a)
    (evaluate S A U E N u r q W w e) (evaluate S A V H M v s t W z h)
  have hr := SheafOfModules.CochainScalarConstruction.pure_smul_right
    (realizationRing S A) (N.X (r + q)) (M.X (s + t)) W
    ((realizationRingUnit S A).app W a)
    (evaluate S A U E N u r q W w e) (evaluate S A V H M v s t W z h)
  exact congrArg (fun x ↦ (J.XIsoOfEq _).hom.val.app W
    ((i.f _).val.app W ((CochainComplex.ιMapBifunctor N M
      (curriedTensor (Modules S A)) _ _ _ rfl).val.app W x))) (hl.trans hr.symm)

attribute [local irreducible] pairingCochain

private def pairingBilinear (r s n : ℤ) (hn : r + s = n) :
    U.X r →+ V.X s →+
      CochainComplex.HomComplex.Cochain (tensorComplex S A E H) J n :=
  AddMonoidHom.mk' (fun w ↦ AddMonoidHom.mk'
    (pairingCochain S A U V E H N M J u v i r s n hn w)
    (pairingCochain_add_right S A U V E H N M J u v i r s n hn w))
    (fun w w' ↦ AddMonoidHom.ext fun z ↦
      pairingCochain_add_left S A U V E H N M J u v i r s n hn w w' z)

private def pairingTensor (r s n : ℤ) (hn : r + s = n) :
    (U.X r ⊗[A] V.X s) →+
      CochainComplex.HomComplex.Cochain (tensorComplex S A E H) J n :=
  TensorProduct.liftAddHom (pairingBilinear S A U V E H N M J u v i r s n hn)
    (pairingCochain_balanced S A U V E H N M J u v i r s n hn)

private def pairingComponent (n : ℤ) :
    ((underlying A).obj (U ⊗ V)).X n ⟶
      (CochainComplex.HomComplex (tensorComplex S A E H) J).X n :=
  Cofan.IsColimit.desc (HomologicalComplex.mapBifunctor.isColimitMapCofan
    (G := forget₂ (ModuleCat A) AddCommGrpCat)
    (F := curriedTensor (ModuleCat A)) U V n)
    (fun x ↦ AddCommGrpCat.ofHom
      (pairingTensor S A U V E H N M J u v i x.1.1 x.1.2 n x.2))

set_option backward.isDefEq.respectTransparency false in
private theorem pairingComponent_pure (r s : ℤ) (w : U.X r) (z : V.X s) :
    pairingComponent S A U V E H N M J u v i (r + s)
      (coefficientTensor A U V r s w z) =
        pairingCochain S A U V E H N M J u v i r s (r + s) rfl w z := by
  have he := Cofan.IsColimit.fac
    (HomologicalComplex.mapBifunctor.isColimitMapCofan
      (G := forget₂ (ModuleCat A) AddCommGrpCat)
      (F := curriedTensor (ModuleCat A)) (c := ComplexShape.up ℤ) U V (r + s))
    (fun x ↦ AddCommGrpCat.ofHom
      (pairingTensor S A U V E H N M J u v i x.1.1 x.1.2 (r + s) x.2))
    ⟨⟨r, s⟩, rfl⟩
  exact ConcreteCategory.congr_hom he (TensorProduct.tmul A w z)

private theorem pairingComponent_pure_at (r s n : ℤ) (hn : r + s = n)
    (w : U.X r) (z : V.X s) :
    pairingComponent S A U V E H N M J u v i n
      ((HomologicalComplex.ιTensorObj U V r s n hn).hom (TensorProduct.tmul A w z)) =
        pairingCochain S A U V E H N M J u v i r s n hn w z := by
  subst n
  exact pairingComponent_pure S A U V E H N M J u v i r s w z

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientTensor_d (R : Type w) [CommRing R] (U V : Coeff R) (r s m : ℤ)
    (hm : (r + s) + 1 = m) (w : U.X r) (z : V.X s) :
    (U ⊗ V).d (r + s) m (coefficientTensor R U V r s w z) =
      (HomologicalComplex.ιTensorObj U V (r + 1) s m (by omega)).hom
          (TensorProduct.tmul R (U.d r (r + 1) w) z) +
        r.negOnePow • (HomologicalComplex.ιTensorObj U V r (s + 1) m (by omega)).hom
          (TensorProduct.tmul R w (V.d s (s + 1) z)) := by
  have hd := congrArg (fun f ↦ f.hom (TensorProduct.tmul R w z))
    (CochainComplex.ιTensorObj_d U V r s (r + s) m rfl hm)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add,
    LinearMap.add_apply, Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply] at hd
  exact hd

set_option backward.isDefEq.respectTransparency false in
private theorem pairingComponent_comm (n m : ℤ) (hnm : n + 1 = m) :
    ((underlying A).obj (U ⊗ V)).d n m ≫
        pairingComponent S A U V E H N M J u v i m =
      pairingComponent S A U V E H N M J u v i n ≫
        (CochainComplex.HomComplex (tensorComplex S A E H) J).d n m := by
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map
    (K₁ := U) (K₂ := V) (F := curriedTensor (ModuleCat.{max u v} A))
    (c := ComplexShape.up ℤ) (forget₂ (ModuleCat A) AddCommGrpCat)
  intro r s hrs
  have hrs' : r + s = n := hrs
  subst n
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul w z =>
    change pairingComponent S A U V E H N M J u v i m
      ((U ⊗ V).d (r + s) m (coefficientTensor A U V r s w z)) =
        CochainComplex.HomComplex.δ (r + s) m
          (pairingComponent S A U V E H N M J u v i (r + s)
            (coefficientTensor A U V r s w z))
    rw [coefficientTensor_d A U V r s m hnm w z, map_add, map_units_smul,
      pairingComponent_pure_at, pairingComponent_pure_at, pairingComponent_pure]
    subst m
    exact (pairingCochain_δ S A U V E H N M J u v i r s w z).symm

private def externalPairing :
    (underlying A).obj (U ⊗ V) ⟶
      CochainComplex.HomComplex (tensorComplex S A E H) J where
  f := pairingComponent S A U V E H N M J u v i
  comm' n m hnm := (pairingComponent_comm S A U V E H N M J u v i n m hnm).symm

set_option backward.isDefEq.respectTransparency false in
private theorem pairingComponent_scalar (n : ℤ) (a : A) :
    (forget₂ (ModuleCat A) AddCommGrpCat).map (a • 𝟙 ((U ⊗ V).X n)) ≫
        pairingComponent S A U V E H N M J u v i n =
      pairingComponent S A U V E H N M J u v i n ≫
        (postcomposeHom (scalarComplex S A J a)).f n := by
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map
    (K₁ := U) (K₂ := V) (F := curriedTensor (ModuleCat.{max u v} A))
    (c := ComplexShape.up ℤ) (forget₂ (ModuleCat A) AddCommGrpCat)
  intro r s hrs
  have hrs' : r + s = n := hrs
  subst n
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul w z =>
    change pairingComponent S A U V E H N M J u v i (r + s)
        (a • coefficientTensor A U V r s w z) = _
    have hs : a • coefficientTensor A U V r s w z =
        coefficientTensor A U V r s (a • w) z := by
      unfold coefficientTensor
      rw [← TensorProduct.smul_tmul']
      exact (((HomologicalComplex.ιTensorObj U V r s (r + s) rfl).hom).map_smul
        a (TensorProduct.tmul A w z)).symm
    rw [hs, pairingComponent_pure]
    change _ = (postcomposeHom (scalarComplex S A J a)).f (r + s)
      (pairingComponent S A U V E H N M J u v i (r + s)
        (coefficientTensor A U V r s w z))
    rw [pairingComponent_pure]
    exact pairingCochain_smul S A U V E H N M J u v i r s (r + s) rfl a w z

set_option backward.isDefEq.respectTransparency false in
private theorem externalPairing_spec :
    IsExternalPairing S A U V E H N M J u v i
      (externalPairing S A U V E H N M J u v i) := by
  constructor
  · intro n a x j k hjk W y
    have hx := ConcreteCategory.congr_hom
      (pairingComponent_scalar S A U V E H N M J u v i n a) x
    change pairingComponent S A U V E H N M J u v i n (a • x) =
      (postcomposeHom (scalarComplex S A J a)).f n
        (pairingComponent S A U V E H N M J u v i n x) at hx
    have hv := CochainComplex.HomComplex.Cochain.congr_v hx j k hjk
    change _ = ((pairingComponent S A U V E H N M J u v i n x).comp
      (CochainComplex.HomComplex.Cochain.ofHom (scalarComplex S A J a))
        (add_zero n)).v j k hjk at hv
    rw [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
      CochainComplex.HomComplex.Cochain.ofHom_v] at hv
    exact congrArg (fun f ↦ f.val.app W y) hv
  · intro r s q t W w z e h
    change ((pairingComponent S A U V E H N M J u v i (r + s)
      (coefficientTensor A U V r s w z)).v _ _ _).val.app W _ = _
    rw [pairingComponent_pure]
    exact pairingCochain_section S A U V E H N M J u v i r s (r + s) rfl
      q t (q + t) ((q + t) + (r + s)) rfl rfl W w z e h

attribute [local irreducible] pairingComponent externalPairing

private def tensorHomShift₁ (E H J : Complex S A) :
    CochainComplex.HomComplex (tensorComplex S A (E⟦(1 : ℤ)⟧) H) J ≅
      (CochainComplex.HomComplex (tensorComplex S A E H) J)⟦(-1 : ℤ)⟧ :=
  precomposeHomIso (tensorShift₁ S A E H 1) J ≪≫ homShiftIso _ J

private def tensorHomShift₂ (E H J : Complex S A) :
    CochainComplex.HomComplex (tensorComplex S A E (H⟦(1 : ℤ)⟧)) J ≅
      (CochainComplex.HomComplex (tensorComplex S A E H) J)⟦(-1 : ℤ)⟧ :=
  precomposeHomIso (tensorShift₂ S A E H 1) J ≪≫ homShiftIso _ J

private theorem tensorSection_units_left (P Q : Modules S A) (W : Cᵒᵖ)
    (a : ℤˣ) (x : P.val.obj W) (y : Q.val.obj W) :
    tensorSection S A P Q W (a • x) y = a • tensorSection S A P Q W x y := by
  rcases Int.units_eq_one_or a with rfl | rfl
  · simp
  · simp only [Units.neg_smul, one_smul]
    change (SheafOfModules.CochainScalarConstruction.pureBilin
      (realizationRing S A) P Q W (-x)) y =
        -((SheafOfModules.CochainScalarConstruction.pureBilin
          (realizationRing S A) P Q W x) y)
    rw [map_neg]
    rfl

private theorem tensorSection_units_right (P Q : Modules S A) (W : Cᵒᵖ)
    (a : ℤˣ) (x : P.val.obj W) (y : Q.val.obj W) :
    tensorSection S A P Q W x (a • y) = a • tensorSection S A P Q W x y := by
  rcases Int.units_eq_one_or a with rfl | rfl
  · simp
  · simp only [Units.neg_smul, one_smul]
    exact (SheafOfModules.CochainScalarConstruction.pureBilin
      (realizationRing S A) P Q W x).map_neg y

private theorem shifted_evaluate (U : Coeff A) (E N : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (η : tensorComplex S A ((constantComplex S A).obj (U⟦(-1 : ℤ)⟧))
      (E⟦(1 : ℤ)⟧) ≅ tensorComplex S A ((constantComplex S A).obj U) E)
    (hη : IsBalancingShift S A U E η) (r q : ℤ) (W : Cᵒᵖ)
    (w : (U⟦(-1 : ℤ)⟧).X r) (e : ((E⟦(1 : ℤ)⟧).X q).val.obj W) :
    evaluate S A (U⟦(-1 : ℤ)⟧) (E⟦(1 : ℤ)⟧) N (η.hom ≫ u) r q W w e =
      r.negOnePow • (u.f (r + q)).val.app W
        (tensorComplexSection S A ((constantComplex S A).obj U) E
          (r + -1) (q + 1) (r + q) (by omega) W
            (constantSection S A (U.X (r + -1)) W w) e) := by
  change (u.f (r + q)).val.app W (_ ) = _
  exact (congrArg ((u.f (r + q)).val.app W) (hη r q W w e)).trans
    (map_units_smul ((u.f (r + q)).val.app W).hom r.negOnePow _)

set_option backward.isDefEq.respectTransparency false in
private theorem unsignedEvaluation_at (r s q t a b k : ℤ)
    (ha : r + q = a) (hb : s + t = b) (hk : a + b = k) (W : Cᵒᵖ)
    (w : U.X r) (z : V.X s) (e : (E.X q).val.obj W) (h : (H.X t).val.obj W) :
    unsignedEvaluation S A U V E H N M J u v i r s q t k (by omega) W w z e h =
      (i.f k).val.app W (tensorComplexSection S A N M a b k hk W
        ((u.f a).val.app W (tensorComplexSection S A ((constantComplex S A).obj U) E
          r q a ha W (constantSection S A (U.X r) W w) e))
        ((v.f b).val.app W (tensorComplexSection S A ((constantComplex S A).obj V) H
          s t b hb W (constantSection S A (V.X s) W z) h))) := by
  subst a b
  have he : CochainComplex.ιMapBifunctor N M (curriedTensor (Modules S A))
      (r + q) (s + t) ((r + q) + (s + t)) rfl ≫
        i.f ((r + q) + (s + t)) ≫ (J.XIsoOfEq hk).hom =
      CochainComplex.ιMapBifunctor N M (curriedTensor (Modules S A))
        (r + q) (s + t) k hk ≫ i.f k := by
    rw [HomologicalComplex.XIsoOfEq_hom_naturality, ← Category.assoc]
    erw [ιTensor_XIso]
  exact congrArg (fun f ↦ f.val.app W (tensorSection S A (N.X (r + q)) (M.X (s + t)) W
    (evaluate S A U E N u r q W w e) (evaluate S A V H M v s t W z h))) he

attribute [local irreducible] unsignedEvaluation

set_option backward.isDefEq.respectTransparency false in
private theorem cochain_section_at (E H J : Complex S A) {n : ℤ}
    (f : CochainComplex.HomComplex.Cochain (tensorComplex S A E H) J n)
    (q t j k : ℤ) (hj : q + t = j) (hk : j + n = k) (W : Cᵒᵖ)
    (e : (E.X q).val.obj W) (h : (H.X t).val.obj W) :
    (f.v j k hk).val.app W (tensorComplexSection S A E H q t j hj W e h) =
      (f.v (q + t) k (by omega)).val.app W
        (tensorComplexSection S A E H q t (q + t) rfl W e h) := by
  subst j
  rfl

private theorem unsignedEvaluation_shift₁ (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J)
    (η : tensorComplex S A ((constantComplex S A).obj (U⟦(-1 : ℤ)⟧))
      (E⟦(1 : ℤ)⟧) ≅ tensorComplex S A ((constantComplex S A).obj U) E)
    (hη : IsBalancingShift S A U E η) (r s q t k : ℤ)
    (hk : (r + q) + (s + t) = k) (W : Cᵒᵖ)
    (w : (U⟦(-1 : ℤ)⟧).X r) (z : V.X s)
    (e : ((E⟦(1 : ℤ)⟧).X q).val.obj W) (h : (H.X t).val.obj W) :
    unsignedEvaluation S A (U⟦(-1 : ℤ)⟧) V (E⟦(1 : ℤ)⟧) H N M J
      (η.hom ≫ u) v i r s q t k hk W w z e h =
      r.negOnePow • unsignedEvaluation S A U V E H N M J u v i
        (r + -1) s (q + 1) t k (by omega) W w z e h := by
  rw [unsignedEvaluation_at S A (U⟦(-1 : ℤ)⟧) V (E⟦(1 : ℤ)⟧) H N M J
    (η.hom ≫ u) v i r s q t (r + q) (s + t) k rfl rfl hk]
  rw [unsignedEvaluation_at S A U V E H N M J u v i
    (r + -1) s (q + 1) t (r + q) (s + t) k (by omega) rfl hk]
  change (i.f k).val.app W (tensorComplexSection S A N M (r + q) (s + t) k hk W
    (evaluate S A (U⟦(-1 : ℤ)⟧) (E⟦(1 : ℤ)⟧) N (η.hom ≫ u) r q W w e)
    (evaluate S A V H M v s t W z h)) = _
  rw [shifted_evaluate S A U E N u η hη]
  unfold tensorComplexSection
  rw [tensorSection_units_left, map_units_smul, map_units_smul]
  rfl

private theorem unsignedEvaluation_shift₂ (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J)
    (η : tensorComplex S A ((constantComplex S A).obj (V⟦(-1 : ℤ)⟧))
      (H⟦(1 : ℤ)⟧) ≅ tensorComplex S A ((constantComplex S A).obj V) H)
    (hη : IsBalancingShift S A V H η) (r s q t k : ℤ)
    (hk : (r + q) + (s + t) = k) (W : Cᵒᵖ)
    (w : U.X r) (z : (V⟦(-1 : ℤ)⟧).X s)
    (e : (E.X q).val.obj W) (h : ((H⟦(1 : ℤ)⟧).X t).val.obj W) :
    unsignedEvaluation S A U (V⟦(-1 : ℤ)⟧) E (H⟦(1 : ℤ)⟧) N M J
      u (η.hom ≫ v) i r s q t k hk W w z e h =
      s.negOnePow • unsignedEvaluation S A U V E H N M J u v i
        r (s + -1) q (t + 1) k (by omega) W w z e h := by
  rw [unsignedEvaluation_at S A U (V⟦(-1 : ℤ)⟧) E (H⟦(1 : ℤ)⟧) N M J
    u (η.hom ≫ v) i r s q t (r + q) (s + t) k rfl rfl hk]
  rw [unsignedEvaluation_at S A U V E H N M J u v i
    r (s + -1) q (t + 1) (r + q) (s + t) k rfl (by omega) hk]
  change (i.f k).val.app W (tensorComplexSection S A N M (r + q) (s + t) k hk W
    (evaluate S A U E N u r q W w e)
    (evaluate S A (V⟦(-1 : ℤ)⟧) (H⟦(1 : ℤ)⟧) M (η.hom ≫ v) s t W z h)) = _
  rw [shifted_evaluate S A V H M v η hη]
  unfold tensorComplexSection
  rw [tensorSection_units_right, map_units_smul, map_units_smul]
  rfl

attribute [local irreducible] evaluate

private theorem pairing_spec_at (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J)
    (p : (underlying A).obj (U ⊗ V) ⟶
      CochainComplex.HomComplex (tensorComplex S A E H) J)
    (hp : IsExternalPairing S A U V E H N M J u v i p)
    (r s q t n j k : ℤ) (hn : r + s = n) (hj : q + t = j) (hk : j + n = k)
    (W : Cᵒᵖ) (w : U.X r) (z : V.X s)
    (e : (E.X q).val.obj W) (h : (H.X t).val.obj W) :
    (((p.f n) ((HomologicalComplex.ιTensorObj U V r s n hn).hom
      (TensorProduct.tmul A w z))).v j k hk).val.app W
        (tensorComplexSection S A E H q t j hj W e h) =
      (s * q).negOnePow • unsignedEvaluation S A U V E H N M J u v i
        r s q t k (by omega) W w z e h := by
  subst n j k
  exact hp.2 r s q t W w z e h

set_option backward.isDefEq.respectTransparency false in
private theorem tensorShift₁_inv_ι (E H : Complex S A) (q t j : ℤ)
    (hj : q + t = j) :
    CochainComplex.ιMapBifunctor E H (curriedTensor (Modules S A))
        (q + 1) t (j + 1) (by omega) ≫ (tensorShift₁ S A E H 1).inv.f j =
      CochainComplex.ιMapBifunctor (E⟦(1 : ℤ)⟧) H (curriedTensor (Modules S A))
        q t j hj := by
  have hh : CochainComplex.ιMapBifunctor (E⟦(1 : ℤ)⟧) H
      (curriedTensor (Modules S A)) q t j hj ≫ (tensorShift₁ S A E H 1).hom.f j =
      CochainComplex.ιMapBifunctor E H (curriedTensor (Modules S A))
        (q + 1) t (j + 1) (by omega) := by
    erw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f E H _ 1 q t j hj
      (q + 1) (j + 1) rfl rfl]
    simp only [CochainComplex.shiftFunctor_obj_X', curriedTensor_obj_obj,
      CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, curriedTensor_map_app, Iso.refl_inv, Category.comp_id]
    erw [id_whiskerRight]
    simp
  rw [← hh, Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
    HomologicalComplex.id_f]
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem tensorShift₂_inv_ι (E H : Complex S A) (q t j : ℤ)
    (hj : q + t = j) :
    CochainComplex.ιMapBifunctor E H (curriedTensor (Modules S A))
        q (t + 1) (j + 1) (by omega) ≫ (tensorShift₂ S A E H 1).inv.f j =
      q.negOnePow • CochainComplex.ιMapBifunctor E (H⟦(1 : ℤ)⟧)
        (curriedTensor (Modules S A)) q t j hj := by
  have hh : CochainComplex.ιMapBifunctor E (H⟦(1 : ℤ)⟧)
      (curriedTensor (Modules S A)) q t j hj ≫ (tensorShift₂ S A E H 1).hom.f j =
      q.negOnePow • CochainComplex.ιMapBifunctor E H (curriedTensor (Modules S A))
        q (t + 1) (j + 1) (by omega) := by
    erw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f E H _ 1 q t j hj
      (t + 1) (j + 1) rfl rfl]
    simp only [CochainComplex.shiftFunctor_obj_X', curriedTensor_obj_obj, mul_one,
      CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, curriedTensor_obj_map, Iso.refl_inv, Category.comp_id,
      smul_left_cancel_iff]
    erw [whiskerLeft_id]
    simp
  have hh' : CochainComplex.ιMapBifunctor E H (curriedTensor (Modules S A))
      q (t + 1) (j + 1) (by omega) = q.negOnePow •
      (CochainComplex.ιMapBifunctor E (H⟦(1 : ℤ)⟧)
        (curriedTensor (Modules S A)) q t j hj ≫ (tensorShift₂ S A E H 1).hom.f j) := by
    rw [hh, smul_smul, Int.units_mul_self, one_smul]
  rw [hh', Linear.units_smul_comp, Category.assoc, ← HomologicalComplex.comp_f,
    Iso.hom_inv_id, HomologicalComplex.id_f]
  erw [Category.comp_id]

private theorem homShiftIso_v (B J : Complex S A) (n j k : ℤ)
    (hk : (j + 1) + (n + -1) = k)
    (f : CochainComplex.HomComplex.Cochain (B⟦(1 : ℤ)⟧) J n) :
    ((homShiftIso B J).hom.f n f).v (j + 1) k hk =
      n.negOnePow • f.v j k (by omega) := by
  change (f.leftUnshift (n + -1) (by omega)).v (j + 1) k hk = _
  rw [CochainComplex.HomComplex.Cochain.leftUnshift_v f (n + -1)
    (by omega) (j + 1) k hk j (by omega)]
  simp only [one_mul, sub_self, mul_zero, Int.zero_ediv, add_zero,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem tensorHomShift₁_section (E H J : Complex S A) (n : ℤ)
    (f : CochainComplex.HomComplex.Cochain (tensorComplex S A (E⟦(1 : ℤ)⟧) H) J n)
    (q t j k : ℤ) (hj : q + t = j) (hk : (j + 1) + (n + -1) = k)
    (W : Cᵒᵖ) (e : (E.X (q + 1)).val.obj W) (h : (H.X t).val.obj W) :
    (((tensorHomShift₁ S A E H J).hom.f n f).v (j + 1) k hk).val.app W
        (tensorComplexSection S A E H (q + 1) t (j + 1) (by omega) W e h) =
      n.negOnePow • (f.v j k (by omega)).val.app W
        (tensorComplexSection S A (E⟦(1 : ℤ)⟧) H q t j hj W e h) := by
  change (((homShiftIso (tensorComplex S A E H) J).hom.f n
    (precomposeCochain S A (tensorShift₁ S A E H 1).inv f)).v (j + 1) k hk).val.app W _ = _
  rw [homShiftIso_v]
  rw [units_smul_app]
  congr 1
  unfold precomposeCochain
  rw [CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  have he := tensorShift₁_inv_ι S A E H q t j hj
  exact congrArg (fun g ↦ (f.v j k (by omega)).val.app W
    (g.val.app W (tensorSection S A (E.X (q + 1)) (H.X t) W e h))) he

set_option backward.isDefEq.respectTransparency false in
private theorem tensorHomShift₂_section (E H J : Complex S A) (n : ℤ)
    (f : CochainComplex.HomComplex.Cochain (tensorComplex S A E (H⟦(1 : ℤ)⟧)) J n)
    (q t j k : ℤ) (hj : q + t = j) (hk : (j + 1) + (n + -1) = k)
    (W : Cᵒᵖ) (e : (E.X q).val.obj W) (h : (H.X (t + 1)).val.obj W) :
    (((tensorHomShift₂ S A E H J).hom.f n f).v (j + 1) k hk).val.app W
        (tensorComplexSection S A E H q (t + 1) (j + 1) (by omega) W e h) =
      (n + q).negOnePow • (f.v j k (by omega)).val.app W
        (tensorComplexSection S A E (H⟦(1 : ℤ)⟧) q t j hj W e h) := by
  change (((homShiftIso (tensorComplex S A E H) J).hom.f n
    (precomposeCochain S A (tensorShift₂ S A E H 1).inv f)).v (j + 1) k hk).val.app W _ = _
  rw [homShiftIso_v]
  rw [units_smul_app]
  unfold precomposeCochain
  rw [CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  have he := tensorShift₂_inv_ι S A E H q t j hj
  have he' := congrArg (fun g ↦ (f.v j k (by omega)).val.app W
    (g.val.app W (tensorSection S A (E.X q) (H.X (t + 1)) W e h))) he
  rw [units_smul_app, map_units_smul] at he'
  change _ = _ at he'
  have hn := congrArg (fun x ↦ n.negOnePow • x) he'
  rw [smul_smul, ← Int.negOnePow_add] at hn
  exact hn

attribute [local irreducible] tensorComplexSection

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientShift₁_pure (R : Type w) [CommRing R] (U V : Coeff R) (r s : ℤ)
    (w : (U⟦(-1 : ℤ)⟧).X r) (z : V.X s) :
    ((coefficientShift₁ R U V (-1)).hom.f (r + s))
        (coefficientTensor R (U⟦(-1 : ℤ)⟧) V r s w z) =
      (HomologicalComplex.ιTensorObj U V (r + -1) s ((r + s) + -1)
        (by omega)).hom (TensorProduct.tmul R w z) := by
  have he : HomologicalComplex.ιTensorObj (U⟦(-1 : ℤ)⟧) V r s (r + s) rfl ≫
      (coefficientShift₁ R U V (-1)).hom.f (r + s) =
      HomologicalComplex.ιTensorObj U V (r + -1) s ((r + s) + -1) (by omega) := by
    erw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f U V _ (-1) r s (r + s) rfl
      (r + -1) ((r + s) + -1) rfl rfl]
    simp only [Int.reduceNeg, CochainComplex.shiftFunctor_obj_X', curriedTensor_obj_obj,
      CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, curriedTensor_map_app, Iso.refl_inv, Category.comp_id]
    erw [id_whiskerRight]
    simp
  exact congrArg (fun f ↦ f.hom (TensorProduct.tmul R w z)) he

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientShift₂_pure (R : Type w) [CommRing R] (U V : Coeff R) (r s : ℤ)
    (w : U.X r) (z : (V⟦(-1 : ℤ)⟧).X s) :
    ((coefficientShift₂ R U V (-1)).hom.f (r + s))
        (coefficientTensor R U (V⟦(-1 : ℤ)⟧) r s w z) =
      r.negOnePow • (HomologicalComplex.ιTensorObj U V r (s + -1) ((r + s) + -1)
        (by omega)).hom (TensorProduct.tmul R w z) := by
  have he : HomologicalComplex.ιTensorObj U (V⟦(-1 : ℤ)⟧) r s (r + s) rfl ≫
      (coefficientShift₂ R U V (-1)).hom.f (r + s) =
      r.negOnePow • HomologicalComplex.ιTensorObj U V r (s + -1) ((r + s) + -1)
        (by omega) := by
    erw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f U V _ (-1) r s (r + s) rfl
      (s + -1) ((r + s) + -1) rfl rfl]
    simp only [Int.reduceNeg, CochainComplex.shiftFunctor_obj_X', curriedTensor_obj_obj,
      mul_neg, mul_one, Int.negOnePow_neg, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, curriedTensor_obj_map,
      Iso.refl_inv, Category.comp_id, smul_left_cancel_iff]
    erw [whiskerLeft_id]
    simp
  have hx := congrArg (fun f ↦ f.hom (TensorProduct.tmul R w z)) he
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply] at hx
  exact hx

set_option backward.isDefEq.respectTransparency false in
private theorem shiftedCoefficient₁_section (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J)
    (p : (underlying A).obj (U ⊗ V) ⟶
      CochainComplex.HomComplex (tensorComplex S A E H) J)
    (hp : IsExternalPairing S A U V E H N M J u v i p) (r s q t k : ℤ)
    (hk : ((q + t) + 1) + ((r + s) + -1) = k) (W : Cᵒᵖ)
    (w : (U⟦(-1 : ℤ)⟧).X r) (z : V.X s)
    (e : ((E⟦(1 : ℤ)⟧).X q).val.obj W) (h : (H.X t).val.obj W) :
    (((((underlying A).map (coefficientShift₁ A U V (-1)).hom ≫
      (((underlying A).commShiftIso (-1)).inv.app (U ⊗ V)) ≫ p⟦(-1 : ℤ)⟧').f
        (r + s)) (coefficientTensor A (U⟦(-1 : ℤ)⟧) V r s w z)).v
          ((q + t) + 1) k hk).val.app W
            (tensorComplexSection S A E H (q + 1) t ((q + t) + 1) (by omega) W e h) =
      (s * q + s).negOnePow • unsignedEvaluation S A U V E H N M J u v i
        (r + -1) s (q + 1) t k (by omega) W w z e h := by
  change (((p.f ((r + s) + -1))
    (((coefficientShift₁ A U V (-1)).hom.f (r + s))
      (coefficientTensor A (U⟦(-1 : ℤ)⟧) V r s w z))).v
        ((q + t) + 1) k hk).val.app W _ = _
  rw [coefficientShift₁_pure A]
  rw [pairing_spec_at S A U V E H N M J u v i p hp
    (r + -1) s (q + 1) t ((r + s) + -1) ((q + t) + 1) k
      (by omega) (by omega) hk]
  rw [show s * (q + 1) = s * q + s by ring]

set_option backward.isDefEq.respectTransparency false in
private theorem shiftedCoefficient₂_section (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J)
    (p : (underlying A).obj (U ⊗ V) ⟶
      CochainComplex.HomComplex (tensorComplex S A E H) J)
    (hp : IsExternalPairing S A U V E H N M J u v i p) (r s q t k : ℤ)
    (hk : ((q + t) + 1) + ((r + s) + -1) = k) (W : Cᵒᵖ)
    (w : U.X r) (z : (V⟦(-1 : ℤ)⟧).X s)
    (e : (E.X q).val.obj W) (h : ((H⟦(1 : ℤ)⟧).X t).val.obj W) :
    (((((underlying A).map (coefficientShift₂ A U V (-1)).hom ≫
      (((underlying A).commShiftIso (-1)).inv.app (U ⊗ V)) ≫ p⟦(-1 : ℤ)⟧').f
        (r + s)) (coefficientTensor A U (V⟦(-1 : ℤ)⟧) r s w z)).v
          ((q + t) + 1) k hk).val.app W
            (tensorComplexSection S A E H q (t + 1) ((q + t) + 1) (by omega) W e h) =
      (s * q + q + r).negOnePow • unsignedEvaluation S A U V E H N M J u v i
        r (s + -1) q (t + 1) k (by omega) W w z e h := by
  change (((p.f ((r + s) + -1))
    (((coefficientShift₂ A U V (-1)).hom.f (r + s))
      (coefficientTensor A U (V⟦(-1 : ℤ)⟧) r s w z))).v
        ((q + t) + 1) k hk).val.app W _ = _
  rw [coefficientShift₂_pure A, map_units_smul,
    CochainComplex.HomComplex.Cochain.units_smul_v, units_smul_app]
  rw [pairing_spec_at S A U V E H N M J u v i p hp
    r (s + -1) q (t + 1) ((r + s) + -1) ((q + t) + 1) k
      (by omega) (by omega) hk, smul_smul]
  congr 1
  rw [← Int.negOnePow_add]
  apply (Int.negOnePow_eq_iff _ _).2
  refine ⟨-q, ?_⟩
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem shiftedPairing₁_section (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J)
    (η : tensorComplex S A ((constantComplex S A).obj (U⟦(-1 : ℤ)⟧))
      (E⟦(1 : ℤ)⟧) ≅ tensorComplex S A ((constantComplex S A).obj U) E)
    (hη : IsBalancingShift S A U E η)
    (pE : (underlying A).obj (U⟦(-1 : ℤ)⟧ ⊗ V) ⟶
      CochainComplex.HomComplex (tensorComplex S A (E⟦(1 : ℤ)⟧) H) J)
    (hpE : IsExternalPairing S A (U⟦(-1 : ℤ)⟧) V (E⟦(1 : ℤ)⟧) H N M J
      (η.hom ≫ u) v i pE) (r s q t k : ℤ)
    (hk : ((q + t) + 1) + ((r + s) + -1) = k) (W : Cᵒᵖ)
    (w : (U⟦(-1 : ℤ)⟧).X r) (z : V.X s)
    (e : ((E⟦(1 : ℤ)⟧).X q).val.obj W) (h : (H.X t).val.obj W) :
    ((((pE ≫ (tensorHomShift₁ S A E H J).hom).f (r + s))
      (coefficientTensor A (U⟦(-1 : ℤ)⟧) V r s w z)).v ((q + t) + 1) k hk).val.app W
        (tensorComplexSection S A E H (q + 1) t ((q + t) + 1) (by omega) W e h) =
      (s * q + s).negOnePow • unsignedEvaluation S A U V E H N M J u v i
        (r + -1) s (q + 1) t k (by omega) W w z e h := by
  change (((tensorHomShift₁ S A E H J).hom.f (r + s)
    ((pE.f (r + s)) (coefficientTensor A (U⟦(-1 : ℤ)⟧) V r s w z))).v
      ((q + t) + 1) k hk).val.app W _ = _
  rw [tensorHomShift₁_section S A E H J (r + s) _ q t (q + t) k rfl hk]
  erw [pairing_spec_at S A (U⟦(-1 : ℤ)⟧) V (E⟦(1 : ℤ)⟧) H N M J
    (η.hom ≫ u) v i pE hpE r s q t (r + s) (q + t) k rfl rfl (by omega)]
  rw [unsignedEvaluation_shift₁ S A U V E H N M J u v i η hη]
  rw [smul_smul, smul_smul]
  congr 1
  rw [← Int.negOnePow_add, ← Int.negOnePow_add]
  apply (Int.negOnePow_eq_iff _ _).2
  refine ⟨r, ?_⟩
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem shiftedPairing₂_section (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J)
    (η : tensorComplex S A ((constantComplex S A).obj (V⟦(-1 : ℤ)⟧))
      (H⟦(1 : ℤ)⟧) ≅ tensorComplex S A ((constantComplex S A).obj V) H)
    (hη : IsBalancingShift S A V H η)
    (pH : (underlying A).obj (U ⊗ V⟦(-1 : ℤ)⟧) ⟶
      CochainComplex.HomComplex (tensorComplex S A E (H⟦(1 : ℤ)⟧)) J)
    (hpH : IsExternalPairing S A U (V⟦(-1 : ℤ)⟧) E (H⟦(1 : ℤ)⟧) N M J
      u (η.hom ≫ v) i pH) (r s q t k : ℤ)
    (hk : ((q + t) + 1) + ((r + s) + -1) = k) (W : Cᵒᵖ)
    (w : U.X r) (z : (V⟦(-1 : ℤ)⟧).X s)
    (e : (E.X q).val.obj W) (h : ((H⟦(1 : ℤ)⟧).X t).val.obj W) :
    ((((pH ≫ (tensorHomShift₂ S A E H J).hom).f (r + s))
      (coefficientTensor A U (V⟦(-1 : ℤ)⟧) r s w z)).v ((q + t) + 1) k hk).val.app W
        (tensorComplexSection S A E H q (t + 1) ((q + t) + 1) (by omega) W e h) =
      (s * q + q + r).negOnePow • unsignedEvaluation S A U V E H N M J u v i
        r (s + -1) q (t + 1) k (by omega) W w z e h := by
  change (((tensorHomShift₂ S A E H J).hom.f (r + s)
    ((pH.f (r + s)) (coefficientTensor A U (V⟦(-1 : ℤ)⟧) r s w z))).v
      ((q + t) + 1) k hk).val.app W _ = _
  rw [tensorHomShift₂_section S A E H J (r + s) _ q t (q + t) k rfl hk]
  erw [pairing_spec_at S A U (V⟦(-1 : ℤ)⟧) E (H⟦(1 : ℤ)⟧) N M J
    u (η.hom ≫ v) i pH hpH r s q t (r + s) (q + t) k rfl rfl (by omega)]
  rw [unsignedEvaluation_shift₂ S A U V E H N M J u v i η hη]
  rw [smul_smul, smul_smul]
  congr 1
  rw [← Int.negOnePow_add, ← Int.negOnePow_add]
  apply (Int.negOnePow_eq_iff _ _).2
  refine ⟨s, ?_⟩
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem shift_square₁ (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J)
    (η : tensorComplex S A ((constantComplex S A).obj (U⟦(-1 : ℤ)⟧))
      (E⟦(1 : ℤ)⟧) ≅ tensorComplex S A ((constantComplex S A).obj U) E)
    (hη : IsBalancingShift S A U E η)
    (p : (underlying A).obj (U ⊗ V) ⟶
      CochainComplex.HomComplex (tensorComplex S A E H) J)
    (hp : IsExternalPairing S A U V E H N M J u v i p)
    (pE : (underlying A).obj (U⟦(-1 : ℤ)⟧ ⊗ V) ⟶
      CochainComplex.HomComplex (tensorComplex S A (E⟦(1 : ℤ)⟧) H) J)
    (hpE : IsExternalPairing S A (U⟦(-1 : ℤ)⟧) V (E⟦(1 : ℤ)⟧) H N M J
      (η.hom ≫ u) v i pE) :
    pE ≫ (tensorHomShift₁ S A E H J).hom =
      (underlying A).map (coefficientShift₁ A U V (-1)).hom ≫
        (((underlying A).commShiftIso (-1)).inv.app (U ⊗ V)) ≫ p⟦(-1 : ℤ)⟧' := by
  apply pairing_hom_ext S A (U⟦(-1 : ℤ)⟧) V E H J (-1)
  intro r s q t W w z e h
  obtain ⟨q, rfl⟩ : ∃ q' : ℤ, q' + 1 = q := ⟨q - 1, by omega⟩
  have he := shiftedPairing₁_section S A U V E H N M J u v i η hη pE hpE
    r s q t (((q + 1) + t) + ((r + s) + -1)) (by omega) W w z e h
  have hc := shiftedCoefficient₁_section S A U V E H N M J u v i p hp
    r s q t (((q + 1) + t) + ((r + s) + -1)) (by omega) W w z e h
  erw [cochain_section_at] at he hc
  exact he.trans hc.symm

set_option backward.isDefEq.respectTransparency false in
private theorem shift_square₂ (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J)
    (η : tensorComplex S A ((constantComplex S A).obj (V⟦(-1 : ℤ)⟧))
      (H⟦(1 : ℤ)⟧) ≅ tensorComplex S A ((constantComplex S A).obj V) H)
    (hη : IsBalancingShift S A V H η)
    (p : (underlying A).obj (U ⊗ V) ⟶
      CochainComplex.HomComplex (tensorComplex S A E H) J)
    (hp : IsExternalPairing S A U V E H N M J u v i p)
    (pH : (underlying A).obj (U ⊗ V⟦(-1 : ℤ)⟧) ⟶
      CochainComplex.HomComplex (tensorComplex S A E (H⟦(1 : ℤ)⟧)) J)
    (hpH : IsExternalPairing S A U (V⟦(-1 : ℤ)⟧) E (H⟦(1 : ℤ)⟧) N M J
      u (η.hom ≫ v) i pH) :
    pH ≫ (tensorHomShift₂ S A E H J).hom =
      (underlying A).map (coefficientShift₂ A U V (-1)).hom ≫
        (((underlying A).commShiftIso (-1)).inv.app (U ⊗ V)) ≫ p⟦(-1 : ℤ)⟧' := by
  apply pairing_hom_ext S A U (V⟦(-1 : ℤ)⟧) E H J (-1)
  intro r s q t W w z e h
  obtain ⟨t, rfl⟩ : ∃ t' : ℤ, t' + 1 = t := ⟨t - 1, by omega⟩
  have he := shiftedPairing₂_section S A U V E H N M J u v i η hη pH hpH
    r s q t ((q + (t + 1)) + ((r + s) + -1)) (by omega) W w z e h
  have hc := shiftedCoefficient₂_section S A U V E H N M J u v i p hp
    r s q t ((q + (t + 1)) + ((r + s) + -1)) (by omega) W w z e h
  erw [cochain_section_at] at he hc
  exact he.trans hc.symm

end PairingData

/-- Both coefficient shift squares for the signed external chain evaluation.

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, Tag 0A90 (lemma-compose),
and lemma-RHom-triangulated; agent two-variable sign calculation from steps 8 and 9
of lem-pur-external-rhom-cone-pairing
(blueprint: lem-pur-external-evaluation-two-shift-squares).

Proof: (1) Extend the displayed balanced local formula through module sheafification
and the direct-sum tensor universal property, taking products of all Hom components.
This also gives an equality test on homogeneous pure tensors (constant module functor,
sheaf tensor, sheafification, total tensor and Hom-complex dependency nodes).
(2) Expand the Hom differential of the external evaluation. The four terms have signs
sq, sq+r, sq+r+q and sq+r+q+s. Subtraction of the two source-differential terms cancels
those differentiating e and h, leaving exactly p(dw,z)+(-1)^r p(w,dz).
(3) The Hom shift sends f to (-1)^n f with its source index reduced by one; expanding
both differentials verifies the chain-map identity and the same sign gives its inverse.
(4) For the balancing comparison, the two shifted differential terms both become
(-1)^r dw tensor e minus w tensor de. The same signed reindexing is its inverse.
(5) The first tensor shift is unsigned; the second carries (-1)^(a*r). Checking the
two differential terms gives chain isomorphisms for a=1 and a=-1. Precomposition with
the inverse coefficient comparison, followed by the Hom shift, gives rho.
(6) In the E square the four signs are sq, r, 0 and r+s, summing to sq+s modulo two.
The right side has sign s(q+1), the same exponent modulo two.
(7) In the H square the signs are sq, s, q and r+s, summing to sq+q+r modulo two.
The right side has r+(s-1)q, again the same exponent. The equality test of (1) proves
both equalities of chain maps. All calculations hold in every integer degree and use
no boundedness, flatness or injectivity. -/
theorem external_evaluation_two_shift_squares
    (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J) :
    ∃ θ : ∀ B : Complex S A,
        CochainComplex.HomComplex (B⟦(1 : ℤ)⟧) J ≅
          (CochainComplex.HomComplex B J)⟦(-1 : ℤ)⟧,
      (∀ B : Complex S A, IsHomShift S A B J (θ B)) ∧
      ∃ (ηU : tensorComplex S A ((constantComplex S A).obj (U⟦(-1 : ℤ)⟧))
          (E⟦(1 : ℤ)⟧) ≅ tensorComplex S A ((constantComplex S A).obj U) E)
        (ηV : tensorComplex S A ((constantComplex S A).obj (V⟦(-1 : ℤ)⟧))
          (H⟦(1 : ℤ)⟧) ≅ tensorComplex S A ((constantComplex S A).obj V) H),
        IsBalancingShift S A U E ηU ∧ IsBalancingShift S A V H ηV ∧
        ∃ (p : (underlying A).obj (U ⊗ V) ⟶
            CochainComplex.HomComplex (tensorComplex S A E H) J)
          (pE : (underlying A).obj (U⟦(-1 : ℤ)⟧ ⊗ V) ⟶
            CochainComplex.HomComplex (tensorComplex S A (E⟦(1 : ℤ)⟧) H) J)
          (pH : (underlying A).obj (U ⊗ V⟦(-1 : ℤ)⟧) ⟶
            CochainComplex.HomComplex (tensorComplex S A E (H⟦(1 : ℤ)⟧)) J)
          (ρE : CochainComplex.HomComplex (tensorComplex S A (E⟦(1 : ℤ)⟧) H) J ≅
            (CochainComplex.HomComplex (tensorComplex S A E H) J)⟦(-1 : ℤ)⟧)
          (ρH : CochainComplex.HomComplex (tensorComplex S A E (H⟦(1 : ℤ)⟧)) J ≅
            (CochainComplex.HomComplex (tensorComplex S A E H) J)⟦(-1 : ℤ)⟧),
          IsExternalPairing S A U V E H N M J u v i p ∧
          IsExternalPairing S A (U⟦(-1 : ℤ)⟧) V (E⟦(1 : ℤ)⟧) H N M J
            (ηU.hom ≫ u) v i pE ∧
          IsExternalPairing S A U (V⟦(-1 : ℤ)⟧) E (H⟦(1 : ℤ)⟧) N M J
            u (ηV.hom ≫ v) i pH ∧
          (∀ (n : ℤ)
            (f : CochainComplex.HomComplex.Cochain
              (tensorComplex S A (E⟦(1 : ℤ)⟧) H) J n),
            (ρE.hom.f n) f = ((θ (tensorComplex S A E H)).hom.f n)
              (precomposeCochain S A (tensorShift₁ S A E H 1).inv f)) ∧
          (∀ (n : ℤ)
            (f : CochainComplex.HomComplex.Cochain
              (tensorComplex S A E (H⟦(1 : ℤ)⟧)) J n),
            (ρH.hom.f n) f = ((θ (tensorComplex S A E H)).hom.f n)
              (precomposeCochain S A (tensorShift₂ S A E H 1).inv f)) ∧
          pE ≫ ρE.hom =
            (underlying A).map (coefficientShift₁ A U V (-1)).hom ≫
              (((underlying A).commShiftIso (-1)).inv.app (U ⊗ V)) ≫ p⟦(-1 : ℤ)⟧' ∧
          pH ≫ ρH.hom =
            (underlying A).map (coefficientShift₂ A U V (-1)).hom ≫
              (((underlying A).commShiftIso (-1)).inv.app (U ⊗ V)) ≫ p⟦(-1 : ℤ)⟧' ∧
          (∀ (r s q t : ℤ) (W : Cᵒᵖ) (w : (U⟦(-1 : ℤ)⟧).X r) (z : V.X s)
            (e : ((E⟦(1 : ℤ)⟧).X q).val.obj W) (h : (H.X t).val.obj W),
            ((((((pE ≫ ρE.hom).f (r + s))
              (coefficientTensor A (U⟦(-1 : ℤ)⟧) V r s w z)).v
                ((q + t) + 1) (((q + t) + 1) + ((r + s) + -1)) rfl).val.app W)
                  (tensorComplexSection S A E H (q + 1) t ((q + t) + 1)
                    (by omega) W e h)) =
              (s * q + s).negOnePow • unsignedEvaluation S A U V E H N M J u v i
                (r + -1) s (q + 1) t (((q + t) + 1) + ((r + s) + -1))
                (by omega) W w z e h) ∧
          (∀ (r s q t : ℤ) (W : Cᵒᵖ) (w : U.X r) (z : (V⟦(-1 : ℤ)⟧).X s)
            (e : (E.X q).val.obj W) (h : ((H⟦(1 : ℤ)⟧).X t).val.obj W),
            ((((((pH ≫ ρH.hom).f (r + s))
              (coefficientTensor A U (V⟦(-1 : ℤ)⟧) r s w z)).v
                ((q + t) + 1) (((q + t) + 1) + ((r + s) + -1)) rfl).val.app W)
                  (tensorComplexSection S A E H q (t + 1) ((q + t) + 1)
                    (by omega) W e h)) =
              (s * q + q + r).negOnePow • unsignedEvaluation S A U V E H N M J u v i
                r (s + -1) q (t + 1) (((q + t) + 1) + ((r + s) + -1))
                (by omega) W w z e h) := by
  let ηU := balancingIso S A U E
  let ηV := balancingIso S A V H
  let p := externalPairing S A U V E H N M J u v i
  let pE := externalPairing S A (U⟦(-1 : ℤ)⟧) V (E⟦(1 : ℤ)⟧) H N M J
    (ηU.hom ≫ u) v i
  let pH := externalPairing S A U (V⟦(-1 : ℤ)⟧) E (H⟦(1 : ℤ)⟧) N M J
    u (ηV.hom ≫ v) i
  have hp : IsExternalPairing S A U V E H N M J u v i p :=
    externalPairing_spec S A U V E H N M J u v i
  have hpE : IsExternalPairing S A (U⟦(-1 : ℤ)⟧) V (E⟦(1 : ℤ)⟧) H N M J
      (ηU.hom ≫ u) v i pE :=
    externalPairing_spec S A (U⟦(-1 : ℤ)⟧) V (E⟦(1 : ℤ)⟧) H N M J
      (ηU.hom ≫ u) v i
  have hpH : IsExternalPairing S A U (V⟦(-1 : ℤ)⟧) E (H⟦(1 : ℤ)⟧) N M J
      u (ηV.hom ≫ v) i pH :=
    externalPairing_spec S A U (V⟦(-1 : ℤ)⟧) E (H⟦(1 : ℤ)⟧) N M J
      u (ηV.hom ≫ v) i
  refine ⟨fun B ↦ homShiftIso B J, fun B ↦ homShiftIso_spec S A B J,
    ηU, ηV, balancingIso_spec S A U E, balancingIso_spec S A V H,
    p, pE, pH, tensorHomShift₁ S A E H J, tensorHomShift₂ S A E H J,
    hp, hpE, hpH, (fun n f ↦ rfl), (fun n f ↦ rfl), ?_, ?_, ?_, ?_⟩
  · exact shift_square₁ S A U V E H N M J u v i
      ηU (balancingIso_spec S A U E) p hp pE hpE
  · exact shift_square₂ S A U V E H N M J u v i
      ηV (balancingIso_spec S A V H) p hp pH hpH
  · intro r s q t W w z e h
    exact shiftedPairing₁_section S A U V E H N M J u v i
      ηU (balancingIso_spec S A U E) pE hpE r s q t _ rfl W w z e h
  · intro r s q t W w z e h
    exact shiftedPairing₂_section S A U V E H N M J u v i
      ηV (balancingIso_spec S A V H) pH hpH r s q t _ rfl W w z e h

end CategoryTheory.ExternalEvaluation
