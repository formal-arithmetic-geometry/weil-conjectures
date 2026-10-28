/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.FiniteTensorReductionData
public import Sheaf.Paper.FiniteTensorComparisonEquations
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Sheaf.Paper.FiniteReductionRootCharts
public import Sheaf.Paper.FiniteReductionComparisons
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.FiniteCoefficientReductionFlatModel
public import Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin
public import Sheaf.Paper.SupportedCup
public import Sheaf.Paper.OrientationFiniteCoefficientTwists
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal
public import Sheaf.Paper.FiniteScalarTensorData
import Sheaf.Paper.FiniteScalarMonoidalRepresentative
import Sheaf.Paper.FiniteScalarTensorSource
import Sheaf.Paper.FiniteTensorSemilinearReduction
import Sheaf.Paper.FiniteTensorLineDerivedExistence


/-! # Finite reduction of signed twists and tensor presentations

Source: main-20261015, thm-pur-finite-reduction-of-purity, proof Step 2;
Stacks Tags 07A4, 0FPT, 0FNH, 03EK and 03EM.
(blueprint: def-pur-finite-signed-reduction-comparisons)

## Main declarations

- `finiteTensorCore`
- `finiteTensorLineComparison`
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w uA vA uB vB wA wB
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] finiteTensorAdjunction finiteTensorFixedLineMap
  Functor.leftAdjoint Adjunction.ofIsRightAdjoint
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Full scalar-first tensor-counit normalization on K-flat representatives.
Source: blueprint proof Step 2, Stacks 07A4 and 0FPT
(blueprint: def-pur-finite-signed-reduction-comparisons). -/
def FiniteTensorCoreNormalized (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u})
    (h : (P.finiteTensorReduction m hm hmn T).CoreMonoidal) : Prop :=
  (finiteScalarTensorData
    (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1} T).Normalized h

private theorem core_ext_tensor
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} (m n : F.CoreMonoidal)
    (ht : ∀ X Y, m.μIso X Y = n.μIso X Y) : m = n := by
  have hew : m.εIso.hom ▷ F.obj (𝟙_ C) = n.εIso.hom ▷ F.obj (𝟙_ C) := by
    apply (cancel_mono ((n.μIso (𝟙_ C) (𝟙_ C)).hom ≫ F.map (λ_ (𝟙_ C)).hom)).1
    simpa only [Category.assoc, ← ht] using
      (m.left_unitality (𝟙_ C)).symm.trans (n.left_unitality (𝟙_ C))
  have hew' : m.εIso.hom ▷ (𝟙_ D) = n.εIso.hom ▷ (𝟙_ D) := by
    apply (cancel_mono ((F.obj (𝟙_ C)) ◁ n.εIso.hom)).1
    rw [← whisker_exchange, ← whisker_exchange, hew]
  have heh : m.εIso.hom = n.εIso.hom := by
    apply (cancel_epi (ρ_ (𝟙_ D)).hom).1
    simpa only [rightUnitor_naturality] using
      congrArg (fun a ↦ a ≫ (ρ_ (F.obj (𝟙_ C))).hom) hew'
  have he : m.εIso = n.εIso := Iso.ext heh
  have ht' : m.μIso = n.μIso := funext (fun X ↦ funext (ht X))
  cases m
  cases n
  cases he
  cases ht'
  rfl

private theorem core_ext_representatives
    {C D K : Type*} [Category* C] [Category* D] [Category* K]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} (m n : F.CoreMonoidal) (R : K ⥤ C) (S : K → Prop)
    (hR : ∀ X, ∃ a, S a ∧ Nonempty (R.obj a ≅ X))
    (ht : ∀ a b, S a → S b → m.μIso (R.obj a) (R.obj b) =
      n.μIso (R.obj a) (R.obj b)) : m = n := by
  apply core_ext_tensor m n
  intro X Y
  obtain ⟨a, ha, ⟨e⟩⟩ := hR X
  obtain ⟨b, hb, ⟨f⟩⟩ := hR Y
  apply Iso.ext
  apply (cancel_epi (F.map e.hom ⊗ₘ F.map f.hom)).1
  have hn (c : F.CoreMonoidal) :
      (F.map e.hom ⊗ₘ F.map f.hom) ≫ (c.μIso X Y).hom =
        (c.μIso (R.obj a) (R.obj b)).hom ≫ F.map (e.hom ⊗ₘ f.hom) := by
    let _ := c.toMonoidal
    exact Functor.LaxMonoidal.μ_natural F e.hom f.hom
  rw [hn m, hn n, ht a b ha hb]

private theorem existsUnique_core_of_source_tail
    {C D K L : Type*} [Category* C] [Category* D] [Category* K] [Category* L]
    [MonoidalCategory C] [MonoidalCategory D]
    {Q : C ⥤ D} {R : K ⥤ C} {QB : L ⥤ D} {S : K → Prop}
    (d : TensorRepresentativeData Q R QB S) (n : Q.CoreMonoidal)
    (hR : ∀ X, ∃ a, S a ∧ Nonempty (R.obj a ≅ X))
    (hs : ∀ X Y, S X → S Y → IsIso (d.source X Y))
    (hn : d.Normalized n) : ∃! h : Q.CoreMonoidal, d.Normalized h := by
  refine ⟨n, hn, ?_⟩
  intro h hh
  apply core_ext_representatives h n R S hR
  intro X Y hX hY
  apply Iso.ext_inv
  have := hs X Y hX hY
  have ht : d.tail X Y = (n.μIso _ _).hom ≫ d.source X Y := by
    rw [hn X Y hX hY, Iso.hom_inv_id_assoc]
  have : IsIso (d.tail X Y) := by
    rw [ht]
    infer_instance
  apply (cancel_mono (d.tail X Y)).1
  exact (hh X Y hX hY).symm.trans (hn X Y hX hY)

private theorem cochain_kFlat_density
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{w} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [MonoidalClosed A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
    [HasColimitsOfSize.{0, 0} A]
    (X : _root_.DerivedCategory A) :
    ∃ C, (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C ∧
      Nonempty (_root_.DerivedCategory.Q.obj C ≅ X) := by
  have : HasExactColimitsOfShape ℤ A :=
    HasExactColimitsOfShape.of_domain_equivalence _ (AsSmall.equiv (C := ℤ)).symm
  obtain ⟨K, hK, ⟨e⟩⟩ := _root_.DerivedCategory.exists_kFlat_iso X
  obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  exact ⟨C, (HomotopyCategory.kFlat_quotient_obj_iff C).1 hK,
    ⟨((_root_.DerivedCategory.quotientCompQhIso _).app C).symm ≪≫ e⟩⟩

private theorem existsUnique_scalarCore
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    ∃! h : (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).CoreMonoidal,
      (finiteScalarTensorData φ T).Normalized h := by
  exact existsUnique_core_of_source_tail (finiteScalarTensorData φ T)
    (finiteScalarMonoidalModel φ T) cochain_kFlat_density
    (finiteScalarTensorData_source_isIso φ T)
    (fun C D _ _ ↦ finiteScalarMonoidalModel_representative φ T C D)

/-- The representative-normalized tensor structure is unique.
Source: blueprint proof Step 2, Stacks 07A4 and 0FPT
(blueprint: def-pur-finite-signed-reduction-comparisons).
Proof: resolve both inputs by flat-term K-flat complexes. Scalar extension preserves
these resolutions and its ordinary scalar-first tensor map is invertible. The
localization universal property descends that map uniquely. The ordinary unit,
associator and symmetry equations give the monoidal axioms after descent. -/
theorem existsUnique_finiteTensorCore (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    ∃! h : (P.finiteTensorReduction m hm hmn T).CoreMonoidal,
      P.FiniteTensorCoreNormalized m hm hmn T h := by
  exact existsUnique_scalarCore (A := P.Coefficient)
    (B := (P.finiteReductionSetting m hm).Coefficient)
    (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1} T

/-- Canonical derived tensor structure, determined by its K-flat representative formula.
Source: blueprint proof Step 2
(blueprint: def-pur-finite-signed-reduction-comparisons). -/
def finiteTensorCore (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    (P.finiteTensorReduction m hm hmn T).CoreMonoidal :=
  (P.existsUnique_finiteTensorCore m hm hmn T).choose

attribute [local irreducible] finiteTensorCore

private theorem existsUnique_family {ι : Type*} {B : ι → Type*}
    (p : ∀ r, B r → Prop) (h : ∀ r, ∃! b, p r b) :
    ∃! b : ∀ r, B r, ∀ r, p r (b r) := by
  classical
  refine ⟨fun r ↦ (h r).choose, fun r ↦ (h r).choose_spec.1, ?_⟩
  intro b hb
  funext r
  exact (h r).choose_spec.2 (b r) (hb r)

private theorem existsUnique_with_family
    {A : Type*} {ι : Type*} {B : ι → Type*}
    (p : A → Prop) (q : A → ∀ r : ι, B r → Prop)
    (h : ∃! a, p a) (g : ∀ a, p a → ∀ r, ∃! b, q a r b) :
    ∃! a, p a ∧ ∃! b : ∀ r, B r, ∀ r, q a r (b r) := by
  obtain ⟨a, ha, hau⟩ := h
  refine ⟨a, ⟨ha, existsUnique_family _ (g a ha)⟩, ?_⟩
  intro a' ha'
  exact hau a' ha'.1

private theorem existsUnique_transposed_lines
    {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
    {F : C ⥤ D} {G : D ⥤ C} {A : Type*} {ι : Type*} {X : ι → C} {Y : ι → D}
    (d : TransposedFamilyData F G X Y A) (p : A → Prop) (hp : ∃! a, p a)
    (hb : ∀ a, p a → ∀ i, ∃! b : F.obj (X i) ≅ Y i, d.Pointwise a i b) :
    ∃! a, p a ∧ ∃! b : ∀ i, F.obj (X i) ≅ Y i, d.Normalized a b := by
  exact existsUnique_with_family p _ hp hb

/-- The signed line comparisons are fixed by integral balancing and dual evaluation.
Source: blueprint proof Steps 3--5, Stacks 03EK, 04TT and 03EM
(blueprint: def-pur-finite-signed-reduction-comparisons).
Proof: in degree one associate the two scalar tensors of the integral line; in
degree zero use the scalar unit. Recurse on positive powers with the normalized
tensor comparison. For negative powers use the base-change isomorphism of the
internal dual of an invertible sheaf and its evaluation formula. Local rank-one
bases give uniqueness of all semilinear maps. Adjoint transposition on single
complexes then gives unique derived isomorphisms, since the lines are flat. -/
theorem existsUnique_finiteTensorLines (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] :
    ∃! c : P.FiniteTensorLineMaps m hm hmn T,
      P.FiniteTensorLineMapsNormalized m hm hmn T c ∧
        ∃! b : ∀ r : ℤ, (P.finiteTensorReduction m hm hmn T).obj
            (P.finiteTensorFixedLine T r) ≅
          (P.finiteReductionSetting m hm).finiteTensorFixedLine T r,
          P.FiniteTensorLineComparisonNormalized m hm hmn T c b := by
  exact existsUnique_transposed_lines (P.finiteTensorLineComparisonData m hm hmn T)
    (P.FiniteTensorLineMapsNormalized m hm hmn T)
    (P.existsUnique_finiteTensorSemilinearReduction m hm hmn T)
    (fun c hc r ↦ P.existsUnique_finiteTensorLineDerivedComparison m hm hmn T c hc r)

/-- The prescribed semilinear reduction of every signed line.
Source: blueprint proof Steps 3--5
(blueprint: def-pur-finite-signed-reduction-comparisons). -/
def finiteTensorLineMaps (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] :=
  (P.existsUnique_finiteTensorLines m hm hmn T).choose

/-- The derived line isomorphism specified by its ordinary adjoint transpose.
Source: blueprint proof Steps 3--5
(blueprint: def-pur-finite-signed-reduction-comparisons). -/
def finiteTensorLineComparison (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (r : ℤ) :
    (P.finiteTensorReduction m hm hmn T).obj (P.finiteTensorFixedLine T r) ≅
      (P.finiteReductionSetting m hm).finiteTensorFixedLine T r :=
  (((P.existsUnique_finiteTensorLines m hm hmn T).choose_spec.1).2).choose r



attribute [local irreducible] finiteTensorLineMaps finiteTensorLineComparison

/-- Twist means tensor with the prescribed signed degree-zero coefficient object.
Source: def-coefficient-twists-detailed
(blueprint: def-pur-finite-signed-reduction-comparisons). -/
def finiteTensorTwist (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r : ℤ) :
    _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) ⥤
      _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) :=
  tensorRight (P.finiteTensorFixedLine T r)

/-- The shared type of the canonical natural signed-twist/shift comparison.
Source: blueprint proof Step 6
(blueprint: def-pur-finite-signed-reduction-comparisons). -/
def FiniteTensorTwistShiftType (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) (r s : ℤ) :=
  P.finiteTensorTwist T r ⋙ shiftFunctor _ s ⋙ P.finiteTensorReduction m hm hmn T ≅
    P.finiteTensorReduction m hm hmn T ⋙
      (P.finiteReductionSetting m hm).finiteTensorTwist T r ⋙ shiftFunctor _ s

/-- The exact component normalization, shared as a predicate before extracting its map.
Source: blueprint proof Steps 2--6
(blueprint: def-pur-finite-signed-reduction-comparisons). -/
def FiniteTensorTwistShiftNormalized (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (r s : ℤ)
    (e : P.FiniteTensorTwistShiftType m hm hmn T r s) : Prop :=
  ∀ K, HEq (e.app K)
        (finiteTensorTwistShiftComponent (P.finiteTensorReduction m hm hmn T)
          (P.finiteTensorCore m hm hmn T) K (P.finiteTensorFixedLine T r)
          ((P.finiteReductionSetting m hm).finiteTensorFixedLine T r)
          (P.finiteTensorLineComparison m hm hmn T r) s
          ((P.finiteTensorScalarShift m hm hmn T s).app (K ⊗ P.finiteTensorFixedLine T r)))

private theorem exists_twistShift
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) (h : F.CoreMonoidal) (A : C) (B : D) (b : F.obj A ≅ B)
    (s : ℤ) (σ : shiftFunctor C s ⋙ F ≅ F ⋙ shiftFunctor D s) :
    ∃ e : tensorRight A ⋙ shiftFunctor C s ⋙ F ≅
        F ⋙ tensorRight B ⋙ shiftFunctor D s,
      ∀ K, e.app K = finiteTensorTwistShiftComponent F h K A B b s (σ.app (K ⊗ A)) := by
  let _ := h.toMonoidal
  have hδ (X Y : C) : Functor.OplaxMonoidal.δ F X Y = (h.μIso X Y).inv := rfl
  let t : tensorRight A ⋙ F ≅ F ⋙ tensorRight B :=
    (Functor.Monoidal.commTensorRight F A).symm ≪≫
      Functor.isoWhiskerLeft F ((tensoringRight D).mapIso b)
  let e : tensorRight A ⋙ shiftFunctor C s ⋙ F ≅
      F ⋙ tensorRight B ⋙ shiftFunctor D s :=
    Functor.isoWhiskerLeft (tensorRight A) σ ≪≫
      (Functor.associator (tensorRight A) F (shiftFunctor D s)).symm ≪≫
      Functor.isoWhiskerRight t (shiftFunctor D s) ≪≫
      Functor.associator F (tensorRight B) (shiftFunctor D s)
  refine ⟨e, ?_⟩
  intro K
  apply Iso.ext
  simp [e, t, finiteTensorTwistShiftComponent, Functor.Monoidal.commTensorRight,
    Functor.Monoidal.μIso, hδ, MonoidalCategory.tensorHom_def]

/-- The prescribed scalar-shift/tensor/line components determine one natural isomorphism.
Source: blueprint proof Steps 2--6
(blueprint: def-pur-finite-signed-reduction-comparisons).
Proof: the scalar-shift comparison is natural, as is the binary tensorator.
Tensor its inverse with the fixed signed-line comparison and apply the shift
functor. The resulting invertible components are natural in the variable object.
The component formula fixes the resulting natural transformation uniquely. -/
theorem existsUnique_finiteTensorTwistShiftComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (r s : ℤ) :
    ∃! e : P.FiniteTensorTwistShiftType m hm hmn T r s,
      P.FiniteTensorTwistShiftNormalized m hm hmn T r s e := by
  obtain ⟨e, he⟩ := exists_twistShift (P.finiteTensorReduction m hm hmn T)
    (P.finiteTensorCore m hm hmn T) (P.finiteTensorFixedLine T r)
    ((P.finiteReductionSetting m hm).finiteTensorFixedLine T r)
    (P.finiteTensorLineComparison m hm hmn T r) s
    (P.finiteTensorScalarShift m hm hmn T s)
  have hn : P.FiniteTensorTwistShiftNormalized m hm hmn T r s e :=
    fun K ↦ heq_of_eq (he K)
  refine ⟨e, hn, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact congrArg Iso.hom ((eq_of_heq (he' K)).trans (eq_of_heq (hn K)).symm)

/-- Canonical natural signed-twist and shift comparison with the prescribed components.
Source: blueprint proof Steps 2--6
(blueprint: def-pur-finite-signed-reduction-comparisons). -/
def finiteTensorTwistShiftComparison (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (r s : ℤ) :
    P.FiniteTensorTwistShiftType m hm hmn T r s :=
  (P.existsUnique_finiteTensorTwistShiftComparison m hm hmn T r s).exists.choose

end WeilConjectures.PurityFiniteSetting
