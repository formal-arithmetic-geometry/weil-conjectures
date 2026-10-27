/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated

/-! # Regrouping relative external powers

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 0G7E and 0D6D;
blueprint sk-prop-an, Proof Steps 3--4
(blueprint: lem-pur-relative-external-power-regrouping).

The index j represents j+1 factors. Every tensor is left associated and nonempty.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RelativeExternalPower

/-- The existing native derived tensor, with its existing flat K-flat normalization.
Source: Stacks 07A4 (blueprint: lem-pur-relative-external-power-regrouping). -/
def tensorModel (Y : Scheme.{u}) (A : Type u) [CommRing A] :
    ProEtaleTensorModel Y (proEtaleConstantRing Y A) where
  tensor := @MonoidalCategory.tensor _ _
    (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2}
      (ProEt.topology Y) (proEtaleConstantRing Y A))
  representative := NatIso.ofComponents
    (fun P ↦ RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
      (ProEt.topology Y) (proEtaleConstantRing Y A)
      P.1.obj P.2.obj (Or.inl P.1.property.1))
    (fun f ↦ RingedDerivedNative.tensorIso_naturality.{u + 1, u, 0, u + 2}
      (ProEt.topology Y) (proEtaleConstantRing Y A) _ _ _ _ _ _ f.1.hom f.2.hom)

/-- Left-iterated fibre products of the first j+1 factors, as schemes over B.
Source: blueprint sk-prop-an, Steps 3--4
(blueprint: lem-pur-relative-external-power-regrouping). -/
def product {B : Scheme.{u}} (X : ℕ → Over B) : ℕ → Over B
  | 0 => X 0
  | j + 1 => Over.mk (pullback.fst (product X j).hom (X (j + 1)).hom ≫ (product X j).hom)

/-- The first projection in the next relative product.
Source: blueprint sk-prop-an (blueprint: lem-pur-relative-external-power-regrouping). -/
abbrev fst {B : Scheme.{u}} (X : ℕ → Over B) (j : ℕ) :
    (product X (j + 1)).left ⟶ (product X j).left :=
  pullback.fst (product X j).hom (X (j + 1)).hom

/-- The last-factor projection in the next relative product.
Source: blueprint sk-prop-an (blueprint: lem-pur-relative-external-power-regrouping). -/
abbrev snd {B : Scheme.{u}} (X : ℕ → Over B) (j : ℕ) :
    (product X (j + 1)).left ⟶ (X (j + 1)).left :=
  pullback.snd (product X j).hom (X (j + 1)).hom

/-- All coordinate projections, with the identity at one factor.
Source: blueprint sk-prop-an (blueprint: lem-pur-relative-external-power-regrouping). -/
def projection {B : Scheme.{u}} (X : ℕ → Over B) :
    (j : ℕ) → (i : Fin (j + 1)) → (product X j).left ⟶ (X i.val).left
  | 0, i => Fin.cases (𝟙 (X 0).left) (fun k ↦ Fin.elim0 k) i
  | j + 1, i => Fin.lastCases (snd X j) (fun k ↦ fst X j ≫ projection X j k) i

/-- A nonempty left-associated tensor of j+1 objects, in the recorded native tensor.
Source: Stacks 07A4 (blueprint: lem-pur-relative-external-power-regrouping). -/
def tensorPrefix (Y : Scheme.{u}) (A : Type u) [CommRing A] :
    (j : ℕ) → (Fin (j + 1) → proEtaleDerivedCategory Y A) → proEtaleDerivedCategory Y A
  | 0, L => L 0
  | j + 1, L => (tensorModel Y A).tensor.obj
      (tensorPrefix Y A j (fun i ↦ L i.castSucc), L (Fin.last (j + 1)))

/-- Tensor a family of isomorphisms in the same fixed left association.
Source: Stacks 0FPT (blueprint: lem-pur-relative-external-power-regrouping). -/
def tensorPrefixIso (Y : Scheme.{u}) (A : Type u) [CommRing A] :
    (j : ℕ) → {L M : Fin (j + 1) → proEtaleDerivedCategory Y A} →
      (∀ i, L i ≅ M i) → (tensorPrefix Y A j L ≅ tensorPrefix Y A j M)
  | 0, _, _, e => e 0
  | j + 1, _, _, e => (tensorModel Y A).tensor.mapIso
      ((tensorPrefixIso Y A j (fun i ↦ e i.castSucc)).prod (e (Fin.last (j + 1))))

/-- Distribute pullback across the prefix using exactly the canonical binary comparisons.
Source: Stacks 07A4 (blueprint: lem-pur-relative-external-power-regrouping). -/
def pullbackPrefix {Z Y : Scheme.{u}} (A : Type u) [CommRing A] (a : Z ⟶ Y) :
    (j : ℕ) → (L : Fin (j + 1) → proEtaleDerivedCategory Y A) →
      (proEtaleConstantRingDerivedPullback A a).obj (tensorPrefix Y A j L) ≅
        tensorPrefix Z A j (fun i ↦ (proEtaleConstantRingDerivedPullback A a).obj (L i))
  | 0, _ => Iso.refl _
  | j + 1, L =>
      (proEtaleCanonicalTensorComparison a (proEtaleConstantRing Y A)
        (proEtaleConstantRing Z A) (proEtaleConstantRingComparison a A)
        (tensorModel Y A) (tensorModel Z A)).app
          (tensorPrefix Y A j (fun i ↦ L i.castSucc), L (Fin.last (j + 1))) ≪≫
      (tensorModel Z A).tensor.mapIso
        ((pullbackPrefix A a j (fun i ↦ L i.castSucc)).prod (Iso.refl _))

/-- The external tensor on a specified prefix of coordinate maps.
Source: blueprint sk-prop-an (blueprint: lem-pur-relative-external-power-regrouping). -/
def externalAt {B : Scheme.{u}} (X : ℕ → Over B) (A : Type u) [CommRing A]
    (K : ∀ i : ℕ, proEtaleDerivedCategory (X i).left A)
    (j : ℕ) (Y : Scheme.{u}) (p : ∀ i : Fin (j + 1), Y ⟶ (X i.val).left) :
    proEtaleDerivedCategory Y A :=
  tensorPrefix Y A j (fun i ↦ (proEtaleConstantRingDerivedPullback A (p i)).obj (K i.val))

/-- The object T_(j+1), using the actual projections of the chosen iterated fibre product.
Source: blueprint sk-prop-an (blueprint: lem-pur-relative-external-power-regrouping). -/
def external {B : Scheme.{u}} (X : ℕ → Over B) (A : Type u) [CommRing A]
    (K : ∀ i : ℕ, proEtaleDerivedCategory (X i).left A) (j : ℕ) :
    proEtaleDerivedCategory (product X j).left A :=
  externalAt X A K j (product X j).left (projection X j)

/-- The distribution followed by each canonical pullback compositor.
Source: Stacks 07A4, 0D6D (blueprint: lem-pur-relative-external-power-regrouping). -/
def externalPullback {B : Scheme.{u}} (X : ℕ → Over B) (A : Type u) [CommRing A]
    (K : ∀ i : ℕ, proEtaleDerivedCategory (X i).left A)
    (j : ℕ) {Z Y : Scheme.{u}} (a : Z ⟶ Y)
    (p : ∀ i : Fin (j + 1), Y ⟶ (X i.val).left) :
    (proEtaleConstantRingDerivedPullback A a).obj (externalAt X A K j Y p) ≅
      externalAt X A K j Z (fun i ↦ a ≫ p i) :=
  pullbackPrefix A a j _ ≪≫ tensorPrefixIso Z A j
    (fun i ↦ (proEtaleConstantRingPullbackComposition a (p i) A).app (K i.val))

/-- The prescribed regrouping rho: distribute, compose coordinate pullbacks, tensor identity.
With the fixed left association its target is literally the next external product.
Source: Stacks 07A4, 0D6D, 0FPT
(blueprint: lem-pur-relative-external-power-regrouping). -/
def regroup {B : Scheme.{u}} (X : ℕ → Over B) (A : Type u) [CommRing A]
    (K : ∀ i : ℕ, proEtaleDerivedCategory (X i).left A) (j : ℕ) :
    (tensorModel (product X (j + 1)).left A).tensor.obj
      ((proEtaleConstantRingDerivedPullback A (fst X j)).obj (external X A K j),
        (proEtaleConstantRingDerivedPullback A (snd X j)).obj (K (j + 1))) ≅
      external X A K (j + 1) := by
  simpa only [external, externalAt, tensorPrefix, projection, Fin.lastCases_castSucc,
    Fin.lastCases_last, Fin.val_castSucc, Fin.val_last] using
    (tensorModel (product X (j + 1)).left A).tensor.mapIso
      ((externalPullback X A K j (fst X j) (projection X j)).prod (Iso.refl
        ((proEtaleConstantRingDerivedPullback A (snd X j)).obj (K (j + 1)))))

private theorem ctf_of_iso (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    {K L : proEtaleDerivedCategory Y P.Ring} (e : K ≅ L)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y L := by
  let : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension P.level
        P.level_pos Y) := (proEtale_bounded_constructible_isTriangulated Y P.Ring).1
  refine ⟨ObjectProperty.prop_of_iso _ e hK.1, ?_⟩
  obtain ⟨a, b, ht⟩ := hK.2
  refine ⟨a, b, ht.1, ?_⟩
  intro M Q hM f hf hQ N i hi
  exact ht.2 M Q (hM.map (fun j ↦ j ≪≫ e.symm)) f hf hQ N i hi

private theorem ctf_pullback (P : PurityFiniteSetting.{u})
    {Z Y : Scheme.{u}} (aZ : Z ⟶ Spec (.of P.field.k))
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : Z ⟶ Y) (hf : f ≫ aY = aZ)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (K : proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z
      ((proEtaleConstantRingDerivedPullback P.Ring f).obj K) := by
  have : LocallyOfFiniteType (Over.mk aZ).hom := ‹LocallyOfFiniteType aZ›
  have : QuasiCompact (Over.mk aZ).hom := ‹QuasiCompact aZ›
  have : LocallyOfFiniteType (Over.mk aY).hom := ‹LocallyOfFiniteType aY›
  have : QuasiCompact (Over.mk aY).hom := ‹QuasiCompact aY›
  let g : Over.mk aZ ⟶ Over.mk aY := Over.homMk f hf
  have : IsSeparated g.left := ‹IsSeparated f›
  have : LocallyOfFiniteType g.left := ‹LocallyOfFiniteType f›
  have : QuasiCompact g.left := ‹QuasiCompact f›
  exact sf_pullback_finiteTorConstructible P.field P.coefficients.l
    P.coefficients.different P.extension P.level P.level_pos
    (Over.mk aZ) (Over.mk aY) g K hK

private theorem ctf_tensor (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K L : proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
    (hL : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y L) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((tensorModel Y P.Ring).tensor.obj (K, L)) := by
  classical
  let : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) := ‹LocallyOfFiniteType aY›
  have : QuasiCompact (Y ↘ Spec (.of P.field.k)) := ‹QuasiCompact aY›
  let C := proEtaleRingModules Y (proEtaleConstantRing Y P.Ring)
  let : HasDerivedCategory C := HasDerivedCategory.standard C
  let Kc := (DerivedCategory.Q (C := C)).objPreimage K
  let Lc := (DerivedCategory.Q (C := C)).objPreimage L
  let eK := (DerivedCategory.Q (C := C)).objObjPreimageIso K
  let eL := (DerivedCategory.Q (C := C)).objObjPreimageIso L
  have hKc := ctf_of_iso P Y eK.symm hK
  have hLc := ctf_of_iso P Y eL.symm hL
  obtain ⟨Q, f, hQ, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral Kc
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C f).2 hf
  let e : derivedTensor Y P.Ring Kc Lc Q f hf hQ ≅
      (tensorModel Y P.Ring).tensor.obj (K, L) :=
    RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
        (ProEt.topology Y) (proEtaleConstantRing Y P.Ring) Q Lc (.inl hQ) ≪≫
      (tensorModel Y P.Ring).tensor.mapIso
        ((asIso (DerivedCategory.Q.map f) ≪≫ eK).prod eL)
  obtain ⟨a, b, htK⟩ := hKc.2
  obtain ⟨c, d, htL⟩ := hLc.2
  exact ctf_of_iso P Y e
    ((finiteCoefficient_tensor_ctf P.field P.coefficients.l P.coefficients.different
      P.extension P.level P.level_pos Y Kc Lc Q f hf hQ a b hKc htK hLc.1).2
      c d hLc htL).1

private theorem ctf_prefix (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :
    ∀ (j : ℕ) (L : Fin (j + 1) → proEtaleDerivedCategory Y P.Ring),
      (∀ i, finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
        Y (L i)) →
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
        (tensorPrefix Y P.Ring j L) := by
  intro j
  induction j with
  | zero => intro L hL; exact hL 0
  | succ j ih =>
    intro L hL
    exact ctf_tensor P Y aY _ _ (ih _ (fun i ↦ hL i.castSucc)) (hL (Fin.last _))

private theorem geometry {B : Scheme.{u}} (r : ℕ) (X : ℕ → Over B)
    (hX : ∀ i < r, IsSeparated (X i).hom ∧ LocallyOfFiniteType (X i).hom ∧
      QuasiCompact (X i).hom) :
    ∀ j < r,
      (IsSeparated (product X j).hom ∧ LocallyOfFiniteType (product X j).hom ∧
        QuasiCompact (product X j).hom) ∧
      ∀ i : Fin (j + 1), IsSeparated (projection X j i) ∧
        LocallyOfFiniteType (projection X j i) ∧ QuasiCompact (projection X j i) := by
  intro j
  induction j with
  | zero =>
    intro hj
    refine ⟨hX 0 hj, ?_⟩
    intro i
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    change IsSeparated (𝟙 _) ∧ LocallyOfFiniteType (𝟙 _) ∧ QuasiCompact (𝟙 _)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  | succ j ih =>
    intro hj
    obtain ⟨hh, hp⟩ := ih (by omega)
    let := hh.1
    let := hh.2.1
    let := hh.2.2
    let := (hX (j + 1) hj).1
    let := (hX (j + 1) hj).2.1
    let := (hX (j + 1) hj).2.2
    refine ⟨?_, ?_⟩
    · change IsSeparated (fst X j ≫ (product X j).hom) ∧
        LocallyOfFiniteType (fst X j ≫ (product X j).hom) ∧
        QuasiCompact (fst X j ≫ (product X j).hom)
      exact ⟨inferInstance, inferInstance, inferInstance⟩
    intro i
    refine Fin.lastCases ?_ (fun k ↦ ?_) i
    · simpa only [projection, Fin.lastCases_last] using
        (show IsSeparated (snd X j) ∧ LocallyOfFiniteType (snd X j) ∧
          QuasiCompact (snd X j) from ⟨inferInstance, inferInstance, inferInstance⟩)
    · let := (hp k).1
      let := (hp k).2.1
      let := (hp k).2.2
      simpa only [projection, Fin.lastCases_castSucc] using
        (show IsSeparated (fst X j ≫ projection X j k) ∧
          LocallyOfFiniteType (fst X j ≫ projection X j k) ∧
          QuasiCompact (fst X j ≫ projection X j k) from
          ⟨inferInstance, inferInstance, inferInstance⟩)

private theorem projection_comp {B : Scheme.{u}} (X : ℕ → Over B) :
    ∀ (j : ℕ) (i : Fin (j + 1)), projection X j i ≫ (X i.val).hom = (product X j).hom := by
  intro j
  induction j with
  | zero =>
    intro i
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    exact Category.id_comp _
  | succ j ih =>
    intro i
    refine Fin.lastCases ?_ (fun k ↦ ?_) i
    · simp only [projection, Fin.lastCases_last, Fin.val_last]
      change pullback.snd (product X j).hom (X (j + 1)).hom ≫ (X (j + 1)).hom =
        pullback.fst (product X j).hom (X (j + 1)).hom ≫ (product X j).hom
      exact pullback.condition.symm
    · simp only [projection, Fin.lastCases_castSucc, Fin.val_castSucc, Category.assoc, ih]
      rfl

/-- Relative external-power regrouping and all geometric and finite-Tor domain assertions.
Source: Stacks sites-cohomology.tex, Tags 07A4, 0G7E, 0D6D; blueprint sk-prop-an,
Steps 3--4 (blueprint: lem-pur-relative-external-power-regrouping).
Proof:
1. Induct on the number of factors. The first structure map is f_1 and the first
projection is the identity. Base change preserves separatedness and finite type;
composition gives the structure maps, coordinate projections and maps to Spec k.
2. Choose a finite Tor interval for every input. Pullback preserves each interval
(lem-sf-pullback-tor-amplitude). Binary tensor adds the intervals and preserves
constructibility (lem-sf-tensor-ctf). Induction gives every T_j and its two next
pullbacks in the stated full subcategories.
3. Constant-section coefficient identifications compose. Distribute pullback across
left-associated tensors by binary comparisons (07A4), then apply the inverse of
c_(a,p), namely proEtaleConstantRingPullbackComposition (0D6D), to each factor.
4. Tensor this lambda with the identity on the last factor. Left association and
p_last=b identify the target with T_(j+1); regroup is exactly this composite.
No flatness of scheme morphisms, compact support, duality or exceptional adjoint is used. -/
theorem relative_external_power_regrouping
    (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (r : ℕ) (hr : 1 ≤ r) (X : ℕ → Over B)
    (hX : ∀ i < r, IsSeparated (X i).hom ∧ LocallyOfFiniteType (X i).hom ∧
      QuasiCompact (X i).hom)
    (K : ∀ i : ℕ, proEtaleDerivedCategory (X i).left P.Ring)
    (hK : ∀ i < r, finiteTorConstructible P.coefficients.l P.extension P.level
      P.level_pos (X i).left (K i)) :
    (∀ j < r,
      (IsSeparated ((product X j).hom ≫ b) ∧
        LocallyOfFiniteType ((product X j).hom ≫ b) ∧
        QuasiCompact ((product X j).hom ≫ b)) ∧
      (IsSeparated (product X j).hom ∧ LocallyOfFiniteType (product X j).hom ∧
        QuasiCompact (product X j).hom) ∧
      (∀ i : Fin (j + 1), IsSeparated (projection X j i) ∧
        LocallyOfFiniteType (projection X j i) ∧ QuasiCompact (projection X j i)) ∧
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
        (product X j).left (external X P.Ring K j)) ∧
    (∀ j, j + 1 < r →
      (IsSeparated (fst X j) ∧ LocallyOfFiniteType (fst X j) ∧ QuasiCompact (fst X j)) ∧
      (IsSeparated (snd X j) ∧ LocallyOfFiniteType (snd X j) ∧ QuasiCompact (snd X j)) ∧
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
        (product X (j + 1)).left
        ((proEtaleConstantRingDerivedPullback P.Ring (fst X j)).obj (external X P.Ring K j)) ∧
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
        (product X (j + 1)).left
        ((proEtaleConstantRingDerivedPullback P.Ring (snd X j)).obj (K (j + 1)))) := by
  have hgeom := geometry r X hX
  have hr0 : 0 < r := hr
  have hdom : ∀ j < r,
      (IsSeparated ((product X j).hom ≫ b) ∧
        LocallyOfFiniteType ((product X j).hom ≫ b) ∧
        QuasiCompact ((product X j).hom ≫ b)) ∧
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
        (product X j).left (external X P.Ring K j) := by
    intro j hj
    have hg := hgeom j hj
    let := hg.1.1
    let := hg.1.2.1
    let := hg.1.2.2
    refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, ?_⟩
    apply ctf_prefix P (product X j).left ((product X j).hom ≫ b)
    intro i
    have hi : i.val < r := by
      by_cases hj0 : j = 0
      · subst j
        have : i.val = 0 := by omega
        simpa only [this] using hr0
      · exact lt_of_lt_of_le i.isLt (by omega)
    let := (hX i.val hi).1
    let := (hX i.val hi).2.1
    let := (hX i.val hi).2.2
    let := (hg.2 i).1
    let := (hg.2 i).2.1
    let := (hg.2 i).2.2
    exact ctf_pullback P ((product X j).hom ≫ b) ((X i.val).hom ≫ b)
      (projection X j i) (by rw [← Category.assoc, projection_comp]) (K i.val) (hK i.val hi)
  constructor
  · intro j hj
    exact ⟨(hdom j hj).1, (hgeom j hj).1, (hgeom j hj).2, (hdom j hj).2⟩
  · intro j hj
    have hp := hgeom j (by omega)
    let := hp.1.1
    let := hp.1.2.1
    let := hp.1.2.2
    let := (hX (j + 1) hj).1
    let := (hX (j + 1) hj).2.1
    let := (hX (j + 1) hj).2.2
    let := (hdom j (by omega)).1.2.1
    let := (hdom j (by omega)).1.2.2
    let := (hdom (j + 1) hj).1.2.1
    let := (hdom (j + 1) hj).1.2.2
    refine ⟨⟨inferInstance, inferInstance, inferInstance⟩,
      ⟨inferInstance, inferInstance, inferInstance⟩, ?_, ?_⟩
    · exact ctf_pullback P ((product X (j + 1)).hom ≫ b) ((product X j).hom ≫ b)
        (fst X j) (by rfl) _ (hdom j (by omega)).2
    · exact ctf_pullback P ((product X (j + 1)).hom ≫ b) ((X (j + 1)).hom ≫ b)
        (snd X j) (by
          change pullback.snd (product X j).hom (X (j + 1)).hom ≫
            ((X (j + 1)).hom ≫ b) =
            (pullback.fst (product X j).hom (X (j + 1)).hom ≫ (product X j).hom) ≫ b
          rw [← Category.assoc, ← pullback.condition]) _ (hK (j + 1) hj)

end WeilConjectures.RelativeExternalPower
