module
public import Sheaf.Paper.CupCechPairCochain
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct
local notation "cechCupCochain" => n2CechCupCochain
noncomputable section


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cechEquiv_smul {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) (n : ℕ) (c : Γ(X, ⊤))
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X n)
    (y : Fin (n + 1) → ι) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n (c • a) y =
      c • (show F.presheafModuleCat.obj (op (⨅ k, U (y k))) from
        TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a y) := by
  simp only [TopCat.Presheaf.cechComplexFunctorXAddEquiv_apply]
  exact _root_.map_smul
    ((F.presheafModuleCat.map _).hom.comp
      (TopCat.Presheaf.cechComplexFunctorπ U F.presheafModuleCat n y).hom) c a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The row formula is bilinear over global sections.
Source: Stacks Project, Remark 20.25.3 (blueprint: new-cup-cech-total-cochain-map). -/
@[irreducible] private def cupCechPairLinear {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (D : CupResolutionPairing F G) (r s i j : ℕ) :
    ((cupCechDouble U D.left.K).X r).X i →ₗ[Γ(X, ⊤)]
      ((cupCechDouble U D.right.K).X s).X j →ₗ[Γ(X, ⊤)]
        ((cupCechDouble U D.target.K).X (r + s)).X (i + j) :=
  LinearMap.mk₂ _ (cupCechPairCochain U D r s i j)
    (by
      intro a a' b
      apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv
        U (D.target.K.X (r + s)).presheafModuleCat (i + j)).injective
      simp only [cupCechPairCochain, AddEquiv.apply_symm_apply, map_add]
      funext y
      simp only [Pi.add_apply, map_add, LinearMap.add_apply])
    (by
      intro c a b
      apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv
        U (D.target.K.X (r + s)).presheafModuleCat (i + j)).injective
      funext y
      rw [cechEquiv_smul]
      simp only [cupCechPairCochain, AddEquiv.apply_symm_apply]
      rw [cechEquiv_smul U (D.left.K.X r)]
      change D.pair r s _ ((D.left.K.X r).presheafModuleCat.map _ (c • _)) _ =
        c • (show (D.target.K.X (r + s)).presheafModuleCat.obj _ from D.pair r s _ _ _)
      rw [show (D.left.K.X r).presheafModuleCat.map
          (n2CupFaceRestriction U y (n2CupFront i j)).op (c • _) =
          c • (D.left.K.X r).presheafModuleCat.map
            (n2CupFaceRestriction U y (n2CupFront i j)).op _ from
        _root_.map_smul _ c _]
      change D.pair r s (⨅ k, U (y k))
        ((X.presheaf.map (homOfLE
          (show (⨅ k, U (y k)) ≤ ⊤ from le_top)).op c) • _) _ = _
      simp only [LinearMap.map_smul, LinearMap.smul_apply]
      rfl)
    (by
      intro a b b'
      apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv
        U (D.target.K.X (r + s)).presheafModuleCat (i + j)).injective
      simp only [cupCechPairCochain, AddEquiv.apply_symm_apply, map_add]
      funext y
      simp only [Pi.add_apply, map_add])
    (by
      intro c a b
      apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv
        U (D.target.K.X (r + s)).presheafModuleCat (i + j)).injective
      funext y
      rw [cechEquiv_smul]
      simp only [cupCechPairCochain, AddEquiv.apply_symm_apply]
      rw [cechEquiv_smul U (D.right.K.X s)]
      change D.pair r s _ _ ((D.right.K.X s).presheafModuleCat.map _ (c • _)) =
        c • (show (D.target.K.X (r + s)).presheafModuleCat.obj _ from D.pair r s _ _ _)
      rw [show (D.right.K.X s).presheafModuleCat.map
          (n2CupFaceRestriction U y (n2CupBack i j)).op (c • _) =
          c • (D.right.K.X s).presheafModuleCat.map
            (n2CupFaceRestriction U y (n2CupBack i j)).op _ from
        _root_.map_smul _ c _]
      change D.pair r s (⨅ k, U (y k)) _
        ((X.presheaf.map (homOfLE
          (show (⨅ k, U (y k)) ≤ ⊤ from le_top)).op c) • _) = _
      simp only [LinearMap.map_smul]
      rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The signed row pairing included in a specified total degree.
Source: Stacks Project, equation 07MB (blueprint: new-cup-cech-total-cochain-map). -/
@[irreducible] private def cupCechSignedRow {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (D : CupResolutionPairing F G)
    (r s i j k : ℕ) (hk : r + s + (i + j) = k) :
    ((cupCechDouble U D.left.K).X r).X i →ₗ[Γ(X, ⊤)]
      ((cupCechDouble U D.right.K).X s).X j →ₗ[Γ(X, ⊤)]
        ((cupCechDouble U D.target.K).total (ComplexShape.up ℕ)).X k :=
  (-1 : ℤ) ^ (i * s) • (cupCechPairLinear U D r s i j).compr₂
    ((cupCechDouble U D.target.K).ιTotal (ComplexShape.up ℕ)
      (r + s) (i + j) k (by simpa using hk)).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Extend a bilinear family over the two coproducts defining total degrees.
Source: coproduct universal property (blueprint: new-cup-cech-total-cochain-map). -/
@[irreducible] private def totalDescBilinear {R : Type u} [CommRing R]
    (A B : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (C : ModuleCat.{u} R) (m n : ℕ)
    (f : ∀ r i, r + i = m → ∀ s j, s + j = n →
      (A.X r).X i →ₗ[R] (B.X s).X j →ₗ[R] C) :
    (A.total (ComplexShape.up ℕ)).X m →ₗ[R]
      (B.total (ComplexShape.up ℕ)).X n →ₗ[R] C :=
  (A.totalDesc (c₁₂ := ComplexShape.up ℕ) (i₁₂ := m)
    (A := ModuleCat.of R ((B.total (ComplexShape.up ℕ)).X n →ₗ[R] C))
    (fun r i hm ↦ ModuleCat.ofHom
      (LinearMap.flip
        (B.totalDesc (c₁₂ := ComplexShape.up ℕ) (i₁₂ := n)
          (A := ModuleCat.of R ((A.X r).X i →ₗ[R] C))
          (fun s j hn ↦ ModuleCat.ofHom (LinearMap.flip (f r i hm s j hn)))).hom))).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The double coproduct extension has its prescribed values on inclusions.
Source: coproduct universal property (blueprint: new-cup-cech-total-cochain-map). -/
private theorem totalDescBilinear_ι {R : Type u} [CommRing R]
    (A B : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (C : ModuleCat.{u} R) (m n : ℕ)
    (f : ∀ r i, r + i = m → ∀ s j, s + j = n →
      (A.X r).X i →ₗ[R] (B.X s).X j →ₗ[R] C)
    (r i s j : ℕ) (hm : r + i = m) (hn : s + j = n)
    (a : (A.X r).X i) (b : (B.X s).X j) :
    totalDescBilinear A B C m n f
      (A.ιTotal (ComplexShape.up ℕ) r i m hm a)
      (B.ιTotal (ComplexShape.up ℕ) s j n hn b) = f r i hm s j hn a b := by
  unfold totalDescBilinear
  have h := A.ι_totalDesc (c₁₂ := ComplexShape.up ℕ)
    (fun r i hm ↦ ModuleCat.ofHom
      (LinearMap.flip
        (B.totalDesc (c₁₂ := ComplexShape.up ℕ) (i₁₂ := n)
          (A := ModuleCat.of R ((A.X r).X i →ₗ[R] C))
          (fun s j hn ↦ ModuleCat.ofHom (LinearMap.flip (f r i hm s j hn)))).hom))
    r i hm
  have h' := congrArg (fun g ↦ g.hom a (B.ιTotal (ComplexShape.up ℕ) s j n hn b)) h
  change _ = (B.totalDesc (c₁₂ := ComplexShape.up ℕ)
    (A := ModuleCat.of R ((A.X r).X i →ₗ[R] C))
    (fun s j hn ↦ ModuleCat.ofHom (LinearMap.flip (f r i hm s j hn)))).hom
      (B.ιTotal (ComplexShape.up ℕ) s j n hn b) a at h'
  simp only [ConcreteCategory.comp_apply] at h'
  erw [h']
  have hB := B.ι_totalDesc (c₁₂ := ComplexShape.up ℕ)
    (fun s j hn ↦ ModuleCat.ofHom (LinearMap.flip (f r i hm s j hn))) s j hn
  exact (congrArg (fun g ↦ g.hom b a) hB)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Two bilinear maps from total degrees agree if they agree on all row inclusions.
Source: coproduct universal property (blueprint: new-cup-cech-total-cochain-map). -/
private theorem totalBilinear_ext {R : Type u} [CommRing R]
    (A B : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (C : ModuleCat.{u} R) (m n : ℕ)
    (f g : (A.total (ComplexShape.up ℕ)).X m →ₗ[R]
      (B.total (ComplexShape.up ℕ)).X n →ₗ[R] C)
    (h : ∀ r i (hm : r + i = m) s j (hn : s + j = n)
      (a : (A.X r).X i) (b : (B.X s).X j),
      f (A.ιTotal (ComplexShape.up ℕ) r i m hm a)
        (B.ιTotal (ComplexShape.up ℕ) s j n hn b) =
      g (A.ιTotal (ComplexShape.up ℕ) r i m hm a)
        (B.ιTotal (ComplexShape.up ℕ) s j n hn b)) : f = g := by
  suffices hh : (ModuleCat.ofHom f : (A.total (ComplexShape.up ℕ)).X m ⟶
      ModuleCat.of R ((B.total (ComplexShape.up ℕ)).X n →ₗ[R] C)) =
        ModuleCat.ofHom g from congrArg ModuleCat.Hom.hom hh
  apply HomologicalComplex₂.total.hom_ext
  intro r i hm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  suffices hh : (ModuleCat.ofHom (f (A.ιTotal (ComplexShape.up ℕ) r i m hm a)) :
      (B.total (ComplexShape.up ℕ)).X n ⟶ C) =
        ModuleCat.ofHom (g (A.ιTotal (ComplexShape.up ℕ) r i m hm a)) by
    exact congrArg ModuleCat.Hom.hom hh
  apply HomologicalComplex₂.total.hom_ext
  intro s j hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  exact h r i hm s j hn a b

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Extend the signed rows across both finite total diagonals.
Source: Stacks Project, equation 07MB (blueprint: new-cup-cech-total-cochain-map). -/
@[irreducible] private def cupCechTotalLinear {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (D : CupResolutionPairing F G)
    (m n k : ℕ) (hk : m + n = k) :
    ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ)).X m →ₗ[Γ(X, ⊤)]
      ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ)).X n →ₗ[Γ(X, ⊤)]
        ((cupCechDouble U D.target.K).total (ComplexShape.up ℕ)).X k :=
  totalDescBilinear (cupCechDouble U D.left.K) (cupCechDouble U D.right.K)
    (((cupCechDouble U D.target.K).total (ComplexShape.up ℕ)).X k) m n
    (fun r i hm s j hn ↦ cupCechSignedRow U D r s i j k (by omega))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The bilinear total extension recovers its signed rows.
Source: Stacks Project, equation 07MB (blueprint: new-cup-cech-total-cochain-map). -/
private theorem cupCechTotalLinear_ι {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (D : CupResolutionPairing F G)
    (r s i j m n k : ℕ) (hm : r + i = m) (hn : s + j = n) (hk : m + n = k)
    (a : ((cupCechDouble U D.left.K).X r).X i)
    (b : ((cupCechDouble U D.right.K).X s).X j) :
    cupCechTotalLinear U D m n k hk
      ((cupCechDouble U D.left.K).ιTotal (ComplexShape.up ℕ) r i m hm a)
      ((cupCechDouble U D.right.K).ιTotal (ComplexShape.up ℕ) s j n hn b) =
    (-1 : ℤ) ^ (i * s) •
      (cupCechDouble U D.target.K).ιTotal (ComplexShape.up ℕ)
        (r + s) (i + j) k (by dsimp; omega) (cupCechPairCochain U D r s i j a b) := by
  unfold cupCechTotalLinear
  rw [totalDescBilinear_ι]
  simp only [cupCechSignedRow, cupCechPairLinear, LinearMap.smul_apply,
    LinearMap.compr₂_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The component of the total tensor map, defined by the coproduct universal property.
Source: Stacks Project, equation 07MB (blueprint: new-cup-cech-total-cochain-map). -/
private def cupCechTotalComponent {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (D : CupResolutionPairing F G) (k : ℕ) :
    (HomologicalComplex.mapBifunctor
      ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
      ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
      (curriedTensor (ModuleCat.{u} Γ(X, ⊤))) (ComplexShape.up ℕ)).X k ⟶
        ((cupCechDouble U D.target.K).total (ComplexShape.up ℕ)).X k :=
  HomologicalComplex.mapBifunctorDesc (fun m n hn ↦
    ModuleCat.ofHom (TensorProduct.lift (cupCechTotalLinear U D m n k hn)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restrict the total component to a tensor summand.
Source: coproduct universal property (blueprint: new-cup-cech-total-cochain-map). -/
private theorem cupCechTotalComponent_ι_hom {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (D : CupResolutionPairing F G)
    (m n k : ℕ) (hk : m + n = k) :
    HomologicalComplex.ιMapBifunctor
      ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
      ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
      (curriedTensor (ModuleCat.{u} Γ(X, ⊤))) (ComplexShape.up ℕ) m n k hk ≫
        cupCechTotalComponent U D k =
    ModuleCat.ofHom (TensorProduct.lift (cupCechTotalLinear U D m n k hk)) := by
  apply HomologicalComplex.ι_mapBifunctorDesc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The total component recovers every signed row formula.
Source: Stacks Project, equation 07MB (blueprint: new-cup-cech-total-cochain-map). -/
private theorem cupCechTotalComponent_ι {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (D : CupResolutionPairing F G)
    (r s i j m n k : ℕ) (hm : r + i = m) (hn : s + j = n) (hk : m + n = k)
    (a : ((cupCechDouble U D.left.K).X r).X i)
    (b : ((cupCechDouble U D.right.K).X s).X j) :
    cupCechTotalComponent U D k
      (HomologicalComplex.ιMapBifunctor
        ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
        ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
        (curriedTensor (ModuleCat.{u} Γ(X, ⊤))) (ComplexShape.up ℕ) m n k hk
        (((cupCechDouble U D.left.K).ιTotal (ComplexShape.up ℕ) r i m hm a) ⊗ₜ[Γ(X, ⊤)]
          ((cupCechDouble U D.right.K).ιTotal (ComplexShape.up ℕ) s j n hn b))) =
      (-1 : ℤ) ^ (i * s) •
        (cupCechDouble U D.target.K).ιTotal (ComplexShape.up ℕ)
          (r + s) (i + j) k (by dsimp; omega) (cupCechPairCochain U D r s i j a b) := by
  have h := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := (cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
    (K₂ := (cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
    (F := curriedTensor (ModuleCat.{u} Γ(X, ⊤))) (c := ComplexShape.up ℕ)
    (fun m n hn ↦ ModuleCat.ofHom (TensorProduct.lift (cupCechTotalLinear U D m n k hn)))
    m n hk
  have h' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h)
    (((cupCechDouble U D.left.K).ιTotal (ComplexShape.up ℕ) r i m hm a) ⊗ₜ[Γ(X, ⊤)]
      ((cupCechDouble U D.right.K).ιTotal (ComplexShape.up ℕ) s j n hn b))
  change cupCechTotalComponent U D k _ =
    TensorProduct.lift (cupCechTotalLinear U D m n k hk) _ at h'
  erw [h']
  rw [TensorProduct.lift.tmul]
  unfold cupCechTotalLinear
  rw [totalDescBilinear_ι]
  simp only [cupCechSignedRow, cupCechPairLinear, LinearMap.smul_apply,
    LinearMap.compr₂_apply]
  rfl



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def faceSection {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : X.Modules) {m n : ℕ} (c : ∀ y : Fin m → ι, Γ(F, ⨅ i, U (y i)))
    (y : Fin n → ι) (face : Fin m → Fin n) : Γ(F, ⨅ i, U (y i)) :=
  F.presheaf.map (n2CupFaceRestriction U y face).op (c (y ∘ face))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma faceSection_comp {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : X.Modules) {m n k : ℕ} (c : ∀ y : Fin m → ι, Γ(F, ⨅ i, U (y i)))
    (y : Fin n → ι) (face : Fin k → Fin n) (face' : Fin m → Fin k) :
    F.presheaf.map (n2CupFaceRestriction U y face).op
      (faceSection U F c (y ∘ face) face') = faceSection U F c y (face ∘ face') := by
  dsimp only [faceSection]
  exact TopCat.Presheaf.map_homOfLE_map_homOfLE_apply F.presheaf _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma eq_cast {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : X.Modules) {m n : ℕ} (h : m = n)
    (c : ((cechComplexFunctor U).obj F.presheafModuleCat).X m)
    (y : Fin (n + 1) → ι) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n
      (eqToHom (congrArg (fun i ↦ ((cechComplexFunctor U).obj F.presheafModuleCat).X i)
        h) c) y =
      faceSection U F
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat m c)
        y (Fin.cast (congrArg (fun i ↦ i + 1) h)) := by
  subst n
  dsimp only [eqToHom_refl]
  change TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat m c y =
    F.presheaf.map (𝟙 (op (⨅ i, U (y i))))
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat m c y)
  exact (ConcreteCategory.congr_hom (F.presheaf.map_id _) _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma equiv_d {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : X.Modules) (n : ℕ)
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X n)
    (y : Fin (n + 2) → ι) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat (n + 1)
      (((cechComplexFunctor U).obj F.presheafModuleCat).d n (n + 1) a) y =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        F.presheaf.map (n2CupFaceRestriction U y i.succAbove).op
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a
            (y ∘ i.succAbove)) := by
  have h := (congrArg (fun f ↦ f a y)
    ((TopCat.Presheaf.cechComplexFunctorIso U F.presheafModuleCat).hom.comm n (n + 1))).symm
  change TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat (n + 1)
    (((cechComplexFunctor U).obj F.presheafModuleCat).d n (n + 1) a) y =
      ((TopCat.Presheaf.cechComplex U).obj
        (F.presheafModuleCat ⋙ forget₂ (ModuleCat _) AddCommGrpCat)).d n (n + 1)
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a) y at h
  rw [TopCat.Presheaf.cechComplex_d_apply] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma faceSection_d {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : X.Modules) (m n : ℕ)
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X m)
    (y : Fin n → ι) (face : Fin (m + 2) → Fin n) :
    faceSection U F
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat (m + 1)
          (((cechComplexFunctor U).obj F.presheafModuleCat).d m (m + 1) a)) y face =
      ∑ i : Fin (m + 2), (-1 : ℤ) ^ i.val • faceSection U F
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat m a)
        y (face ∘ i.succAbove) := by
  unfold faceSection
  rw [equiv_d, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  exact congrArg ((-1 : ℤ) ^ i.val • ·)
    (faceSection_comp U F _ y face i.succAbove)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma faceSection_pair {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (D : CupResolutionPairing F G) (r s p q n : ℕ)
    (a : ((cupCechDouble U D.left.K).X r).X p)
    (b : ((cupCechDouble U D.right.K).X s).X q)
    (y : Fin n → ι) (face : Fin (p + q + 1) → Fin n) :
    faceSection U (D.target.K.X (r + s))
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
          (D.target.K.X (r + s)).presheafModuleCat (p + q)
          (cupCechPairCochain U D r s p q a b)) y face =
      D.pair r s (⨅ k, U (y k))
        (faceSection U (D.left.K.X r)
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
            (D.left.K.X r).presheafModuleCat p a) y (face ∘ n2CupFront p q))
        (faceSection U (D.right.K.X s)
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
            (D.right.K.X s).presheafModuleCat q b) y (face ∘ n2CupBack p q)) := by
  simp only [faceSection, cupCechPairCochain, AddEquiv.apply_symm_apply]
  exact (D.restriction r s _ _ (n2CupFaceRestriction U y face).le _ _).trans
    (congrArg₂ (fun a b ↦ D.pair r s (⨅ k, U (y k)) a b)
      (faceSection_comp U (D.left.K.X r)
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
          (D.left.K.X r).presheafModuleCat p a) y face (n2CupFront p q))
      (faceSection_comp U (D.right.K.X s)
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
          (D.right.K.X s).presheafModuleCat q b) y face (n2CupBack p q)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma aw_sum {A : Type*} [AddCommGroup A] (p q : ℕ)
    (L : Fin (p + 2) → A) (R : Fin (q + 2) → A) (S : Fin (p + q + 2) → A)
    (hl : ∀ i : Fin (p + 1), S ⟨i.val, by omega⟩ = L i.castSucc)
    (hr : ∀ j : Fin (q + 1), S ⟨p + 1 + j.val, by omega⟩ = R j.succ)
    (hm : L (Fin.last (p + 1)) = R 0) :
    (∑ i, (-1 : ℤ) ^ i.val • S i) =
      (∑ i, (-1 : ℤ) ^ i.val • L i) + (-1 : ℤ) ^ p • ∑ j, (-1 : ℤ) ^ j.val • R j := by
  have hn : (p + 1) + (q + 1) = p + q + 2 := by omega
  have hd : (∑ i, (-1 : ℤ) ^ i.val • S i) =
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ i.val • L i.castSucc) +
        ∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) • R j.succ := by
    rw [← Fin.sum_congr' (fun i ↦ (-1 : ℤ) ^ i.val • S i) hn, Fin.sum_univ_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      exact congrArg ((-1 : ℤ) ^ i.val • ·) (hl i)
    · apply Finset.sum_congr rfl
      intro j _
      exact congrArg ((-1 : ℤ) ^ (p + 1 + j.val) • ·) (hr j)
  rw [hd, Fin.sum_univ_castSucc (fun i : Fin (p + 2) ↦ (-1 : ℤ) ^ i.val • L i),
    Fin.sum_univ_succ (fun j : Fin (q + 2) ↦ (-1 : ℤ) ^ j.val • R j)]
  simp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero, pow_zero, one_smul,
    Fin.val_succ, hm, smul_add, Finset.smul_sum]
  have ht : (∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) • R j.succ) =
      ∑ j : Fin (q + 1), (-1 : ℤ) ^ p • ((-1 : ℤ) ^ (j.val + 1) • R j.succ) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_smul, ← pow_add]
    congr 2
    omega
  rw [ht, pow_succ', mul_smul, neg_one_zsmul]
  abel

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma pair_sum_left {R A B C : Type*} [CommRing R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B →ₗ[R] C) {n : ℕ} (a : Fin n → A) (b : B) :
    f (∑ i, (-1 : ℤ) ^ i.val • a i) b = ∑ i, (-1 : ℤ) ^ i.val • f (a i) b := by
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma pair_sum_right {R A B C : Type*} [CommRing R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B →ₗ[R] C) {n : ℕ} (a : A) (b : Fin n → B) :
    f a (∑ i, (-1 : ℤ) ^ i.val • b i) = ∑ i, (-1 : ℤ) ^ i.val • f a (b i) := by
  simp only [map_sum, map_zsmul]

set_option maxHeartbeats 800000 in
-- The dependent degree casts and finite face arithmetic require extra elaboration.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The row pairing satisfies the alternating Cech Leibniz identity.
Source: Stacks Project, Remark 20.25.3, equation 07MB.
(blueprint: new-cup-cech-total-cochain-map)
Proof: expand the omitted-vertex sums. Before the shared vertex each term is
from the left differential; after it each is from the right differential with
sign (-1)^p. The two shared-vertex terms agree by restriction compatibility
and cancel. Bilinearity distributes the sums and the signs. -/
private theorem cupCechPairCochain_cech_leibniz {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (D : CupResolutionPairing F G) (r s p q : ℕ)
    (a : ((cechComplexFunctor U).obj (D.left.K.X r).presheafModuleCat).X p)
    (b : ((cechComplexFunctor U).obj (D.right.K.X s).presheafModuleCat).X q) :
    ((cechComplexFunctor U).obj (D.target.K.X (r + s)).presheafModuleCat).d
        (p + q) (p + q + 1) (cupCechPairCochain U D r s p q a b) =
      (eqToHom (congrArg
        (fun n ↦ ((cechComplexFunctor U).obj (D.target.K.X (r + s)).presheafModuleCat).X n)
        (Nat.add_right_comm p 1 q)))
          (cupCechPairCochain U D r s (p + 1) q
            (((cechComplexFunctor U).obj (D.left.K.X r).presheafModuleCat).d p (p + 1) a) b) +
      (-1 : ℤ) ^ p • (eqToHom (congrArg
        (fun n ↦ ((cechComplexFunctor U).obj (D.target.K.X (r + s)).presheafModuleCat).X n)
        (Nat.add_assoc p q 1).symm))
          (cupCechPairCochain U D r s p (q + 1) a
            (((cechComplexFunctor U).obj (D.right.K.X s).presheafModuleCat).d q (q + 1) b)) := by
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv
    U (D.target.K.X (r + s)).presheafModuleCat (p + q + 1)).injective
  simp only [map_add, map_zsmul]
  funext y
  rw [equiv_d]
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [eq_cast U (D.target.K.X (r + s)) (Nat.add_right_comm p 1 q),
    eq_cast U (D.target.K.X (r + s)) (Nat.add_assoc p q 1).symm]
  change (∑ i : Fin (p + q + 2), (-1 : ℤ) ^ i.val •
      faceSection U (D.target.K.X (r + s))
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv
          U (D.target.K.X (r + s)).presheafModuleCat (p + q)
          (cupCechPairCochain U D r s p q a b)) y i.succAbove) = _
  simp_rw [faceSection_pair]
  rw [faceSection_d, faceSection_d]
  rw [pair_sum_left, pair_sum_right]
  apply aw_sum p q
  · intro i
    apply congrArg₂ (fun a b ↦ D.pair r s (⨅ k, U (y k)) a b)
    · apply congrArg (faceSection U (D.left.K.X r) _ y)
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, n2CupFront, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all
    · apply congrArg (faceSection U (D.right.K.X s) _ y)
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, n2CupBack, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all <;> omega
  · intro j
    apply congrArg₂ (fun a b ↦ D.pair r s (⨅ k, U (y k)) a b)
    · apply congrArg (faceSection U (D.left.K.X r) _ y)
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, n2CupFront, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all
      omega
    · apply congrArg (faceSection U (D.right.K.X s) _ y)
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, n2CupBack, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all <;> omega
  · apply congrArg₂ (fun a b ↦ D.pair r s (⨅ k, U (y k)) a b)
    · apply congrArg (faceSection U (D.left.K.X r) _ y)
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, n2CupFront, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all
      omega
    · apply congrArg (faceSection U (D.right.K.X s) _ y)
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, n2CupBack, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all
      omega

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma equiv_map {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (φ : F ⟶ G) (n : ℕ)
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X n)
    (y : Fin (n + 1) → ι) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U G.presheafModuleCat n
      (((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map φ.val)).f
          n a) y =
      φ.val.app (op (⨅ k, U (y k)))
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a y) := by
  simp only [TopCat.Presheaf.cechComplexFunctorXAddEquiv_apply]
  erw [← ConcreteCategory.comp_apply
      (((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          φ.val)).f n),
    TopCat.Presheaf.cechComplexFunctor_map_f_π, ConcreteCategory.comp_apply]
  exact (NatTrans.naturality_apply
    ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map φ.val)
    (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op
    (TopCat.Presheaf.cechComplexFunctorπ U F.presheafModuleCat n y a)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma equiv_resolution_cast {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (K : CochainComplex X.Modules ℕ) {r s : ℕ} (h : r = s) (i : ℕ)
    (a : ((cupCechDouble U K).X r).X i) (y : Fin (i + 1) → ι) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U (K.X s).presheafModuleCat i
      (eqToHom (congrArg (fun r ↦ ((cupCechDouble U K).X r).X i) h) a) y =
    (eqToHom (congrArg K.X h)).val.app (op (⨅ k, U (y k)))
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (K.X r).presheafModuleCat i a y) := by
  subst s
  rfl

set_option maxHeartbeats 800000 in
-- Degree casts and the three Cech functor maps require extra elaboration.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The resolution differential satisfies the signed row Leibniz identity.
Source: Stacks Project, Remark 20.25.3, equation 07MB.
(blueprint: new-cup-cech-total-cochain-map)
Proof: evaluate on every tuple intersection. Naturality moves both input
resolution differentials past the face restrictions. The asserted identity is
then D.leibniz on that intersection. The two degree casts are the same as its
casts. The tuplewise equivalence is injective. -/
private theorem cupCechPairCochain_resolution_leibniz {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G)
    (r s i j : ℕ)
    (a : ((cupCechDouble U D.left.K).X r).X i)
    (b : ((cupCechDouble U D.right.K).X s).X j) :
    ((cupCechDouble U D.target.K).d (r + s) (r + s + 1)).f (i + j)
        (cupCechPairCochain U D r s i j a b) =
      eqToHom (congrArg (fun n ↦ ((cupCechDouble U D.target.K).X n).X (i + j))
        (by omega : r + 1 + s = r + s + 1))
        (cupCechPairCochain U D (r + 1) s i j
          (((cupCechDouble U D.left.K).d r (r + 1)).f i a) b) +
      (-1 : ℤ) ^ r •
        eqToHom (congrArg (fun n ↦ ((cupCechDouble U D.target.K).X n).X (i + j))
          (by omega : r + (s + 1) = r + s + 1))
          (cupCechPairCochain U D r (s + 1) i j a
            (((cupCechDouble U D.right.K).d s (s + 1)).f j b)) := by
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
    (D.target.K.X (r + s + 1)).presheafModuleCat (i + j)).injective
  simp only [map_add, map_zsmul]
  funext y
  simp only [Pi.add_apply, Pi.smul_apply]
  have hL := equiv_resolution_cast U D.target.K
    (by omega : r + 1 + s = r + s + 1) (i + j)
    (cupCechPairCochain U D (r + 1) s i j
      (((cupCechDouble U D.left.K).d r (r + 1)).f i a) b) y
  have hR := equiv_resolution_cast U D.target.K
    (by omega : r + (s + 1) = r + s + 1) (i + j)
    (cupCechPairCochain U D r (s + 1) i j a
      (((cupCechDouble U D.right.K).d s (s + 1)).f j b)) y
  erw [hL, hR]
  erw [equiv_map U (D.target.K.d (r + s) (r + s + 1))]
  simp only [cupCechPairCochain, AddEquiv.apply_symm_apply]
  erw [equiv_map U (D.left.K.d r (r + 1)) i a (y ∘ n2CupFront i j)]
  erw [equiv_map U (D.right.K.d s (s + 1)) j b (y ∘ n2CupBack i j)]
  have h := D.leibniz r s (⨅ k, U (y k))
    ((D.left.K.X r).presheaf.map (n2CupFaceRestriction U y (n2CupFront i j)).op
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
        (D.left.K.X r).presheafModuleCat i a (y ∘ n2CupFront i j)))
    ((D.right.K.X s).presheaf.map (n2CupFaceRestriction U y (n2CupBack i j)).op
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
        (D.right.K.X s).presheafModuleCat j b (y ∘ n2CupBack i j)))
  erw [PresheafOfModules.naturality_apply (D.left.K.d r (r + 1)).val
      (n2CupFaceRestriction U y (n2CupFront i j)).op,
    PresheafOfModules.naturality_apply (D.right.K.d s (s + 1)).val
      (n2CupFaceRestriction U y (n2CupBack i j)).op] at h
  exact h



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma total_d_ι {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r i m : ℕ) (hm : r + i = m) :
    K.ιTotal (ComplexShape.up ℕ) r i m hm ≫
        (K.total (ComplexShape.up ℕ)).d m (m + 1) =
      (K.d r (r + 1)).f i ≫
        K.ιTotal (ComplexShape.up ℕ) (r + 1) i (m + 1) (by dsimp; omega) +
      (-1 : ℤ) ^ r • ((K.X r).d i (i + 1) ≫
        K.ιTotal (ComplexShape.up ℕ) r (i + 1) (m + 1) (by dsimp; omega)) := by
  change _ ≫ (K.D₁ _ _ _ + K.D₂ _ _ _) = _
  rw [Preadditive.comp_add, K.ι_D₁, K.ι_D₂,
    K.d₁_eq _ (rfl : (ComplexShape.up ℕ).Rel r (r + 1)) _ _ (by dsimp; omega),
    K.d₂_eq _ _ (rfl : (ComplexShape.up ℕ).Rel i (i + 1)) _ (by dsimp; omega)]
  simp [Units.smul_def]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma tensor_d_ι {R : Type u} [CommRing R]
    (A B : CochainComplex (ModuleCat.{u} R) ℕ) (m n k : ℕ) (hk : m + n = k) :
    HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{u} R))
        (ComplexShape.up ℕ) m n k hk ≫
        (HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{u} R))
          (ComplexShape.up ℕ)).d k (k + 1) =
      A.d m (m + 1) ▷ B.X n ≫
        HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{u} R))
          (ComplexShape.up ℕ) (m + 1) n (k + 1) (by dsimp; omega) +
      (-1 : ℤ) ^ m • (A.X m ◁ B.d n (n + 1) ≫
        HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{u} R))
          (ComplexShape.up ℕ) m (n + 1) (k + 1) (by dsimp; omega)) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (rfl : (ComplexShape.up ℕ).Rel m (m + 1)) _ _ (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
      (rfl : (ComplexShape.up ℕ).Rel n (n + 1)) _ (by dsimp; omega)]
  simp [Units.smul_def]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma total_d_ι_apply {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r i m : ℕ) (hm : r + i = m) (a : (K.X r).X i) :
    (K.total (ComplexShape.up ℕ)).d m (m + 1)
        (K.ιTotal (ComplexShape.up ℕ) r i m hm a) =
      K.ιTotal (ComplexShape.up ℕ) (r + 1) i (m + 1) (by dsimp; omega)
        ((K.d r (r + 1)).f i a) +
      (-1 : ℤ) ^ r • K.ιTotal (ComplexShape.up ℕ) r (i + 1) (m + 1) (by dsimp; omega)
        ((K.X r).d i (i + 1) a) := by
  have h := congrArg ModuleCat.Hom.hom (total_d_ι K r i m hm)
  exact LinearMap.congr_fun h a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cast_row_ι {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    {r r' : ℕ} (h : r = r') (i k : ℕ) (hk : r' + i = k) (a : (K.X r).X i) :
    K.ιTotal (ComplexShape.up ℕ) r' i k hk
      (eqToHom (congrArg (fun r ↦ (K.X r).X i) h) a) =
    K.ιTotal (ComplexShape.up ℕ) r i k (by dsimp; omega) a := by
  subst r'
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cast_col_ι {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r : ℕ) {i i' : ℕ} (h : i = i') (k : ℕ) (hk : r + i' = k) (a : (K.X r).X i) :
    K.ιTotal (ComplexShape.up ℕ) r i' k hk
      (eqToHom (congrArg (fun i ↦ (K.X r).X i) h) a) =
    K.ιTotal (ComplexShape.up ℕ) r i k (by dsimp; omega) a := by
  subst i'
  rfl

set_option maxHeartbeats 800000 in
-- The signed bilinear expressions contain dependent degree transports.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The signed total bilinear formula satisfies Leibniz.
Source: Stacks Project, Remark 20.25.3, equation 07MB.
(blueprint: new-cup-cech-total-cochain-map)
Proof: both sides are bilinear. On a pair of included row cochains, expand the
total differentials into the resolution and Cech parts. The row identities give
four terms. The left resolution term keeps (-1)^(i*s); the right resolution
term has (-1)^(i*s+r), which equals (-1)^(r+i+i*(s+1)). The left Cech term has
(-1)^(i*s+r+s), which equals (-1)^(r+(i+1)*s). The right Cech term has
(-1)^(i*s+r+s+i), which equals (-1)^(r+i+s+i*s). Degree casts disappear after
the target inclusions. Coproduct extensionality proves the identity globally. -/
private theorem cupCechTotalLinear_leibniz {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (D : CupResolutionPairing F G) (m n : ℕ)
    (a : ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ)).X m)
    (b : ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ)).X n) :
    ((cupCechDouble U D.target.K).total (ComplexShape.up ℕ)).d (m + n) (m + n + 1)
      (cupCechTotalLinear U D m n (m + n) rfl a b) =
    cupCechTotalLinear U D (m + 1) n (m + n + 1) (by omega)
      (((cupCechDouble U D.left.K).total (ComplexShape.up ℕ)).d m (m + 1) a) b +
    (-1 : ℤ) ^ m • cupCechTotalLinear U D m (n + 1) (m + n + 1) (by omega) a
      (((cupCechDouble U D.right.K).total (ComplexShape.up ℕ)).d n (n + 1) b) := by
  let A := cupCechDouble U D.left.K
  let B := cupCechDouble U D.right.K
  let C := cupCechDouble U D.target.K
  let f := (cupCechTotalLinear U D m n (m + n) rfl).compr₂
    ((C.total (ComplexShape.up ℕ)).d (m + n) (m + n + 1)).hom
  let g := (cupCechTotalLinear U D (m + 1) n (m + n + 1) (by omega)).comp
      ((A.total (ComplexShape.up ℕ)).d m (m + 1)).hom +
    (-1 : ℤ) ^ m • (cupCechTotalLinear U D m (n + 1) (m + n + 1) (by omega)).compl₂
      ((B.total (ComplexShape.up ℕ)).d n (n + 1)).hom
  have h : f = g := by
    apply totalBilinear_ext A B ((C.total (ComplexShape.up ℕ)).X (m + n + 1)) m n
    intro r i hm s j hn a b
    change (C.total (ComplexShape.up ℕ)).d (m + n) (m + n + 1)
      (cupCechTotalLinear U D m n (m + n) rfl
        (A.ιTotal (ComplexShape.up ℕ) r i m hm a)
        (B.ιTotal (ComplexShape.up ℕ) s j n hn b)) =
      cupCechTotalLinear U D (m + 1) n (m + n + 1) _
        ((A.total (ComplexShape.up ℕ)).d m (m + 1)
          (A.ιTotal (ComplexShape.up ℕ) r i m hm a))
        (B.ιTotal (ComplexShape.up ℕ) s j n hn b) +
      (-1 : ℤ) ^ m • cupCechTotalLinear U D m (n + 1) (m + n + 1) _
        (A.ιTotal (ComplexShape.up ℕ) r i m hm a)
        ((B.total (ComplexShape.up ℕ)).d n (n + 1)
          (B.ιTotal (ComplexShape.up ℕ) s j n hn b))
    rw [total_d_ι_apply A r i m hm a, total_d_ι_apply B s j n hn b]
    simp only [LinearMap.map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply]
    erw [cupCechTotalLinear_ι U D r s i j m n (m + n) hm hn rfl a b]
    erw [cupCechTotalLinear_ι U D (r + 1) s i j (m + 1) n (m + n + 1)
      (by omega) hn (by omega) ((A.d r (r + 1)).f i a) b]
    erw [cupCechTotalLinear_ι U D r s (i + 1) j (m + 1) n (m + n + 1)
      (by omega) hn (by omega) ((A.X r).d i (i + 1) a) b]
    erw [cupCechTotalLinear_ι U D r (s + 1) i j m (n + 1) (m + n + 1)
      hm (by omega) (by omega) a ((B.d s (s + 1)).f j b)]
    erw [cupCechTotalLinear_ι U D r s i (j + 1) m (n + 1) (m + n + 1)
      hm (by omega) (by omega) a ((B.X s).d j (j + 1) b)]
    rw [map_zsmul]
    erw [total_d_ι_apply C (r + s) (i + j) (m + n) (by omega)
      (cupCechPairCochain U D r s i j a b)]
    erw [cupCechPairCochain_resolution_leibniz U D r s i j a b,
      cupCechPairCochain_cech_leibniz U D r s i j a b]
    simp only [map_add, map_zsmul]
    erw [cast_row_ι C (by omega : r + 1 + s = r + s + 1)
      (i + j) (m + n + 1) (by omega)]
    erw [cast_row_ι C (by omega : r + (s + 1) = r + s + 1)
      (i + j) (m + n + 1) (by omega)]
    erw [cast_col_ι C (r + s) (by omega : i + 1 + j = i + j + 1)
      (m + n + 1) (by omega)]
    erw [cast_col_ι C (r + s) (by omega : i + (j + 1) = i + j + 1)
      (m + n + 1) (by omega)]
    have hsign : (-1 : ℤ) ^ (m + i * (s + 1)) = (-1 : ℤ) ^ (i * s + r) := by
      rw [show m + i * (s + 1) = i * s + r + 2 * i by rw [← hm]; ring,
        pow_add, pow_mul]
      simp
    have hleft : i * s + (r + s) = r + (i + 1) * s := by ring
    have hright : i * s + (r + s + i) = m + (s + i * s) := by rw [← hm]; ring
    simp only [smul_add, smul_smul, ← pow_add, hsign]
    rw [hleft, hright]
    exact add_add_add_comm _ _ _ _
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cupCechTotalComponent_comm {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G) (k : ℕ) :
    cupCechTotalComponent U D k ≫
      ((cupCechDouble U D.target.K).total (ComplexShape.up ℕ)).d k (k + 1) =
    (HomologicalComplex.mapBifunctor
      ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
      ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
      (curriedTensor (ModuleCat.{u} Γ(X, ⊤))) (ComplexShape.up ℕ)).d k (k + 1) ≫
        cupCechTotalComponent U D (k + 1) := by
  let A := (cupCechDouble U D.left.K).total (ComplexShape.up ℕ)
  let B := (cupCechDouble U D.right.K).total (ComplexShape.up ℕ)
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro m n hk
  change m + n = k at hk
  subst k
  rw [← Category.assoc, cupCechTotalComponent_ι_hom U D m n (m + n) rfl,
    ← Category.assoc, tensor_d_ι A B m n (m + n) rfl]
  rw [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc,
    Category.assoc, cupCechTotalComponent_ι_hom U D (m + 1) n (m + n + 1) (by omega),
    cupCechTotalComponent_ι_hom U D m (n + 1) (m + n + 1) (by omega)]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  simp only [ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_smul,
    ModuleCat.hom_ofHom, ModuleCat.hom_whiskerLeft, ModuleCat.hom_whiskerRight,
    LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    TensorProduct.lift.tmul]
  exact cupCechTotalLinear_leibniz U D m n a b


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The total Alexander--Whitney map with its formula on every tensor of row summands.
Source: Stacks Project, Remark 20.25.3, equation 07MB.
(blueprint: new-cup-cech-total-cochain-map)

Proof: restrict the front i-face and the back j-face to their common intersection
and apply D.pair r s. Local bilinearity and scalar restriction make this formula
bilinear over the ring of global sections. Multiply by (-1)^(i*s). Extend by the
tensor universal property, and by the coproduct universal property over the
finite diagonals, to define each total-degree component. D.leibniz verifies the
resolution part of the cochain identity: shifting r contributes no extra sign,
while shifting s changes the Koszul factor by (-1)^i. In the Cech part, expand
the omitted-vertex sums. The terms before the common vertex come from the first
input, those after it from the second, and the two terms at the common vertex
cancel. D.restriction identifies composite restrictions. With the total
convention d_res + (-1)^r d_Cech, both parts give the differential of the tensor
complex. Pure tensors in the diagonal summands generate the source, so this
proves the cochain identity everywhere. The defining component formula yields
the displayed equality. For an empty index type all row terms are zero; for
zero degrees the same formula uses singleton tuples and sign one. -/
theorem exists_cupCech_total_cochain_map {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G) :
    let A := (cupCechDouble U D.left.K).total (ComplexShape.up ℕ)
    let B := (cupCechDouble U D.right.K).total (ComplexShape.up ℕ)
    let C := (cupCechDouble U D.target.K).total (ComplexShape.up ℕ)
    ∃ h : HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{u} Γ(X, ⊤)))
        (ComplexShape.up ℕ) ⟶ C,
      ∀ (r s i j m n : ℕ) (hm : r + i = m) (hn : s + j = n)
        (a : ((cupCechDouble U D.left.K).X r).X i)
        (b : ((cupCechDouble U D.right.K).X s).X j),
        h.f (m + n)
          (HomologicalComplex.ιMapBifunctor A B
            (curriedTensor (ModuleCat.{u} Γ(X, ⊤))) (ComplexShape.up ℕ)
            m n (m + n) rfl
            (((cupCechDouble U D.left.K).ιTotal (ComplexShape.up ℕ)
                r i m (by simpa using hm) a) ⊗ₜ[Γ(X, ⊤)]
              ((cupCechDouble U D.right.K).ιTotal (ComplexShape.up ℕ)
                s j n (by simpa using hn) b))) =
          (-1 : ℤ) ^ (i * s) •
            (cupCechDouble U D.target.K).ιTotal (ComplexShape.up ℕ)
              (r + s) (i + j) (m + n) (by dsimp; omega)
              (cupCechPairCochain U D r s i j a b) := by
  let h := CochainComplex.ofHom (cupCechTotalComponent U D)
    (cupCechTotalComponent_comm U D)
  refine ⟨h, ?_⟩
  intro r s i j m n hm hn a b
  exact cupCechTotalComponent_ι U D r s i j m n (m + n) hm hn rfl a b
end
end AlgebraicGeometry.Scheme.Modules
