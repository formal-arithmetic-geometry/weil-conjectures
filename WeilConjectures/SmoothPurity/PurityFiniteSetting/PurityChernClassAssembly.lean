/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.ProjectiveBundleFormula
public import WeilConjectures.AlgebraicGeometry.KummerAdditivity
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalGeometry
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityChernEtaleOrigin
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-! # Finite coordinates and extension of the Chern family

Source: Stacks Project, Tag 0FI5, equation-chern-classes; the ordinary
splitting-principle definition in localized-top-Chern Step 4 (L4).
(blueprint: lem-pur-chern-coefficient-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The signed, reverse-ordered projective-bundle coefficient map on the positive
components c_1,...,c_r. This is the left side of the defining Chern relation, with
neither a degree-zero nor an above-rank component.
Source: Stacks Tag 0FI5, equation-chern-classes
(blueprint: lem-pur-chern-coefficient-assembly). -/
def ordinaryFiniteProjectiveCoefficientMap (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T : Scheme.{u}} {F : T.Modules}
    (a : T ⟶ Spec (.of P.field.k)) (D : ProjectiveBundleRealization T F)
    (hL : D.L.IsInvertible) (r : ℕ)
    (c : ∀ i : Fin r, ordinaryFiniteCohomology P T (i.val + 1)) :
    ordinaryFiniteCohomology P D.A.data.relProj r :=
  ∑ i : Fin r, (-1 : ℤ) ^ i.val •
    (P.ordinaryFiniteHyperplaneProduct D.A.data.relProj (P.projectiveBundleChern a D hL)
      (i.val + 1)
      (P.ordinaryFiniteCohomologyPullback t D.A.data.relProjHom
        (P.diagonalExponent_isUnit a) (i.val + 1) (c i))
      (r - (i.val + 1)) ≫
      eqToHom (congrArg (P.diagonalTwist D.A.data.relProj)
        (Nat.add_sub_of_le (Nat.succ_le_of_lt i.isLt))))

/-- The coefficient sum without the alternating signs.
Source: Stacks Tag 0FI5, projective-bundle basis preceding equation-chern-classes.
(blueprint: lem-pur-chern-coefficient-assembly). -/
def ordinaryFiniteProjectiveUnsignedCoefficientMap (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T : Scheme.{u}} {F : T.Modules}
    (a : T ⟶ Spec (.of P.field.k)) (D : ProjectiveBundleRealization T F)
    (hL : D.L.IsInvertible) (r : ℕ)
    (c : ∀ i : Fin r, ordinaryFiniteCohomology P T (i.val + 1)) :
    ordinaryFiniteCohomology P D.A.data.relProj r :=
  ∑ i : Fin r,
    P.ordinaryFiniteHyperplaneProduct D.A.data.relProj (P.projectiveBundleChern a D hL)
      (i.val + 1)
      (P.ordinaryFiniteCohomologyPullback t D.A.data.relProjHom
        (P.diagonalExponent_isUnit a) (i.val + 1) (c i))
      (r - (i.val + 1)) ≫
      eqToHom (congrArg (P.diagonalTwist D.A.data.relProj)
        (Nat.add_sub_of_le (Nat.succ_le_of_lt i.isLt)))

/-- Alternating the positive coordinates is its own inverse, also in characteristic two.
Source: Stacks Tag 0FI5, signs in equation-chern-classes.
(blueprint: lem-pur-chern-coefficient-assembly). -/
def ordinaryFiniteChernSign (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r : ℕ)
    (c : ∀ i : Fin r, ordinaryFiniteCohomology P T (i.val + 1)) :
    ∀ i : Fin r, ordinaryFiniteCohomology P T (i.val + 1) :=
  fun i ↦ (-1 : ℤ) ^ i.val • c i

/-- Proof: the square of each scalar (-1)^i is one.
Source: Stacks Tag 0FI5, alternating Chern coefficients.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteChernSign_involutive (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (r : ℕ) : Function.Involutive (P.ordinaryFiniteChernSign T r) := by
  intro c
  funext i
  dsimp only [ordinaryFiniteChernSign]
  rw [smul_smul, ← mul_pow]
  simp

/-- Proof: inverse image is additive, and composition commutes with integral scaling.
Source: Stacks Tag 0FI5, additive cohomology pullback.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteCohomologyPullback_zsmul (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T T' : Scheme.{u}} (f : T' ⟶ T)
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) (i : ℕ)
    (z : ℤ) (α : ordinaryFiniteCohomology P T i) :
    P.ordinaryFiniteCohomologyPullback t f hT i (z • α) =
      z • P.ordinaryFiniteCohomologyPullback t f hT i α := by
  simp only [ordinaryFiniteCohomologyPullback, Functor.map_zsmul,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul]

private theorem normalized_square_map
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (F : C ⥤ D) (G : C' ⥤ D') (L : C ⥤ C') (R : D ⥤ D')
    (q : F ⋙ R ≅ L ⋙ G) {K M : C} {K' M' : C'}
    (eK : L.obj K ≅ K') (eM : L.obj M ≅ M') (a : K ⟶ M) :
    ((q.app K) ≪≫ G.mapIso eK).inv ≫ R.map (F.map a) ≫
        ((q.app M) ≪≫ G.mapIso eM).hom =
      G.map (eK.inv ≫ L.map a ≫ eM.hom) := by
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  have hn := q.hom.naturality a
  change R.map (F.map a) ≫ (q.app M).hom =
    (q.app K).hom ≫ G.map (L.map a) at hn
  rw [reassoc_of% hn, Iso.inv_hom_id_assoc]

/-- Normalized pro-etale pullback of a comparison image is the comparison image
of the normalized etale pullback, with the same unit and positive Tate maps.
Source: Stacks Tag 099R, the inverse-image site-comparison square.
Proof: expand the two coefficient comparisons. Naturality of their common
comparison-square isomorphism moves the class across that square; its inverse
cancels. Functoriality combines the remaining three etale arrows.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteCohomologyPullback_comparison (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T T' : Scheme.{u}} (f : T' ⟶ T)
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) (i : ℕ)
    (a : Etale.ordinaryFiniteUnit P.Coefficient T ⟶ P.diagonalTwistEtale T i) :
    P.ordinaryFiniteCohomologyPullback t f hT i
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map a) =
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T').mapDerivedCategory.map
          ((Etale.ordinaryFiniteUnitPullback P.Coefficient f).inv ≫
            (Etale.ordinaryFinitePullback P.Coefficient f).map a ≫
            (P.projectiveBundlePositivePullback t f hT i).hom) := by
  unfold ordinaryFiniteCohomologyPullback ProEtale.kummerCoefficientPullback
  exact normalized_square_map
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T').mapDerivedCategory
    (Etale.ordinaryFinitePullback P.Coefficient f)
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).mapDerivedCategory
    (ProEtale.kummerComparisonPullback P.Coefficient f)
    (Etale.ordinaryFiniteUnitPullback P.Coefficient f)
    (P.projectiveBundlePositivePullback t f hT i) a

/-- Normalized coefficient pullback along a scheme isomorphism is bijective.
Source: Stacks Tag 0FI5, invariance of the coefficient groups under isomorphism.
Proof: derived inverse image along an isomorphism is an equivalence. Its Hom
bijection, composed with the source and target coefficient isomorphisms, is
exactly the stipulated normalized pullback.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteCohomologyPullback_bijective (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T T' : Scheme.{u}} (f : T' ⟶ T) [IsIso f]
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) (i : ℕ) :
    Function.Bijective (P.ordinaryFiniteCohomologyPullback t f hT i) := by
  let F := ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f
  have : F.IsEquivalence := inferInstance
  have : F.leftDerivedFunctor.IsEquivalence := inferInstance
  have : F.mapDerivedCategory.IsEquivalence :=
    Functor.isEquivalence_of_iso F.leftDerivedFunctorIsoMapDerivedCategory
  let e :=
    (ProEtale.kummerCoefficientPullback P.Coefficient f _ _
      (Etale.ordinaryFiniteUnitPullback P.Coefficient f)).homCongr
    (ProEtale.kummerCoefficientPullback P.Coefficient f _ _
      (P.projectiveBundlePositivePullback t f hT i))
  have hmap : Function.Bijective
      (F.mapDerivedCategory.map (X := P.projectiveBundleUnit T)
        (Y := P.diagonalTwist T i)) :=
    ⟨F.mapDerivedCategory.map_injective, F.mapDerivedCategory.map_surjective⟩
  exact e.bijective.comp hmap

/-- Normalized coefficient pullback along a scheme isomorphism reflects equality.
Source: Stacks Tag 0FI5, independence of the projective presentation.
Proof: inverse image along an isomorphism is an equivalence. Exact derivation
preserves that equivalence. Cancel the two coefficient comparison isomorphisms
and then use faithfulness on the original Hom group.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteCohomologyPullback_injective (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T T' : Scheme.{u}} (f : T' ⟶ T) [IsIso f]
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) (i : ℕ) :
    Function.Injective (P.ordinaryFiniteCohomologyPullback t f hT i) := by
  exact (P.ordinaryFiniteCohomologyPullback_bijective t f hT i).1

/-- Proof: the derived tensor is additive in its first variable; all other arrows
are fixed. Source: Stacks Tag 0FI5, bilinear cup product.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteHyperplaneStep_zsmul (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)
    (i : ℕ) (z : ℤ) (α : ordinaryFiniteCohomology P T i) :
    P.ordinaryFiniteHyperplaneStep T h i (z • α) =
      z • P.ordinaryFiniteHyperplaneStep T h i α := by
  unfold ordinaryFiniteHyperplaneStep ordinaryFiniteHyperplaneStepRaw
  dsimp only [ProEtale.derivedTensor]
  rw [Functor.map_zsmul]
  simp only [NatTrans.app_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul]

/-- Proof: induction on the ordered power, using scalar linearity of each cup step.
Source: Stacks Tag 0FI5, bilinear cup powers.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteHyperplaneProduct_zsmul (P : PurityFiniteSetting.{u})
    (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)
    (i : ℕ) (z : ℤ) (α : ordinaryFiniteCohomology P T i) (j : ℕ) :
    P.ordinaryFiniteHyperplaneProduct T h i (z • α) j =
      z • P.ordinaryFiniteHyperplaneProduct T h i α j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    dsimp only [ordinaryFiniteHyperplaneProduct]
    rw [ih, ordinaryFiniteHyperplaneStep_zsmul]

/-- Normalized pullback is additive on the published cohomology groups.
Source: Stacks Tag 0FI5, additive inverse image in the projective relation.
Proof: inverse image is additive and composition distributes over addition.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteCohomologyPullback_add (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T T' : Scheme.{u}} (f : T' ⟶ T)
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) (i : ℕ)
    (α β : ordinaryFiniteCohomology P T i) :
    P.ordinaryFiniteCohomologyPullback t f hT i (α + β) =
      P.ordinaryFiniteCohomologyPullback t f hT i α +
        P.ordinaryFiniteCohomologyPullback t f hT i β := by
  simp only [ordinaryFiniteCohomologyPullback, Functor.map_add,
    Preadditive.add_comp, Preadditive.comp_add]

/-- The ordered cup step is additive in the arbitrary pro-etale input class.
Source: Stacks Tag 0FI5, bilinear full-support cup product.
Proof: tensoring is additive in its first variable, then distribute composition.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteHyperplaneStep_add (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)
    (i : ℕ) (α β : ordinaryFiniteCohomology P T i) :
    P.ordinaryFiniteHyperplaneStep T h i (α + β) =
      P.ordinaryFiniteHyperplaneStep T h i α + P.ordinaryFiniteHyperplaneStep T h i β := by
  unfold ordinaryFiniteHyperplaneStep ordinaryFiniteHyperplaneStepRaw
  dsimp only [ProEtale.derivedTensor]
  rw [Functor.map_add]
  simp only [NatTrans.app_add, Preadditive.add_comp, Preadditive.comp_add]

/-- All ordered cup powers are additive in their arbitrary input class.
Source: Stacks Tag 0FI5, bilinear cup products in the coefficient relation.
Proof: induction on the exponent, using ordinaryFiniteHyperplaneStep_add.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteHyperplaneProduct_add (P : PurityFiniteSetting.{u})
    (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)
    (i : ℕ) (α β : ordinaryFiniteCohomology P T i) (j : ℕ) :
    P.ordinaryFiniteHyperplaneProduct T h i (α + β) j =
      P.ordinaryFiniteHyperplaneProduct T h i α j +
        P.ordinaryFiniteHyperplaneProduct T h i β j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    dsimp only [ordinaryFiniteHyperplaneProduct]
    rw [ih, ordinaryFiniteHyperplaneStep_add]

/-- The exact unsigned projective coefficient formula is additive.
Source: Stacks Tag 0FI5, coefficient expansion in equation-chern-classes.
Proof: distribute pullback, each ordered cup power and the finite sum.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteProjectiveUnsignedCoefficientMap_add (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T : Scheme.{u}} {F : T.Modules}
    (a : T ⟶ Spec (.of P.field.k)) (D : ProjectiveBundleRealization T F)
    (hL : D.L.IsInvertible) (r : ℕ)
    (c d : ∀ i : Fin r, ordinaryFiniteCohomology P T (i.val + 1)) :
    P.ordinaryFiniteProjectiveUnsignedCoefficientMap t a D hL r (c + d) =
      P.ordinaryFiniteProjectiveUnsignedCoefficientMap t a D hL r c +
        P.ordinaryFiniteProjectiveUnsignedCoefficientMap t a D hL r d := by
  simp only [ordinaryFiniteProjectiveUnsignedCoefficientMap, Pi.add_apply,
    ordinaryFiniteCohomologyPullback_add, ordinaryFiniteHyperplaneProduct_add,
    Preadditive.add_comp, Finset.sum_add_distrib]

/-- The signed coefficient map is the unsigned one after the sign involution.
Proof: distribute each integral scalar through pullback and the cup powers.
Source: Stacks Tag 0FI5, equation-chern-classes.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteProjectiveCoefficientMap_eq_unsigned (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T : Scheme.{u}} {F : T.Modules}
    (a : T ⟶ Spec (.of P.field.k)) (D : ProjectiveBundleRealization T F)
    (hL : D.L.IsInvertible) (r : ℕ)
    (c : ∀ i : Fin r, ordinaryFiniteCohomology P T (i.val + 1)) :
    P.ordinaryFiniteProjectiveCoefficientMap t a D hL r c =
      P.ordinaryFiniteProjectiveUnsignedCoefficientMap t a D hL r
        (P.ordinaryFiniteChernSign T r c) := by
  simp only [ordinaryFiniteProjectiveCoefficientMap,
    ordinaryFiniteProjectiveUnsignedCoefficientMap, ordinaryFiniteChernSign,
    ordinaryFiniteCohomologyPullback_zsmul, ordinaryFiniteHyperplaneProduct_zsmul,
    Preadditive.zsmul_comp]

/-- Proof: the sign involution is bijective, so composing the unsigned bijection
with it preserves bijectivity. Source: Stacks Tag 0FI5, alternating Chern relation.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteProjectiveCoefficientMap_bijective_of_unsigned
    (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T : Scheme.{u}} {F : T.Modules}
    (a : T ⟶ Spec (.of P.field.k)) (D : ProjectiveBundleRealization T F)
    (hL : D.L.IsInvertible) (r : ℕ)
    (hb : Function.Bijective (P.ordinaryFiniteProjectiveUnsignedCoefficientMap t a D hL r)) :
    Function.Bijective (P.ordinaryFiniteProjectiveCoefficientMap t a D hL r) := by
  have heq : P.ordinaryFiniteProjectiveCoefficientMap t a D hL r =
      P.ordinaryFiniteProjectiveUnsignedCoefficientMap t a D hL r ∘
        P.ordinaryFiniteChernSign T r := by
    funext c
    exact P.ordinaryFiniteProjectiveCoefficientMap_eq_unsigned t a D hL r c
  rw [heq]
  exact hb.comp (P.ordinaryFiniteChernSign_involutive T r).bijective

/-- Extend positive Chern coordinates by c_0=1 and c_i=0 for i>r.
The dependent case split preserves the actual shifted Tate target in each degree.
Source: Stacks Tag 0FI5, c_0=1 and c_i=0 for i>r
(blueprint: lem-pur-chern-coefficient-assembly). -/
def ordinaryFiniteChernExtend (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r : ℕ)
    (c : ∀ i : Fin r, ordinaryFiniteCohomology P T (i.val + 1)) :
    (i : ℕ) → ordinaryFiniteCohomology P T i
  | 0 => P.ordinaryFiniteCohomologyOne T
  | j + 1 => if h : j < r then c ⟨j, h⟩ else 0

/-- Restriction recovers every positive coordinate, including when r=0.
Source: Stacks Tag 0FI5, definition of the coefficient family.
Proof: the index bound selects the first branch of the extension.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteChernExtend_coordinate (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (r : ℕ)
    (c : ∀ i : Fin r, ordinaryFiniteCohomology P T (i.val + 1)) (i : Fin r) :
    P.ordinaryFiniteChernExtend T r c (i.val + 1) = c i := by
  simp only [ordinaryFiniteChernExtend, dif_pos i.isLt]

/-- Every family with the stipulated zero and tail is the extension of its positive
coordinates. Source: Stacks Tag 0FI5, c_0=1 and above-rank vanishing.
Proof: use c_0=1 at zero; at j+1<=r restriction is unchanged, and at j+1>r both
families vanish. Function extensionality gives equality.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteChernExtend_restrict (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (r : ℕ) (c : ∀ i : ℕ, ordinaryFiniteCohomology P T i)
    (hzero : c 0 = P.ordinaryFiniteCohomologyOne T)
    (htail : ∀ i : ℕ, r < i → c i = 0) :
    P.ordinaryFiniteChernExtend T r (fun i : Fin r ↦ c (i.val + 1)) = c := by
  funext i
  cases i with
  | zero => exact hzero.symm
  | succ j =>
    dsimp only [ordinaryFiniteChernExtend]
    split_ifs with h
    · rfl
    · exact (htail (j + 1) (by omega)).symm

private theorem positivePullback_eq (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (P.diagonalExponent : Γ(Y, ⊤))) (i : ℕ) :
    P.projectiveBundlePositivePullback t f hY i =
      Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t f hY i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change (_ ≪≫ Etale.ordinaryFiniteTensorRightMapIso P.Coefficient X
        (P.projectiveBundlePositivePullback t f hY i) _) =
      (_ ≪≫ Etale.ordinaryFiniteTensorRightMapIso P.Coefficient X
        (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t f hY i) _)
    rw [ih]

/-- The normalized ordered positive coefficient comparison respects composition.
Source: Stacks Tag 03PK, normalization on roots and tensor generators.
Proof: the projective-bundle and vector-integration coefficient comparisons are
the identical recursion, starting with the unit comparison and tensoring the
normalized shifted-line comparison at each successor. Apply the existing proved
composition theorem for that recursion. Only its coefficient calculation is used.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem projectiveBundlePositivePullback_comp (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    (hZ : IsUnit (P.diagonalExponent : Γ(Z, ⊤)))
    (hY : IsUnit (P.diagonalExponent : Γ(Y, ⊤))) (i : ℕ) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g fg hfg).hom.app
        (P.diagonalTwistEtale Z i) ≫
      (Etale.ordinaryFinitePullback P.Coefficient f).map
        (P.projectiveBundlePositivePullback t g hZ i).hom ≫
      (P.projectiveBundlePositivePullback t f hY i).hom =
        (P.projectiveBundlePositivePullback t fg hZ i).hom := by
  rw [positivePullback_eq, positivePullback_eq, positivePullback_eq]
  exact Etale.vectorIntegrationBaseCoefficientPullback_comp P.Coefficient
      P.diagonalExponent P.diagonalExponent_annihilates t f g fg hfg hZ hY i

private theorem normalized_composition
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : D ⥤ E) (G : C ⥤ D) (H : C ⥤ E) (q : H ≅ G ⋙ F)
    {U K : C} {UY KY : D} {UX KX : E}
    (eUg : G.obj U ≅ UY) (eKg : G.obj K ≅ KY)
    (eUf : F.obj UY ≅ UX) (eKf : F.obj KY ≅ KX)
    (eUfg : H.obj U ≅ UX) (eKfg : H.obj K ≅ KX)
    (hU : (q.app U).hom ≫ F.map eUg.hom ≫ eUf.hom = eUfg.hom)
    (hK : (q.app K).hom ≫ F.map eKg.hom ≫ eKf.hom = eKfg.hom)
    (α : U ⟶ K) :
    eUf.inv ≫ F.map (eUg.inv ≫ G.map α ≫ eKg.hom) ≫ eKf.hom =
      eUfg.inv ≫ H.map α ≫ eKfg.hom := by
  have heU : q.app U ≪≫ F.mapIso eUg ≪≫ eUf = eUfg := Iso.ext hU
  have heK : q.app K ≪≫ F.mapIso eKg ≪≫ eKf = eKfg := Iso.ext hK
  rw [← heU, ← heK]
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  have hn : H.map α ≫ (q.app K).hom = (q.app U).hom ≫ F.map (G.map α) :=
    q.hom.naturality α
  rw [reassoc_of% hn, Iso.inv_hom_id_assoc]

/-- The normalized cohomology pullbacks satisfy composition on every class,
with the exact unit and ordered positive-power comparisons of the definition.
Source: Stacks Tags 099V and 03PK, normalized inverse image and finite comparison.
Proof: lift the arbitrary pro-etale class uniquely through comparison at its
bounded-below positive Tate target. The proved comparison square reduces each
pullback to etale inverse image. Naturality of the inverse-image compositor,
unit-comparison composition and positive-power-comparison composition identify
the two normalized etale arrows. Apply exact comparison to their equality.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteCohomologyPullback_comp (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    (a : Z ⟶ Spec (.of P.field.k)) (i : ℕ)
    (α : ordinaryFiniteCohomology P Z i) :
    P.ordinaryFiniteCohomologyPullback t f (P.diagonalExponent_isUnit (g ≫ a)) i
        (P.ordinaryFiniteCohomologyPullback t g (P.diagonalExponent_isUnit a) i α) =
      P.ordinaryFiniteCohomologyPullback t fg (P.diagonalExponent_isUnit a) i α := by
  obtain ⟨β, rfl⟩ := (P.ordinaryFiniteCohomologyComparison_bijective a i).2 α
  rw [ordinaryFiniteCohomologyPullback_comparison,
    ordinaryFiniteCohomologyPullback_comparison, ordinaryFiniteCohomologyPullback_comparison]
  congr 1
  exact normalized_composition
    (Etale.ordinaryFinitePullback P.Coefficient f)
    (Etale.ordinaryFinitePullback P.Coefficient g)
    (Etale.ordinaryFinitePullback P.Coefficient fg)
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g fg hfg)
    (Etale.ordinaryFiniteUnitPullback P.Coefficient g)
    (P.projectiveBundlePositivePullback t g (P.diagonalExponent_isUnit a) i)
    (Etale.ordinaryFiniteUnitPullback P.Coefficient f)
    (P.projectiveBundlePositivePullback t f (P.diagonalExponent_isUnit (g ≫ a)) i)
    (Etale.ordinaryFiniteUnitPullback P.Coefficient fg)
    (P.projectiveBundlePositivePullback t fg (P.diagonalExponent_isUnit a) i)
    (Etale.ordinaryFiniteUnitPullback_comp P.Coefficient f g fg hfg)
    (P.projectiveBundlePositivePullback_comp t f g fg hfg
      (P.diagonalExponent_isUnit a) (P.diagonalExponent_isUnit (g ≫ a)) i) β

/-- The Chern relation reads exactly as the finite coordinate equation.
Source: Stacks Tag 0FI5, equation-chern-classes.
Proof: both sides are the same signed sum, with the same index and degree transport.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteProjectiveRelation_iff_coordinates (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T : Scheme.{u}} {F : T.Modules}
    (a : T ⟶ Spec (.of P.field.k)) (D : ProjectiveBundleRealization T F)
    (hL : D.L.IsInvertible) (r : ℕ)
    (c : ∀ i : ℕ, ordinaryFiniteCohomology P T i) :
    P.ordinaryFiniteProjectiveRelation t a D hL r c ↔
      P.ordinaryFiniteProjectiveCoefficientMap t a D hL r
        (fun i : Fin r ↦ c (i.val + 1)) =
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
        D.A.data.relProj).mapDerivedCategory.map
          (P.projectiveBundleCupPower D.A.data.relProj (P.projectiveBundleChern a D hL) r) :=
  Iff.rfl

/-- Canonical root normalization makes the relation independent of the chosen
transport record. Source: Stacks Tags 03PK and 03Q1, normalization on roots.
Proof: the uniqueness theorem identifies the two normalized transport records;
substitution then identifies the relations without any equality of chosen roots.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteProjectiveRelation_transport (P : PurityFiniteSetting.{u})
    (t t' : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T : Scheme.{u}} {F : T.Modules}
    (a : T ⟶ Spec (.of P.field.k)) (D : ProjectiveBundleRealization T F)
    (hL : D.L.IsInvertible) (r : ℕ)
    (c : ∀ i : ℕ, ordinaryFiniteCohomology P T i) :
    P.ordinaryFiniteProjectiveRelation t a D hL r c ↔
      P.ordinaryFiniteProjectiveRelation t' a D hL r c := by
  have ht := Etale.ordinaryFiniteTwistTransport_unique P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t t'
  subst t'
  rfl

/-- Rank zero requires no projective bundle and has exactly the family (1,0,0,...).
Source: Stacks Tag 0FI5, rank-zero convention.
Proof: extend the empty coordinate family. The relation premise 0<0 is false.
Every other satisfying family agrees at zero and vanishes in every successor degree.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem existsUniqueOrdinaryFiniteChernClasses_rank_zero (P : PurityFiniteSetting.{u})
    {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) (F : T.Modules) :
    ∃! c : ∀ i : ℕ, ordinaryFiniteCohomology P T i,
      P.IsOrdinaryFiniteChernClasses a F 0 c := by
  let c := P.ordinaryFiniteChernExtend T 0 (fun i ↦ Fin.elim0 i)
  refine ⟨c, ⟨rfl, ?_, ?_⟩, ?_⟩
  · intro i hi
    cases i with
    | zero => omega
    | succ j => simp only [c, ordinaryFiniteChernExtend, Nat.not_lt_zero, dite_false]
  · intro h
    omega
  · intro d hd
    exact (P.ordinaryFiniteChernExtend_restrict T 0 d hd.1 hd.2.1).symm.trans
      (by rfl)

/-- A bijective finite coefficient map and invariance under normalized realizations
assemble the unique whole Chern family. Neither input asserts existence of a Chern
family: the first concerns every possible right-hand side, and the second only
transports an equation between projective bundles.
Source: Stacks Tag 0FI5, construction following equation-chern-classes.
Proof: take the preimage of h^r under the finite coefficient map; extend it with
unit at zero and zero above rank. The defining equation survives extension because
it sees only degrees 1,...,r. Invariance gives the equation on every realization
and normalized transport. Conversely restrict any satisfying family to 1,...,r;
its defining equation and injectivity of the coefficient map determine all these
coordinates. Its zero and tail clauses then determine the entire family.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem existsUniqueOrdinaryFiniteChernClasses_of_coordinates
    (P : PurityFiniteSetting.{u}) {T : Scheme.{u}} {F : T.Modules}
    (a : T ⟶ Spec (.of P.field.k)) (r : ℕ) (hr : 0 < r)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ProjectiveBundleRealization T F) (hL : D.L.IsInvertible)
    (hbij : Function.Bijective (P.ordinaryFiniteProjectiveCoefficientMap t a D hL r))
    (hreal : ∀ (c : ∀ i : ℕ, ordinaryFiniteCohomology P T i)
      (D' : ProjectiveBundleRealization T F) (hL' : D'.L.IsInvertible),
      P.ordinaryFiniteProjectiveRelation t a D hL r c →
        P.ordinaryFiniteProjectiveRelation t a D' hL' r c) :
    ∃! c : ∀ i : ℕ, ordinaryFiniteCohomology P T i,
      P.IsOrdinaryFiniteChernClasses a F r c := by
  classical
  let target :=
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
      D.A.data.relProj).mapDerivedCategory.map
        (P.projectiveBundleCupPower D.A.data.relProj (P.projectiveBundleChern a D hL) r)
  obtain ⟨v, hv⟩ := hbij.2 target
  let c := P.ordinaryFiniteChernExtend T r v
  have hcoordinate : (fun i : Fin r ↦ c (i.val + 1)) = v := by
    funext i
    exact P.ordinaryFiniteChernExtend_coordinate T r v i
  have hc : P.ordinaryFiniteProjectiveRelation t a D hL r c := by
    apply (P.ordinaryFiniteProjectiveRelation_iff_coordinates t a D hL r c).2
    rw [hcoordinate]
    exact hv
  refine ⟨c, ⟨rfl, ?_, ?_⟩, ?_⟩
  · intro i hi
    cases i with
    | zero => omega
    | succ j =>
      simp only [c, ordinaryFiniteChernExtend, dif_neg (show ¬j < r by omega)]
  · intro _ D' hL' t'
    exact (P.ordinaryFiniteProjectiveRelation_transport t t' a D' hL' r c).1
      (hreal c D' hL' hc)
  · intro d hd
    have hdrel := hd.2.2 hr D hL t
    have hcoordinates : (fun i : Fin r ↦ d (i.val + 1)) = v := by
      apply hbij.1
      exact ((P.ordinaryFiniteProjectiveRelation_iff_coordinates t a D hL r d).1
        hdrel).trans hv.symm
    calc
      d = P.ordinaryFiniteChernExtend T r (fun i : Fin r ↦ d (i.val + 1)) :=
        (P.ordinaryFiniteChernExtend_restrict T r d hd.1 hd.2.1).symm
      _ = c := congrArg (P.ordinaryFiniteChernExtend T r) hcoordinates

end WeilConjectures.PurityFiniteSetting
