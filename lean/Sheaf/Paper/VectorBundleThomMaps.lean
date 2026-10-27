/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.VectorBundleThomClass
public import Sheaf.Paper.FiniteForwardProductSymmetry
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # Canonical comparisons for vector-bundle Thom inputs

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
`thm-pur-vector-bundle-thom` (blueprint: def-pur-vector-bundle-thom-comparisons).

The isomorphism concerns `vectorBundleThomTau`, not an unspecified identification
of its source and target. Base change uses the normalized proper/open exchange;
direct sums use the forward relative compact-support product. The trace is its inverse.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

variable {P : PurityFiniteSetting.{u}}

/-- Compose the prescribed forward product, projection identification and coefficient
map before specializing a coefficient ring. Every arrow is the published native one.
Source: blueprint proof Step 5 (blueprint: def-pur-vector-bundle-thom-comparisons). -/
def vectorBundleThomProductGeneric (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z B W : Scheme.{u}} {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ B} {g : Z ⟶ B}
    {h : W ⟶ B} [HasCompactification f] [HasCompactification g]
    [HasCompactification q] [HasCompactification (q ≫ g)] [HasCompactification h]
    [QuasiCompact q] [QuasiCompact g] (sq : IsPullback p q f g) (eh : q ≫ g = h)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (Q : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} A)))
    (hMN : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) W
      (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) W).obj
        (L(ProEtale.upperStar (ModuleCat.{u + 1} A) p).obj M)).obj
        (L(ProEtale.upperStar (ModuleCat.{u + 1} A) q).obj N)))
    (μ : ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) W).obj
      (L(ProEtale.upperStar (ModuleCat.{u + 1} A) p).obj M)).obj
      (L(ProEtale.upperStar (ModuleCat.{u + 1} A) q).obj N) ⟶ Q) :=
  ProEtale.finiteForwardProduct A sq M N hMN ≫
  (ProEtale.rightDerivedLowerShriekCongr (ModuleCat.{u + 1} A) eh).hom.app _ ≫
  (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).map μ

/-- Map the specified tensor bifunctor on two arrows, without unfolding its models.
Source: blueprint tensor-morphism convention (blueprint: def-pur-vector-bundle-thom-comparisons). -/
def vectorBundleThomTensorMap {C : Type v} [Category.{w} C] (T : C ⥤ C ⥤ C)
    {L L' M M' : C} (a : L ⟶ L') (b : M ⟶ M') :
    (T.obj L).obj M ⟶ (T.obj L').obj M' :=
  (T.map a).app M ≫ (T.obj L').map b

/-- The twisted, shifted coefficient complex used as input to bundle compact support.
Source: blueprint Q_E notation (blueprint: def-pur-vector-bundle-thom-comparisons). -/
abbrev vectorBundleThomInput (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (r : ℕ) :
    P.FunctorialCupDerived true X :=
  ((P.functorialCupSingle true X).obj (P.functorialCupTwist true X r))⟦2 * (r : ℤ)⟧

/-- Every finite twist in Q_E has bounded-below etale origin, without a chosen witness.
Source: blueprint proof Step 1 (blueprint: def-pur-vector-bundle-thom-comparisons).
Proof: the signed twist is the comparison inverse image of its etale representative.
Exact comparison commutes with degree-zero embedding and shifts; the etale antecedent
is a single sheaf shifted by 2r, hence bounded below. -/
theorem vectorBundleThomInput_origin (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (r : ℕ) :
    ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) X
      (vectorBundleThomInput P X r) := by
  sorry

/-- The root-normalized pullback of Q_X, including the shift comparison.
Source: blueprint proof Step 2, twist identification
(blueprint: def-pur-vector-bundle-thom-comparisons). -/
def vectorBundleThomInputPullback {X Y : Scheme.{u}} (v : Y ⟶ X)
    (aX : X ⟶ Spec (.of P.field.k)) (r : ℕ) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).leftDerivedFunctor.obj
      (vectorBundleThomInput P X r) ≅ vectorBundleThomInput P Y r :=
  (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} P.Coefficient) v).app _ ≪≫
  ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).mapDerivedCategory.commShiftIso
    (2 * (r : ℤ))).app _ ≪≫
  (shiftFunctor _ (2 * (r : ℤ))).mapIso
    (((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).mapDerivedCategorySingleFunctor
      0).app _ ≪≫
    (P.functorialCupSingle true Y).mapIso (P.functorialCupTwistPullback true v aX r))

/-- The canonical pullback of A_B in degree zero.
Source: blueprint proof Step 2, source normalization
(blueprint: def-pur-vector-bundle-thom-comparisons). -/
def vectorBundleThomUnitPullback {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.obj
      ((P.functorialCupSingle true X).obj (P.constant X)) ≅
        (P.functorialCupSingle true Y).obj (P.constant Y) :=
  (ProEtale.singleFunctorCompLeftDerivedUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) g).app _ ≪≫
  (P.functorialCupSingle true Y).mapIso (P.functorialCupConstantPullback true g)

/-- The native coefficient multiplication with its two shifts, before specializing
any sheaf category or coefficient ring. Every arrow is the standard localization map.
Source: blueprint proof Step 5 (blueprint: def-pur-vector-bundle-thom-comparisons). -/
def vectorBundleThomInputProductGeneric (C : Type v) [Category.{w} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (L M N : C) (μ : L ⊗ M ⟶ N) (a b c : ℤ) (h : a + b = c) :
    ((_root_.DerivedCategory.singleFunctor C 0).obj L)⟦a⟧ ⊗
      ((_root_.DerivedCategory.singleFunctor C 0).obj M)⟦b⟧ ⟶
        ((_root_.DerivedCategory.singleFunctor C 0).obj N)⟦c⟧ :=
  (_root_.DerivedCategory.shiftTensorShiftIso C
    ((_root_.DerivedCategory.singleFunctor C 0).obj L)
    ((_root_.DerivedCategory.singleFunctor C 0).obj M) a b).hom ≫
  (shiftFunctor _ (a + b)).map (ProEtale.cupDerivedCoefficientMap μ) ≫
  (eqToIso (congrArg (fun n : ℤ ↦ shiftFunctor (_root_.DerivedCategory C) n) h)).hom.app _

/-- The Hom type for the Thom coefficient multiplication, with one shared tensor
presentation. Source: blueprint Step 5 (blueprint: def-pur-vector-bundle-thom-comparisons). -/
abbrev VectorBundleThomInputProductHom (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (r s : ℕ) :=
  ((ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj
    (vectorBundleThomInput P X r)).obj (vectorBundleThomInput P X s) ⟶
      vectorBundleThomInput P X (r + s)

/-- The normalization predicate for the native root and shifted localization composite.
The heterogeneous equalities compare presentations of the existing native structures.
Source: blueprint proof Step 5 (blueprint: def-pur-vector-bundle-thom-comparisons). -/
structure VectorBundleThomInputProductSpec (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (r s : ℕ)
    (f : VectorBundleThomInputProductHom P X r s) : Prop where
  /-- The exact root and shifted-localization normalization.
  Source: blueprint Step 5 (blueprint: def-pur-vector-bundle-thom-comparisons). -/
  normalized :
    ∃ μ : (P.functorialCupTwist true X r :
        Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) ⊗
        (P.functorialCupTwist true X s) ⟶
          (P.functorialCupTwist true X ((r + s : ℕ) : ℤ)),
      HEq μ ((P.functorialCupTwistProduct true X aX r s).hom ≫
        eqToHom (congrArg (P.functorialCupTwist true X) (Int.natCast_add r s).symm)) ∧
      HEq f (vectorBundleThomInputProductGeneric
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
        (P.functorialCupTwist true X r) (P.functorialCupTwist true X s)
        (P.functorialCupTwist true X ((r + s : ℕ) : ℤ)) μ
        (2 * (r : ℤ)) (2 * (s : ℤ)) (2 * ((r + s : ℕ) : ℤ))
        ((mul_add 2 (r : ℤ) (s : ℤ)).symm.trans
          (congrArg (fun t : ℤ ↦ 2 * t) (Int.natCast_add r s).symm)))

/-- The native root product has a unique presentation on the published Thom inputs.
Both ordinary root multiplication and the entire shifted derived map are fixed.
Source: blueprint proof Step 5 (blueprint: def-pur-vector-bundle-thom-comparisons).
Proof: the selected sheaf tensor is the native sheaf tensor and the selected single
functor is the native localization embedding. Transport the root multiplication
through these presentation identities and apply the displayed generic construction.
This gives existence. Each heterogeneous equality fixes its map uniquely, giving
uniqueness of the resulting shifted map, including zero ranks. -/
theorem existsUnique_vectorBundleThomInputProduct (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of P.field.k)) (r s : ℕ) :
    ∃! f : VectorBundleThomInputProductHom P X r s,
      VectorBundleThomInputProductSpec P X aX r s f := by
  sorry

/-- The canonical multiplication Q_X(r) tensor Q_X(s) to Q_X(r+s), using the
native even-shift comparison and the root-normalized finite twist product.
Both shifts are even, so either Koszul ordering gives this same map.
Source: blueprint proof Step 5 (blueprint: def-pur-vector-bundle-thom-comparisons). -/
def vectorBundleThomInputProduct (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (r s : ℕ) :
    VectorBundleThomInputProductHom P X r s :=
  (existsUnique_vectorBundleThomInputProduct P X aX r s).exists.choose

variable {B : Scheme.{u}} {hB : B ⟶ Spec (.of P.field.k)}
  [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}

section BaseChange

variable {B' : Scheme.{u}} (g : B' ⟶ B)
  [IsSeparated (g ≫ hB)] [LocallyOfFiniteType (g ≫ hB)] [QuasiCompact (g ≫ hB)]
  (V : PurityVectorBundle P B hB r) (V' : PurityVectorBundle P B' (g ≫ hB) r)
  (v : V'.E ⟶ V.E) (sq : IsPullback v V'.p V.p g)

/-- A Cartesian map identifies the pulled-back bundle, rather than translating its
zero section, when it is induced by an isomorphism of the generator modules.
The displayed equality specifies that induced map on every symmetric-algebra generator.
Source: blueprint base change of the vector bundle
(blueprint: def-pur-vector-bundle-thom-comparisons). -/
def VectorBundleThomBaseChange : Prop :=
  ∃ e : (Scheme.Modules.tensorPullback g).obj V.𝓔 ≅ V'.𝓔,
    ∀ (U : B.Opens) (m : V.𝓔.val.obj (op U)),
      V'.E.presheaf.map
        (eqToHom (congrArg (fun f ↦ op (f ⁻¹ᵁ U)) sq.w))
        (v.c.app (op (V.p ⁻¹ᵁ U)) (vectorBundleGenerator V U m)) =
      vectorBundleGenerator V' (g ⁻¹ᵁ U)
        (e.hom.val.app (op (g ⁻¹ᵁ U))
          (Scheme.Modules.tensorPullbackSection g V.𝓔 U m))

/-- The proper/open exchange, followed by the canonical twist pullback and the
normalized comparison to the chosen compactification of pi'. Every factor is prescribed.
Source: blueprint proof Step 2 (blueprint: def-pur-vector-bundle-thom-comparisons). -/
def vectorBundleThomBaseChangeMap :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.obj
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).obj
        (vectorBundleThomInput P V.E r)) ⟶
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V'.p).obj
        (vectorBundleThomInput P V'.E r) :=
  (ProEtale.rightDerivedLowerShriekBaseChangeMap
    (ModuleCat.{u + 1} P.Coefficient) sq).app _ ≫
  (ProEtale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} P.Coefficient)
    ((HasCompactification.compactification V.p).ofIsPullback sq)).map
      (vectorBundleThomInputPullback v (V.p ≫ hB) r).hom ≫
  (ProEtale.finiteForwardCompactificationComparison P.Coefficient
    ((HasCompactification.compactification V.p).ofIsPullback sq)
    (HasCompactification.compactification V'.p)).hom.app
      ⟨_, vectorBundleThomInput_origin P V'.E r⟩

end BaseChange

section DirectSum

variable {s : ℕ} (V : PurityVectorBundle P B hB (r + s))
  (V₁ : PurityVectorBundle P B hB r) (V₂ : PurityVectorBundle P B hB s)
  (e : V.𝓔 ≅ V₁.𝓔 ⨯ V₂.𝓔)

/-- The generator-normalized direct-sum projections exhibit the fibre product;
the second projection has the compact-support domain required by the forward product.
Source: blueprint proof Step 5 (blueprint: def-pur-vector-bundle-thom-comparisons).
Proof: in simultaneous affine frames the generator inclusions give the two polynomial
coordinate projections. Sym(M1 plus M2)=Sym(M1) tensor Sym(M2), so the square is
Cartesian. The second projection is a base change of the first bundle projection,
hence quasi-compact and compactifiable. These affine descriptions glue. -/
theorem vectorBundleThomSum_geometry :
    IsPullback (vectorBundleThomProjection₁ V V₁ V₂ e)
      (vectorBundleThomProjection₂ V V₁ V₂ e) V₁.p V₂.p ∧
    QuasiCompact (vectorBundleThomProjection₂ V V₁ V₂ e) ∧
    HasCompactification (vectorBundleThomProjection₂ V V₁ V₂ e) := by
  sorry

/-- The product structure map is the specified projection of the sum bundle.
Source: blueprint E1 plus E2 = E1 times_B E2 (blueprint: def-pur-vector-bundle-thom-comparisons).
Proof: the linear-map generator prescription is over B, so its stored over-base
identity gives precisely this equality. -/
theorem vectorBundleThomSum_projection_comp :
    vectorBundleThomProjection₂ V V₁ V₂ e ≫ V₂.p = V.p := by
  sorry

/-- The composite product projection is compactifiable because it is the bundle projection.
Source: blueprint proof Step 5 (blueprint: def-pur-vector-bundle-thom-comparisons).
Proof: transport vectorBundleThom_compactifiable along vectorBundleThomSum_projection_comp. -/
theorem vectorBundleThomSum_composite_compactifiable :
    HasCompactification (vectorBundleThomProjection₂ V V₁ V₂ e ≫ V₂.p) := by
  sorry

/-- The exterior tensor of Q1 and Q2, on the actual total space of the sum.
Source: blueprint proof Step 5 (blueprint: def-pur-vector-bundle-thom-comparisons). -/
abbrev vectorBundleThomSumExternal : P.FunctorialCupDerived true V.E :=
  ((ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) V.E).obj
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (vectorBundleThomProjection₁ V V₁ V₂ e)).leftDerivedFunctor.obj
        (vectorBundleThomInput P V₁.E r))).obj
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (vectorBundleThomProjection₂ V V₁ V₂ e)).leftDerivedFunctor.obj
        (vectorBundleThomInput P V₂.E s))

/-- The exterior tensor has bounded-below etale origin on the sum bundle.
Source: blueprint proof Steps 1 and 5 (blueprint: def-pur-vector-bundle-thom-comparisons).
Proof: inverse image commutes with the etale comparison and signed finite twists.
The twists are flat rank-one sheaves, so their derived tensor is their ordinary
rank-one tensor, with shift 2r+2s. It is the comparison inverse image of the same
bounded etale complex, including when a summand has rank zero. -/
theorem vectorBundleThomSumExternal_origin :
    ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) V.E
      (vectorBundleThomSumExternal V V₁ V₂ e) := by
  sorry

/-- The coefficient map Q1 exterior Q2 to Q_E is the normalized signed twist product.
It pulls back the two root lines, applies the native even-shift comparison, and
multiplies the finite twist lines. The final equalities are the integer rank and degree identities.
Source: blueprint proof Step 5 (blueprint: def-pur-vector-bundle-thom-comparisons). -/
def vectorBundleThomSumCoefficient :
    vectorBundleThomSumExternal V V₁ V₂ e ⟶ vectorBundleThomInput P V.E (r + s) :=
  vectorBundleThomTensorMap
    (ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) V.E)
    (vectorBundleThomInputPullback (vectorBundleThomProjection₁ V V₁ V₂ e)
      (V₁.p ≫ hB) r).hom
    (vectorBundleThomInputPullback (vectorBundleThomProjection₂ V V₁ V₂ e)
      (V₂.p ≫ hB) s).hom ≫
  vectorBundleThomInputProduct P V.E (V.p ≫ hB) r s

end DirectSum

end WeilConjectures.PurityFiniteSetting
