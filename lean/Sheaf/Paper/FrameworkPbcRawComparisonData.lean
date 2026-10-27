module

public import Sheaf.Paper.FrameworkPbcComparisonData
public import Sheaf.Paper.PbcRationalTransport

/-! # Raw localization of the normalized framework/PBC comparisons

Source: purity-transport coefficient-change proof, raw rationalization clause
(blueprint: def-pur-framework-pbc-raw-comparison-data).
Objects stay integral representatives, and every map is fixed on pure tensors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrameworkPbc
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The restricted coefficient equivalence and its actual raw scalar localization.
The ambient object and arrow equalities fix integral coefficient relabeling;
the pure-tensor equation fixes every denominator of the rational equivalence.
Source: Stacks 099N and blueprint raw-rationalization clause
(blueprint: def-pur-framework-pbc-raw-comparison-data). -/
structure Coefficient (W : Scheme.{u}) where
  integral : sfIntegralConstructibleCategory l E W ≌
    PbcBoundedConstructibleComplete W (pbcIntegralDatum l E)
  objects : ∀ K : sfIntegralConstructibleCategory l E W,
    (integral.functor.obj K).obj = (integralDetailedTransport W l E).obj K.obj
  maps : ∀ (K H : sfIntegralConstructibleCategory l E W) (f : K ⟶ H),
    HEq (integral.functor.map f).hom ((integralDetailedTransport W l E).map f.hom)
  rational : sfRationalConstructibleCategory l E W ≌
    PbcRationalCategory W (pbcIntegralDatum l E) (pbcUniformizer l E)
  rational_objects : ∀ K : sfRationalConstructibleCategory l E W,
    rational.functor.obj K = ⟨integral.functor.obj K.obj⟩
  rational_maps : ∀ (K H : sfIntegralConstructibleCategory l E W)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)) (f : K ⟶ H),
    HEq (rational.functor.map
      (fdRawTensor (Padic.coefficientExtensionUniformizer l E) a f :
        (sfRationalConstructibleLocalization l E W).obj K ⟶
          (sfRationalConstructibleLocalization l E W).obj H))
      (fdRawTensor (pbcUniformizer l E)
        ((pbcRationalCoefficientEquiv l E).symm (sfRationalCoefficientEquiv l E a))
        (integral.functor.map f) :
          (pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).obj
            (integral.functor.obj K) ⟶
          (pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).obj
            (integral.functor.obj H))

/-- The raw pullback comparison is exactly the localization of pi, on the actual
restricted PBC pullback. Its preservation field is a conclusion of the main theorem.
Source: Stacks 099N and blueprint raw-rationalization clause
(blueprint: def-pur-framework-pbc-raw-comparison-data). -/
structure RawPullback {X Y : Scheme.{u}} (h : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (cX : Coefficient l E X) (cY : Coefficient l E Y) (p : Pullback l E h) where
  preserves : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((pbcActualCompletedPull h (pbcIntegralDatum l E)).obj K.obj)
  integral : constructibleIntegralPullback l E h ⋙ cX.integral.functor ≅
    cY.integral.functor ⋙ pbcConditionalIntegral (pbcIntegralDatum l E)
      (pbcActualCompletedPull h (pbcIntegralDatum l E)) preserves
  integral_components : ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq (integral.hom.app K).hom (p.pi.hom.app K)
  rational : rationalDerivedPullback l E h ⋙ cX.rational.functor ≅
    cY.rational.functor ⋙ pbcConditionalRational (pbcIntegralDatum l E)
      (pbcActualCompletedPull h (pbcIntegralDatum l E)) preserves (pbcUniformizer l E)
  rational_components : ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq (rational.hom.app ((sfRationalConstructibleLocalization l E Y).obj K))
      ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map
        (integral.hom.app K))

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The scalar comparison j with all raw denominators, including identity embeddings.
Its rational target is the recorded ordinary PBC scalar extension.
Source: Stacks 099N and blueprint raw-rationalization clause
(blueprint: def-pur-framework-pbc-raw-comparison-data). -/
structure RawScalar (W : Scheme.{u}) [IsNoetherian W]
    (hdim : ∃ n : ℕ, topologicalKrullDim W ≤ n)
    (hinv : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (cE : Coefficient l E W) (cL : Coefficient l L W) where
  integral : integralComparisonConstructibleScalar l E L ι W ⋙ cL.integral.functor ≅
    cE.integral.functor ⋙ pbcEmbeddingIntegralTensor l E L ι W hdim hinv
  integral_components : ∀ K : sfIntegralConstructibleCategory l E W,
    HEq (integral.hom.app K).hom (scalarComponent l E L ι W K).hom
  rational : sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙ cL.rational.functor ≅
    cE.rational.functor ⋙ pbcRationalScalarExtension l E L ι W hdim hinv
  rational_components : ∀ K : sfIntegralConstructibleCategory l E W,
    HEq (rational.hom.app ((sfRationalConstructibleLocalization l E W).obj K))
      ((pbcRationalization W (pbcIntegralDatum l L) (pbcUniformizer l L)).map
        (integral.hom.app K))

/-- The raw tensor is the bilinear extension of the actual restricted completed tensor;
tau is tensored with one. The formula determines its map on every pair of morphisms.
Source: Stacks 07A4 and blueprint raw-rationalization clause
(blueprint: def-pur-framework-pbc-raw-comparison-data). -/
structure RawTensor (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (c : Coefficient l E W) (t : Tensor l E W) where
  preserves : ∀ M N : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E),
    PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E)
      ((tensor l E W).obj (M.obj, N.obj))
  integral : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E) ×
    PbcBoundedConstructibleComplete W (pbcIntegralDatum l E) ⥤
      PbcBoundedConstructibleComplete W (pbcIntegralDatum l E)
  integral_objects : ∀ M N, (integral.obj (M, N)).obj =
    (tensor l E W).obj (M.obj, N.obj)
  integral_maps : ∀ M N M' N' (f : M ⟶ M') (g : N ⟶ N'),
    HEq (integral.map (Prod.mkHom f g)).hom
      ((tensor l E W).map (Prod.mkHom f.hom g.hom))
  tau : constructibleIntegralTensor l E W ⋙ c.integral.functor ≅
    (c.integral.functor.prod c.integral.functor) ⋙ integral
  tau_components : ∀ M N, HEq (tau.hom.app (M, N)).hom (t.tau.hom.app (M.obj, N.obj))
  rational : PbcRationalCategory W (pbcIntegralDatum l E) (pbcUniformizer l E) ×
    PbcRationalCategory W (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
      PbcRationalCategory W (pbcIntegralDatum l E) (pbcUniformizer l E)
  rational_objects : ∀ M N, rational.obj (M, N) = ⟨integral.obj (M.obj, N.obj)⟩
  rational_maps : ∀ M N M' N' (f : M ⟶ M') (g : N ⟶ N')
    (a b : Localization.Away (pbcUniformizer l E)),
    HEq (rational.map (Prod.mkHom
      (fdRawTensor (pbcUniformizer l E) a f :
        (pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).obj M ⟶
          (pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).obj M')
      (fdRawTensor (pbcUniformizer l E) b g :
        (pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).obj N ⟶
          (pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).obj N')))
      (fdRawTensor (pbcUniformizer l E) (a * b) (integral.map (Prod.mkHom f g)) :
        (pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).obj
          (integral.obj (M, N)) ⟶
        (pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).obj
          (integral.obj (M', N')))
  rational_tau : rationalDerivedTensor l E W ⋙ c.rational.functor ≅
    (c.rational.functor.prod c.rational.functor) ⋙ rational
  rational_tau_components : ∀ M N,
    HEq (rational_tau.hom.app
      ((sfRationalConstructibleLocalization l E W).obj M,
        (sfRationalConstructibleLocalization l E W).obj N))
      ((pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).map
        (tau.hom.app (M, N)))

end WeilConjectures.FrameworkPbc
