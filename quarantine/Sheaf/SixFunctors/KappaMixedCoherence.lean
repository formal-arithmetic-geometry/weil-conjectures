module

public import Sheaf.SixFunctors.KappaGeometricComparisons
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.PurityKappaStages

/-! # The two orders of canonical coefficient and geometric comparison

Source: Returned Step 11, steps 3--6
(blueprint: def-pur-kappa-mixed-comparison-equations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- Unit or successive finite scalar-change normalization, using the actual scalar
extension unitor or multiplication associator, not arbitrary comparison data.
Source: Returned Step 11, step 3
(blueprint: def-pur-kappa-mixed-comparison-equations). -/
def KappaFiniteCoefficientIdentity (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] : Prop :=
  ∀ (b : Bool)
    (N : proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring),
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber T₀).left N →
    (ProEtale.directImageScalarPullbackIso (RingHom.id P.Ring)
      (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).inv.app N ≫
      (proEtaleConstantRingDerivedPullback P.Ring
        (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).map
          ((ProEtale.scalarExtensionFunctor_identity (P.frobeniusFiber T₀).left).hom.app N) =
    (ProEtale.scalarExtensionFunctor_identity (P.frobeniusFiber T₀).left).hom.app
      ((proEtaleConstantRingDerivedPullback P.Ring
        (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).obj N)


/-- Unit or successive finite scalar-change normalization, using the actual scalar
extension unitor or multiplication associator, not arbitrary comparison data.
Source: Returned Step 11, step 3
(blueprint: def-pur-kappa-mixed-comparison-equations). -/
def KappaFiniteCoefficientComposition (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] : Prop :=
  ∀ (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (hmn : m ≤ P.level) (hrm : r ≤ m) (b : Bool)
    (N : proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring),
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber T₀).left N →
    ((P.finiteReductionSetting m hm).kappaRawReduction r hr hrm
      (P.frobeniusFiber T₀).left).map
        ((P.kappaRawReductionPullback m hm hmn
          (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).hom.app N) ≫
      ((P.finiteReductionSetting m hm).kappaRawReductionPullback r hr hrm
        (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).hom.app
          ((P.kappaRawReduction m hm hmn (P.frobeniusFiber T₀).left).obj N) ≫
      (proEtaleConstantRingDerivedPullback (P.finiteReductionSetting r hr).Ring
        (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).map
          ((ProEtale.scalarExtensionFunctor_composition
            (P.finiteReductionRingHom m hm hmn)
            ((P.finiteReductionSetting m hm).finiteReductionRingHom r hr hrm)
            (P.frobeniusFiber T₀).left).hom.app N) =
    (ProEtale.scalarExtensionFunctor_composition
      (P.finiteReductionRingHom m hm hmn)
      ((P.finiteReductionSetting m hm).finiteReductionRingHom r hr hrm)
      (P.frobeniusFiber T₀).left).hom.app
        ((proEtaleConstantRingDerivedPullback P.Ring
          (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).obj N) ≫
      (ProEtale.directImageScalarPullbackIso
        (((P.finiteReductionSetting m hm).finiteReductionRingHom r hr hrm).comp
          (P.finiteReductionRingHom m hm hmn))
        (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).inv.app N


/-- The two orders use the actual integral coefficient and pullback comparisons.
The left route performs geometric transport then coefficient transport; the right
route performs coefficient transport then geometric transport. The final scalar
pullback comparison identifies their endpoints.
Source: Returned Step 11, steps 3--6
(blueprint: def-pur-kappa-mixed-comparison-equations). -/
def KappaIntegralMixed (P : PurityFiniteSetting.{u})
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic P.coefficients.l) E] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) L] (ι : E →ₐ[Padic P.coefficients.l] L)
    {T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))}
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (u₀ : T'₀ ⟶ T₀) (N : sfIntegralConstructibleCategory P.coefficients.l E (P.frobeniusFiber
      T₀).left) : Prop :=
  (sfConstructibleIntegralScalarExtension 0 P.coefficients.l
      (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) E L ι (P.frobeniusFiber T'₀).left).map
      ((constructibleIntegralPullback P.coefficients.l E (P.frobeniusMap u₀)).map
        ((P.kappaConstructible E T₀).hom.app N)) ≫
    (sfConstructibleIntegralScalarExtension 0 P.coefficients.l
      (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) E L ι (P.frobeniusFiber
        T'₀).left).map ((P.kappaIntegralSquareNat E u₀ true).hom.app N) ≫
    (P.kappaIntegralScalarComparison E L ι (P.frobeniusGaloisMap T'₀)).hom.app
      ((constructibleIntegralPullback P.coefficients.l E (P.frobeniusMap u₀)).obj N) ≫
    (constructibleIntegralPullback P.coefficients.l L
      (P.frobeniusGaloisMap T'₀)).map ((P.kappaIntegralScalarComparison E L ι (P.frobeniusMap
        u₀)).hom.app N) =
  (P.kappaIntegralScalarComparison E L ι (P.frobeniusMap u₀)).hom.app
      ((constructibleIntegralPullback P.coefficients.l E
        (P.frobeniusSchemeMap T₀)).obj N) ≫
    (constructibleIntegralPullback P.coefficients.l L (P.frobeniusMap u₀)).map
      ((P.kappaIntegralScalarComparison E L ι (P.frobeniusSchemeMap T₀)).hom.app N) ≫
    (P.kappaIntegralSquareNat L u₀ false).hom.app ((sfConstructibleIntegralScalarExtension 0
      P.coefficients.l
      (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) E L ι (P.frobeniusFiber
        T₀).left).obj N) ≫
    (P.kappaConstructible L T'₀).hom.app ((constructibleIntegralPullback P.coefficients.l L
      (P.frobeniusMap u₀)).obj ((sfConstructibleIntegralScalarExtension 0 P.coefficients.l
      (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) E L ι (P.frobeniusFiber
        T₀).left).obj N))

/-- The two orders use the actual rational coefficient and pullback comparisons.
The left route performs geometric transport then coefficient transport; the right
route performs coefficient transport then geometric transport. The final scalar
pullback comparison identifies their endpoints.
Source: Returned Step 11, steps 3--6
(blueprint: def-pur-kappa-mixed-comparison-equations). -/
def KappaRationalMixed (P : PurityFiniteSetting.{u})
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic P.coefficients.l) E] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) L] (ι : E →ₐ[Padic P.coefficients.l] L)
    {T'₀ T₀ : Over (Spec (CommRingCat.of P.field.k₀))}
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (u₀ : T'₀ ⟶ T₀) (N : sfRationalConstructibleCategory P.coefficients.l E (P.frobeniusFiber
      T₀).left) : Prop :=
  (sfRationalScalarExtension P.coefficients.l E (P.frobeniusFiber T'₀).left 0
      (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) L ι).map
      ((rationalDerivedPullback P.coefficients.l E (P.frobeniusMap u₀)).map ((P.kappaRational E
        T₀).hom.app N)) ≫
    (sfRationalScalarExtension P.coefficients.l E (P.frobeniusFiber T'₀).left 0
      (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) L ι).map ((P.kappaRationalSquare E
        u₀ true).hom.app N) ≫
    (rationalPullbackScalarComparison P.coefficients.l E L ι (P.frobeniusGaloisMap T'₀)).hom.app
      ((rationalDerivedPullback P.coefficients.l E (P.frobeniusMap u₀)).obj N) ≫
    (rationalDerivedPullback P.coefficients.l L
      (P.frobeniusGaloisMap T'₀)).map ((rationalPullbackScalarComparison P.coefficients.l E L ι
        (P.frobeniusMap u₀)).hom.app N) =
  (rationalPullbackScalarComparison P.coefficients.l E L ι (P.frobeniusMap u₀)).hom.app
      ((rationalDerivedPullback P.coefficients.l E
        (P.frobeniusSchemeMap T₀)).obj N) ≫
    (rationalDerivedPullback P.coefficients.l L (P.frobeniusMap u₀)).map
      ((rationalPullbackScalarComparison P.coefficients.l E L ι (P.frobeniusSchemeMap
      T₀)).hom.app N) ≫
    (P.kappaRationalSquare L u₀ false).hom.app ((sfRationalScalarExtension P.coefficients.l E
      (P.frobeniusFiber T₀).left 0
      (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) L ι).obj N) ≫
    (P.kappaRational L T'₀).hom.app ((rationalDerivedPullback P.coefficients.l L (P.frobeniusMap
      u₀)).obj ((sfRationalScalarExtension P.coefficients.l E (P.frobeniusFiber T₀).left 0
      (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) L ι).obj N))

/-- Unit and successive-extension equations for the specified integral comparisons.
These equations retain the normalized scalar multiplication associator and unitor.
Source: Returned Step 11, steps 3, 5 and 6
(blueprint: def-pur-kappa-mixed-comparison-equations). -/
def KappaIntegralCoefficientLaws (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] : Prop :=
  (∀ (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
      [FiniteDimensional (Padic P.coefficients.l) E] (b : Bool) (N :
        sfIntegralConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left),
      finiteTorConstructibleIntegral P.coefficients.l E (P.frobeniusFiber T₀).left N.obj →
      (P.kappaIntegralScalarComparison E E (AlgHom.id (Padic P.coefficients.l) E) (if b then
        P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).hom.app N ≫
        (constructibleIntegralPullback P.coefficients.l E
          (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).map
            ((sfIntegralScalarUnit P.coefficients.l E (P.frobeniusFiber T₀).left 0
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime))).hom.app N) =
      (sfIntegralScalarUnit P.coefficients.l E (P.frobeniusFiber T₀).left 0
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime))).hom.app
            ((constructibleIntegralPullback P.coefficients.l E
          (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).obj N)) ∧
  (∀ (E L M : Type u) [Field E] [Field L] [Field M]
      [Algebra (Padic P.coefficients.l) E] [Algebra (Padic P.coefficients.l) L]
      [Algebra (Padic P.coefficients.l) M]
      [FiniteDimensional (Padic P.coefficients.l) E]
      [FiniteDimensional (Padic P.coefficients.l) L]
      [FiniteDimensional (Padic P.coefficients.l) M]
      (ι : E →ₐ[Padic P.coefficients.l] L) (η : L →ₐ[Padic P.coefficients.l] M)
      (b : Bool) (N : sfIntegralConstructibleCategory P.coefficients.l E (P.frobeniusFiber
        T₀).left),
      finiteTorConstructibleIntegral P.coefficients.l E (P.frobeniusFiber T₀).left N.obj →
      (sfConstructibleIntegralScalarExtension 0 P.coefficients.l
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) L M η (P.frobeniusFiber
            T₀).left).map ((P.kappaIntegralScalarComparison E L ι (if b then
            P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).hom.app N) ≫
        (P.kappaIntegralScalarComparison L M η (if b then P.frobeniusGaloisMap T₀ else
          P.frobeniusSchemeMap T₀)).hom.app ((sfConstructibleIntegralScalarExtension 0
          P.coefficients.l
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) E L ι (P.frobeniusFiber
            T₀).left).obj N) ≫
        (constructibleIntegralPullback P.coefficients.l M
          (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).map
            ((sfIntegralScalarComp P.coefficients.l E L ι (P.frobeniusFiber T₀).left 0
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) M η).hom.app N) =
      (sfIntegralScalarComp P.coefficients.l E L ι (P.frobeniusFiber T₀).left 0
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) M η).hom.app
            ((constructibleIntegralPullback P.coefficients.l E
          (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).obj N) ≫
        (P.kappaIntegralScalarComparison E M (η.comp ι) (if b then P.frobeniusGaloisMap T₀ else
          P.frobeniusSchemeMap T₀)).hom.app N)

/-- Unit and successive-extension equations for the specified rational comparisons.
These equations retain the normalized scalar multiplication associator and unitor.
Source: Returned Step 11, steps 3, 5 and 6
(blueprint: def-pur-kappa-mixed-comparison-equations). -/
def KappaRationalCoefficientLaws (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] : Prop :=
  (∀ (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
      [FiniteDimensional (Padic P.coefficients.l) E] (b : Bool) (N :
        sfRationalConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left),
      (rationalPullbackScalarComparison P.coefficients.l E E (AlgHom.id (Padic P.coefficients.l)
        E) (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).hom.app N ≫
        (rationalDerivedPullback P.coefficients.l E
          (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).map
            ((sfRationalScalarUnit P.coefficients.l E (P.frobeniusFiber T₀).left 0
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime))).hom.app N) =
      (sfRationalScalarUnit P.coefficients.l E (P.frobeniusFiber T₀).left 0
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime))).hom.app
            ((rationalDerivedPullback P.coefficients.l E
          (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).obj N)) ∧
  (∀ (E L M : Type u) [Field E] [Field L] [Field M]
      [Algebra (Padic P.coefficients.l) E] [Algebra (Padic P.coefficients.l) L]
      [Algebra (Padic P.coefficients.l) M]
      [FiniteDimensional (Padic P.coefficients.l) E]
      [FiniteDimensional (Padic P.coefficients.l) L]
      [FiniteDimensional (Padic P.coefficients.l) M]
      (ι : E →ₐ[Padic P.coefficients.l] L) (η : L →ₐ[Padic P.coefficients.l] M)
      (b : Bool) (N : sfRationalConstructibleCategory P.coefficients.l E (P.frobeniusFiber
        T₀).left),
      (sfRationalScalarExtension P.coefficients.l L (P.frobeniusFiber T₀).left 0
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) M η).map
            ((rationalPullbackScalarComparison P.coefficients.l E L ι (if b then
            P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).hom.app N) ≫
        (rationalPullbackScalarComparison P.coefficients.l L M η (if b then P.frobeniusGaloisMap
          T₀ else P.frobeniusSchemeMap T₀)).hom.app ((sfRationalScalarExtension P.coefficients.l
          E (P.frobeniusFiber T₀).left 0
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) L ι).obj N) ≫
        (rationalDerivedPullback P.coefficients.l M
          (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).map
            ((sfRationalScalarComp P.coefficients.l E L ι (P.frobeniusFiber T₀).left 0
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) M η).hom.app N) =
      (sfRationalScalarComp P.coefficients.l E L ι (P.frobeniusFiber T₀).left 0
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) M η).hom.app
            ((rationalDerivedPullback P.coefficients.l E
          (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).obj N) ≫
        (rationalPullbackScalarComparison P.coefficients.l E M (η.comp ι) (if b then
          P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).hom.app N)


end WeilConjectures.PurityFiniteSetting
