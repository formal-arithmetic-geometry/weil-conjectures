module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.CompactificationCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.SixFunctors.FrobeniusSquareCartesian
import Sheaf.CategoryTheory.MateIsoAlongEquivalences

/-! # Finite Frobenius exchange and the chosen compact inverse

Source: Deligne, Weil II, (1.1.7), (1.1.10)--(1.1.11), (1.1.14), pp. 150--153;
agent-written ambient finite-coefficient verification of the transport arrows
(blueprint: lem-weil-frobenius-finite-exchange-inverse).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.FrobeniusExchange

/-- The recorded canonical open-square exchange for this very compactification,
with its inherited open-immersion proof supplied explicitly.
Source: Deligne, Weil II, (1.1.14), and the open-square construction of
`def-weil-frobenius-square-exchange`, item 2
(blueprint: lem-weil-frobenius-finite-exchange-inverse). -/
def frobeniusFiniteOpenExchange (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) (c₀ : Compactification f₀.left) :=
  letI := (geometricCompactification_properties D f₀ c₀).1
  constantOpenSquareExchange l E n hn (galois D X₀)
    (fiberMap D (zlCompactificationOpen D f₀ c₀))
    (fiberMap D (zlCompactificationOpen D f₀ c₀))
    (galois D (zlCompactificationMiddle D f₀ c₀))
    (D.frobenius_square_cartesian _ _ (zlCompactificationOpen D f₀ c₀)).2.2.2.2.2.1

/-- The specified compactification comparison on the actual geometric fiber.
Only inherited proof instances are supplied; the comparison is the published
common-refinement-normalized comparison, with its original witnesses.
Source: `prop-compactification-coherence-detailed` and its intrinsic realization
in `def-weil-frobenius-square-exchange`, item 2
(blueprint: lem-weil-frobenius-finite-exchange-inverse). -/
def frobeniusFiniteComparison (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (c d : Compactification (fiberMap D f₀)) :=
  letI : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).1
  letI : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).2
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  letI := (fiberMap_properties D f₀).1
  letI := (fiberMap_properties D f₀).2.1
  letI := (fiberMap_properties D f₀).2.2
  intrinsicCompactificationComparison D.k l (zlClosurePrimeUnit D l hl)
    E n hn (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
    (fiberMap D f₀) c d

private theorem equivalenceOfInverse {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (H : D ⥤ C) (a : F ⋙ H ≅ 𝟭 C) (b : H ⋙ F ≅ 𝟭 D) :
    F.IsEquivalence :=
  (CategoryTheory.Equivalence.mk F H a.symm b).isEquivalence_functor

private theorem intrinsicPullbackEquivalence (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (sfIntrinsicDerivedPullback A g).IsEquivalence := by
  let F := sfIntrinsicDerivedPullback A g
  let H := sfIntrinsicDerivedPullback A (inv g)
  let a : F ⋙ H ≅ 𝟭 _ :=
    (sfIntrinsicDerivedPullbackComp A (inv g) g).symm ≪≫
      eqToIso (congrArg (sfIntrinsicDerivedPullback A) (IsIso.inv_hom_id g)) ≪≫
      sfIntrinsicDerivedPullbackId A Y
  let b : H ⋙ F ≅ 𝟭 _ :=
    (sfIntrinsicDerivedPullbackComp A g (inv g)).symm ≪≫
      eqToIso (congrArg (sfIntrinsicDerivedPullback A) (IsIso.hom_inv_id g)) ≪≫
      sfIntrinsicDerivedPullbackId A X
  exact equivalenceOfInverse F H a b

private theorem tensorExchangeIso (A : Type u) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (gX : X' ⟶ X) (gY : Y' ⟶ Y) [IsIso gX] [IsIso gY]
    (w : gX ≫ f = f' ≫ gY) : IsIso (finiteTensorExchange A f f' gX gY w) := by
  let := intrinsicPullbackEquivalence A gX
  let := intrinsicPullbackEquivalence A gY
  have := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction
    (sfIntrinsicConstantModuleAdjunction f' A).mapDerivedCategoryRightDerivedAdjunction
    (sfIntrinsicDerivedPullback A gY) (sfIntrinsicDerivedPullback A gX)
    ((sfIntrinsicDerivedPullbackComp A f' gY).symm ≪≫
      eqToIso (congrArg (fun h ↦ sfIntrinsicDerivedPullback A h) w.symm) ≪≫
      sfIntrinsicDerivedPullbackComp A gX f)
  dsimp only [finiteTensorExchange, finiteExchange]
  infer_instance

private theorem inverseComposite {C : Type*} [Category C] {W X Y Z : C}
    (a : W ⟶ X) (ai : X ⟶ W) (b : X ⟶ Y) (bi : Y ⟶ X)
    (c : Y ⟶ Z) (ci : Z ⟶ Y)
    (ha : a ≫ ai = 𝟙 _) (hai : ai ≫ a = 𝟙 _)
    (hb : b ≫ bi = 𝟙 _) (hbi : bi ≫ b = 𝟙 _)
    (hc : c ≫ ci = 𝟙 _) (hci : ci ≫ c = 𝟙 _) :
    ∃ e : W ≅ Z, e.hom = a ≫ b ≫ c ∧ e.inv = ci ≫ bi ≫ ai := by
  refine ⟨⟨a ≫ b ≫ c, ci ≫ bi ≫ ai, ?_, ?_⟩, rfl, rfl⟩
  · simp only [Category.assoc, ← Category.assoc c ci, hc, Category.id_comp,
      ← Category.assoc b bi, hb, ha]
  · simp only [Category.assoc, ← Category.assoc ai a, hai, Category.id_comp,
      ← Category.assoc bi b, hbi, hci]

private theorem transportAssembly (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (c d : Compactification f)
    (k : sfIntrinsicCompactSupport c A ⋙ proEtaleConstantRingDerivedPullback A gY ≅
      proEtaleConstantRingDerivedPullback A gX ⋙ sfIntrinsicCompactSupport c A)
    (t : sfIntrinsicCompactSupport c A ⋙ proEtaleConstantRingDerivedPullback A gY ⟶
      proEtaleConstantRingDerivedPullback A gX ⋙ sfIntrinsicCompactSupport c A)
    (hk : k.hom = t)
    (C : intrinsicOriginCandidate A d ≅ intrinsicOriginCandidate A c)
    (O : CompactOriginCategory A X) :
    ∃ e : (proEtaleConstantRingDerivedPullback A gY).obj
          ((intrinsicOriginCandidate A d).obj O) ≅
        (intrinsicOriginCandidate A d).obj (pulledCompactOrigin A gX O),
      e.hom = (proEtaleConstantRingDerivedPullback A gY).map (C.hom.app O) ≫
        t.app O.K ≫ C.inv.app (pulledCompactOrigin A gX O) ∧
      e.inv = C.hom.app (pulledCompactOrigin A gX O) ≫ k.inv.app O.K ≫
        (proEtaleConstantRingDerivedPullback A gY).map (C.inv.app O) := by
  let G := proEtaleConstantRingDerivedPullback A gY
  let O' := pulledCompactOrigin A gX O
  refine inverseComposite (G.map (C.hom.app O)) (G.map (C.inv.app O))
    (t.app O.K) (k.inv.app O.K) (C.inv.app O') (C.hom.app O') ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← G.map_comp, C.hom_inv_id_app, G.map_id]
  · rw [← G.map_comp, C.inv_hom_id_app, G.map_id]
  · rw [← hk]
    exact k.hom_inv_id_app O.K
  · rw [← hk]
    exact k.inv_hom_id_app O.K
  · exact C.inv_hom_id_app O'
  · exact C.hom_inv_id_app O'

private theorem finiteTransport
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (c₀ : Compactification f₀.left) :
    ∀ (compactIso :
      @sfIntrinsicCompactSupport.{u} _ _ _ (geometricCompactification D f₀ c₀)
          (Padic.coefficientExtensionRing l E n) _
          (Padic.finite_coefficientExtensionRing l E n hn) ⋙
          proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n)
            (galois D Y₀) ≅
        proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n)
            (galois D X₀) ⋙
          @sfIntrinsicCompactSupport.{u} _ _ _ (geometricCompactification D f₀ c₀)
            (Padic.coefficientExtensionRing l E n) _
            (Padic.finite_coefficientExtensionRing l E n hn)),
      compactIso.hom = frobeniusCompactFinite D f₀ c₀ l E n hn →
      ∀ (d : Compactification (fiberMap D f₀))
          (O : @CompactOriginCategory.{u} (Padic.coefficientExtensionRing l E n) _
            (Padic.finite_coefficientExtensionRing l E n hn) (D.geometricFiber X₀).left),
        ∃ transportedIso : _ ≅ _,
          transportedIso.hom =
            (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n)
              (galois D Y₀)).map
                ((frobeniusFiniteComparison D l hl E n hn f₀ d
                  (geometricCompactification D f₀ c₀)).hom.app O) ≫
            (frobeniusCompactFinite D f₀ c₀ l E n hn).app
              (@CompactOrigin.K.{u} (Padic.coefficientExtensionRing l E n) _
                (Padic.finite_coefficientExtensionRing l E n hn) _ O) ≫
            (frobeniusFiniteComparison D l hl E n hn f₀ d
              (geometricCompactification D f₀ c₀)).inv.app
                (@pulledCompactOrigin.{u} (Padic.coefficientExtensionRing l E n) _
                  (Padic.finite_coefficientExtensionRing l E n hn) _ (galois D X₀) O) ∧
          transportedIso.inv =
            (frobeniusFiniteComparison D l hl E n hn f₀ d
              (geometricCompactification D f₀ c₀)).hom.app
                (@pulledCompactOrigin.{u} (Padic.coefficientExtensionRing l E n) _
                  (Padic.finite_coefficientExtensionRing l E n hn) _ (galois D X₀) O) ≫
            compactIso.inv.app
              (@CompactOrigin.K.{u} (Padic.coefficientExtensionRing l E n) _
                (Padic.finite_coefficientExtensionRing l E n hn) _ O) ≫
            (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n)
              (galois D Y₀)).map
                ((frobeniusFiniteComparison D l hl E n hn f₀ d
                  (geometricCompactification D f₀ c₀)).inv.app O) := by
  intro compactIso hc d O
  let A := Padic.coefficientExtensionRing l E n
  let : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  exact transportAssembly A (fiberMap D f₀) (galois D X₀) (galois D Y₀)
    (geometricCompactification D f₀ c₀) d compactIso
    (frobeniusCompactFinite D f₀ c₀ l E n hn) hc
    (frobeniusFiniteComparison D l hl E n hn f₀ d
      (geometricCompactification D f₀ c₀)) O

/-- The specified direct and chosen-compactification exchanges are natural isomorphisms
on the full unbounded finite-coefficient categories. The compact inverse reverses the
proper mate and the proper image of the canonical open-square exchange. On retained
etale-origin witnesses, conjugation by the specified compactification comparison has
the displayed inverse. The compactification is retained; no independence is asserted.

Source: Deligne, Weil II, (1.1.7), (1.1.10)--(1.1.11), (1.1.14), pp. 150--153;
agent-written finite-coefficient verification of the two transport arrows
(blueprint: lem-weil-frobenius-finite-exchange-inverse).

Proof:
1. The geometric Frobenius arrows are scheme isomorphisms. Intrinsic derived
   pullback along their scheme inverses, with the existing composition and
   identity isomorphisms, exhibits their intrinsic pullbacks as equivalences.
2. Apply lem-weil-mate-iso-along-equivalences to the intrinsic pullback/direct
   image adjunctions and the specified pullback compositor. Conjugation by the
   tensor pullback models gives the recorded direct and proper exchange arrows.
3. Whisker the proper mate by the open functor and then whisker the canonical
   open-square exchange by the proper image. This composite has the prescribed
   hom; its inverse reverses the two factors, giving the displayed formula.
4. The specified compactification comparison already is an isomorphism on the
   witnessed category. Evaluate it on O and its constructed pulled witness.
   Conjugate the compact exchange by these comparisons and derived pullback.
   The inverse reverses the three factors; both composites cancel by the
   isomorphism laws and functoriality. -/
theorem frobenius_finite_exchange_inverse
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (c₀ : Compactification f₀.left) :
    ∃ (directIso : _ ≅ _) (properIso : _ ≅ _) (compactIso : _ ≅ _),
      directIso.hom = frobeniusDirectFinite D l E n hn f₀ ∧
      properIso.hom = frobeniusDirectFinite D l E n hn
        (zlCompactificationProper D f₀ c₀) ∧
      compactIso.hom = frobeniusCompactFinite D f₀ c₀ l E n hn ∧
      (∀ K : proEtaleDerivedCategory (D.geometricFiber X₀).left
          (Padic.coefficientExtensionRing l E n),
        compactIso.inv.app K =
          (proEtaleConstantDerivedDirectImage
            (fiberMap D (zlCompactificationProper D f₀ c₀))
            (Padic.coefficientExtensionRing l E n)).map
              ((frobeniusFiniteOpenExchange D l E n hn f₀ c₀).inv.app K) ≫
            properIso.inv.app
              ((@sfIntrinsicDerivedOpen.{u} (Padic.coefficientExtensionRing l E n) _
                (Padic.finite_coefficientExtensionRing l E n hn) _ _
                (fiberMap D (zlCompactificationOpen D f₀ c₀))
                (geometricCompactification_properties D f₀ c₀).1).obj K)) ∧
      (∀ (d : Compactification (fiberMap D f₀))
          (O : @CompactOriginCategory.{u} (Padic.coefficientExtensionRing l E n) _
            (Padic.finite_coefficientExtensionRing l E n hn) (D.geometricFiber X₀).left),
        ∃ transportedIso : _ ≅ _,
          transportedIso.hom =
            (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n)
              (galois D Y₀)).map
                ((frobeniusFiniteComparison D l hl E n hn f₀ d
                  (geometricCompactification D f₀ c₀)).hom.app O) ≫
            (frobeniusCompactFinite D f₀ c₀ l E n hn).app
              (@CompactOrigin.K.{u} (Padic.coefficientExtensionRing l E n) _
                (Padic.finite_coefficientExtensionRing l E n hn) _ O) ≫
            (frobeniusFiniteComparison D l hl E n hn f₀ d
              (geometricCompactification D f₀ c₀)).inv.app
                (@pulledCompactOrigin.{u} (Padic.coefficientExtensionRing l E n) _
                  (Padic.finite_coefficientExtensionRing l E n hn) _ (galois D X₀) O) ∧
          transportedIso.inv =
            (frobeniusFiniteComparison D l hl E n hn f₀ d
              (geometricCompactification D f₀ c₀)).hom.app
                (@pulledCompactOrigin.{u} (Padic.coefficientExtensionRing l E n) _
                  (Padic.finite_coefficientExtensionRing l E n hn) _ (galois D X₀) O) ≫
            compactIso.inv.app
              (@CompactOrigin.K.{u} (Padic.coefficientExtensionRing l E n) _
                (Padic.finite_coefficientExtensionRing l E n hn) _ O) ≫
            (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n)
              (galois D Y₀)).map
                ((frobeniusFiniteComparison D l hl E n hn f₀ d
                  (geometricCompactification D f₀ c₀)).inv.app O)) := by
  let A := Padic.coefficientExtensionRing l E n
  let : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let : IsIso (galois D X₀) :=
    inferInstanceAs (IsIso (D.geometricFrobenius X₀).hom)
  let : IsIso (galois D Y₀) :=
    inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  let : IsIso (galois D (zlCompactificationMiddle D f₀ c₀)) :=
    inferInstanceAs (IsIso (D.geometricFrobenius (zlCompactificationMiddle D f₀ c₀)).hom)
  have : IsIso (frobeniusDirectFinite D l E n hn f₀) :=
    tensorExchangeIso A _ _ _ _ _
  have : IsIso (frobeniusDirectFinite D l E n hn
      (zlCompactificationProper D f₀ c₀)) := tensorExchangeIso A _ _ _ _ _
  let directIso := asIso (frobeniusDirectFinite D l E n hn f₀)
  let properIso := asIso (frobeniusDirectFinite D l E n hn
    (zlCompactificationProper D f₀ c₀))
  let := (geometricCompactification_properties D f₀ c₀).1
  let J := sfIntrinsicDerivedOpen A (fiberMap D (zlCompactificationOpen D f₀ c₀))
  let P := proEtaleConstantDerivedDirectImage
    (fiberMap D (zlCompactificationProper D f₀ c₀)) A
  let compactConstruction := Functor.isoWhiskerLeft J properIso ≪≫
    Functor.isoWhiskerRight (frobeniusFiniteOpenExchange D l E n hn f₀ c₀) P
  let compactIso :
      sfIntrinsicCompactSupport (geometricCompactification D f₀ c₀) A ⋙
          proEtaleConstantRingDerivedPullback A (galois D Y₀) ≅
        proEtaleConstantRingDerivedPullback A (galois D X₀) ⋙
          sfIntrinsicCompactSupport (geometricCompactification D f₀ c₀) A :=
    { hom := frobeniusCompactFinite D f₀ c₀ l E n hn
      inv := compactConstruction.inv
      hom_inv_id := compactConstruction.hom_inv_id
      inv_hom_id := compactConstruction.inv_hom_id }
  refine ⟨directIso, properIso, compactIso, rfl, rfl, rfl, ?_, ?_⟩
  · intro K
    rfl
  · intro d O
    exact finiteTransport D l hl E n hn f₀ c₀ compactIso rfl d O

end WeilConjectures.FrobeniusExchange
