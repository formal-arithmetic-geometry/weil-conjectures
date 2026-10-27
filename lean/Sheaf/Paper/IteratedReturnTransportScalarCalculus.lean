module

public import Sheaf.Paper.IteratedReturnTransportData
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.Paper.ProEtaleConstantModulePullbackEncoding
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.ReturnScalarSquares
import Sheaf.Paper.PointScalarSingleStepCoherence
import Sheaf.Paper.RationalScalarSingleStepNormalization

/-! # Proof of iteration and scalar calculus for point return transport

Source: blueprint trace-transport, local normalization Steps 2, 8 and 9
(blueprint: lem-trf-iterated-return-transport-scalar-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v w a b c
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures
namespace IteratedReturnTransport

private theorem pointIterate_naturality {C : Type a} [Category.{b} C]
    {V : Type c} [Category.{v} V] (B : C ⥤ V) (U : C ⥤ C)
    (ι : ∀ N : C, B.obj N ⟶ B.obj (U.obj N))
    (hι : ∀ {N J : C} (f : N ⟶ J), B.map f ≫ ι J = ι N ≫ B.map (U.map f))
    (m : ℕ) {N J : C} (f : N ⟶ J) :
    pointIterate B U ι N m ≫ B.map ((iterate U m).map f) =
      B.map f ≫ pointIterate B U ι J m := by
  induction m with
  | zero => simp [pointIterate, iterate]
  | succ m ih =>
    change (pointIterate B U ι N m ≫ ι _) ≫ B.map (U.map _) = _
    rw [Category.assoc, ← hι, ← Category.assoc, ih, Category.assoc]
    rfl

private theorem indexedFunctorIso_naturality {A : Sort w} {C : Type a}
    [Category.{b} C] {V : Type c} [Category.{v} V] (F : A → C ⥤ V)
    {x y : A} (h : x = y) {N J : C} (f : N ⟶ J) :
    (F x).map f ≫ (eqToIso (congrArg (fun i ↦ (F i).obj J) h)).hom =
      (eqToIso (congrArg (fun i ↦ (F i).obj N) h)).hom ≫ (F y).map f := by
  subst h
  simp

private theorem powerComparison_naturality {S : Type a} [Category.{b} S] (X : S)
    {C : Type c} [Category.{v} C] (F : (X ⟶ X) → C ⥤ C)
    (comp : ∀ (h k : X ⟶ X) (N : C),
      (F (h ≫ k)).obj N ≅ (F h).obj ((F k).obj N))
    (hc : ∀ (h k : X ⟶ X) {N J : C} (f : N ⟶ J),
      (F (h ≫ k)).map f ≫ (comp h k J).hom =
        (comp h k N).hom ≫ (F h).map ((F k).map f))
    (g : X ⟶ X) (r : ℕ) {N J : C} (f : N ⟶ J) :
    (F ((End.of g) ^ (r + 1))).map f ≫ (powerComparison X F comp g r J).hom =
      (powerComparison X F comp g r N).hom ≫ (iterate (F g) (r + 1)).map f := by
  induction r generalizing N J with
  | zero => exact indexedFunctorIso_naturality F (pow_one (End.of g)) f
  | succ r ih =>
    let e : F ((End.of g) ^ (r + 1 + 1)) ≅ F (g ≫ (End.of g) ^ (r + 1)) :=
      NatIso.ofComponents
        (fun N ↦ eqToIso (congrArg (fun h ↦ (F h).obj N)
          (pow_succ (End.of g) (r + 1))))
        (fun f ↦ indexedFunctorIso_naturality F (pow_succ (End.of g) (r + 1)) f)
    let d : F (g ≫ (End.of g) ^ (r + 1)) ≅ F ((End.of g) ^ (r + 1)) ⋙ F g :=
      NatIso.ofComponents (comp g ((End.of g) ^ (r + 1))) (hc g _)
    let p : F ((End.of g) ^ (r + 1)) ≅ iterate (F g) (r + 1) :=
      NatIso.ofComponents (powerComparison X F comp g r) (fun f ↦ by
        exact ih f)
    exact (e ≪≫ d ≪≫ Functor.isoWhiskerRight p (F g)).hom.naturality f

private theorem transport_naturality {A : Type a} [Category.{b} A]
    {B : Type c} [Category.{v} B] {V : Type w} [Category V]
    (P : A ⥤ B) (G : A ⥤ A) (U : B ⥤ B) (F : B ⥤ V)
    (I : ∀ N : B, F.obj N ⟶ F.obj (U.obj N))
    (v : ∀ K : A, U.obj (P.obj K) ≅ P.obj (G.obj K))
    (hI : ∀ {N J : B} (f : N ⟶ J), I N ≫ F.map (U.map f) = F.map f ≫ I J)
    (hv : ∀ {K J : A} (f : K ⟶ J), U.map (P.map f) ≫ (v J).hom =
      (v K).hom ≫ P.map (G.map f)) {K J : A} (f : K ⟶ J) :
    (I (P.obj K) ≫ F.map (v K).hom) ≫ F.map (P.map (G.map f)) =
      F.map (P.map f) ≫ (I (P.obj J) ≫ F.map (v J).hom) := by
  rw [Category.assoc, ← F.map_comp, ← hv, F.map_comp, ← Category.assoc,
    ← Category.assoc, hI, Category.assoc]

private theorem scalarIterate_unit {A : Type a} [Category.{b} A]
    (U T : A ⥤ A) (α : ∀ N : A, T.obj (U.obj N) ≅ U.obj (T.obj N))
    (unit : ∀ N : A, T.obj N ≅ N)
    (hu : ∀ N : A, (α N).hom ≫ U.map (unit N).hom = (unit (U.obj N)).hom)
    (m : ℕ) (N : A) :
    (scalarIterate T U U α m N).hom ≫ (iterate U m).map (unit N).hom =
      (unit ((iterate U m).obj N)).hom := by
  induction m with
  | zero => simp [scalarIterate, iterate]
  | succ m ih =>
    simp only [scalarIterate, Iso.trans_hom, Functor.mapIso_hom, iterate,
      Functor.comp_map]
    rw [Category.assoc, ← U.map_comp, ih, hu]
    rfl

private theorem scalarIterate_tower {A : Type a} [Category.{b} A]
    {B : Type c} [Category.{v} B] {V : Type w} [Category V]
    (U : A ⥤ A) (W : B ⥤ B) (Z : V ⥤ V)
    (T : A ⥤ B) (S : B ⥤ V) (R : A ⥤ V)
    (αT : ∀ N : A, T.obj (U.obj N) ≅ W.obj (T.obj N))
    (αS : ∀ N : B, S.obj (W.obj N) ≅ Z.obj (S.obj N))
    (αR : ∀ N : A, R.obj (U.obj N) ≅ Z.obj (R.obj N))
    (assoc : ∀ N : A, S.obj (T.obj N) ≅ R.obj N)
    (hn : ∀ {N J : B} (f : N ⟶ J), S.map (W.map f) ≫ (αS J).hom =
      (αS N).hom ≫ Z.map (S.map f))
    (ht : ∀ N : A, S.map (αT N).hom ≫ (αS (T.obj N)).hom ≫
      Z.map (assoc N).hom = (assoc (U.obj N)).hom ≫ (αR N).hom)
    (m : ℕ) (N : A) :
    S.map (scalarIterate T U W αT m N).hom ≫
        (scalarIterate S W Z αS m (T.obj N)).hom ≫
        (iterate Z m).map (assoc N).hom =
      (assoc ((iterate U m).obj N)).hom ≫ (scalarIterate R U Z αR m N).hom := by
  induction m with
  | zero => simp [scalarIterate, iterate]
  | succ m ih =>
    let t := (scalarIterate T U W αT m N).hom
    let s := (scalarIterate S W Z αS m (T.obj N)).hom
    let r := (scalarIterate R U Z αR m N).hom
    calc
      _ = S.map (αT ((iterate U m).obj N)).hom ≫
          (αS (T.obj ((iterate U m).obj N))).hom ≫ Z.map (S.map t) ≫
          Z.map s ≫ Z.map ((iterate Z m).map (assoc N).hom) := by
        simpa only [scalarIterate, Iso.trans_hom, Functor.mapIso_hom,
          Functor.map_comp, iterate, Functor.comp_map, Category.assoc, t, s] using
          congrArg (fun f ↦ S.map (αT ((iterate U m).obj N)).hom ≫ f ≫
            Z.map s ≫ Z.map ((iterate Z m).map (assoc N).hom)) (hn t)
      _ = S.map (αT ((iterate U m).obj N)).hom ≫
          (αS (T.obj ((iterate U m).obj N))).hom ≫
          Z.map (assoc ((iterate U m).obj N)).hom ≫ Z.map r := by
        simpa only [Functor.map_comp, Category.assoc, t, s, r] using
          congrArg (fun f ↦ S.map (αT ((iterate U m).obj N)).hom ≫
            (αS (T.obj ((iterate U m).obj N))).hom ≫ Z.map f) ih
      _ = _ := by
        change _ = (assoc (U.obj ((iterate U m).obj N))).hom ≫
          ((αR ((iterate U m).obj N)).hom ≫ Z.map r)
        simpa only [Category.assoc] using
          congrArg (fun f ↦ f ≫ Z.map r) (ht ((iterate U m).obj N))

private theorem pointIterate_scalar {A : Type a} [Category.{b} A]
    {B : Type c} [Category.{v} B] {VE : Type w} [Category VE]
    {VM : Type u} [Category VM]
    (U : A ⥤ A) (W : B ⥤ B) (S : A ⥤ B)
    (BE : A ⥤ VE) (BM : B ⥤ VM) (V : VE ⥤ VM)
    (α : ∀ N : A, S.obj (U.obj N) ≅ W.obj (S.obj N))
    (β : ∀ N : A, V.obj (BE.obj N) ≅ BM.obj (S.obj N))
    (ιE : ∀ N : A, BE.obj N ⟶ BE.obj (U.obj N))
    (ιM : ∀ N : B, BM.obj N ⟶ BM.obj (W.obj N))
    (hn : ∀ {N J : B} (f : N ⟶ J),
      BM.map f ≫ ιM J = ιM N ≫ BM.map (W.map f))
    (hs : ∀ N : A, V.map (ιE N) ≫ (β (U.obj N)).hom ≫ BM.map (α N).hom =
      (β N).hom ≫ ιM (S.obj N)) (m : ℕ) (N : A) :
    V.map (pointIterate BE U ιE N m) ≫ (β ((iterate U m).obj N)).hom ≫
        BM.map (scalarIterate S U W α m N).hom =
      (β N).hom ≫ pointIterate BM W ιM (S.obj N) m := by
  induction m with
  | zero => simp [pointIterate, scalarIterate, iterate]
  | succ m ih =>
    let δ := (scalarIterate S U W α m N).hom
    calc
      _ = V.map (pointIterate BE U ιE N m) ≫
          (β ((iterate U m).obj N)).hom ≫ ιM (S.obj ((iterate U m).obj N)) ≫
          BM.map (W.map δ) := by
        change V.map (pointIterate BE U ιE N m ≫ ιE _) ≫
          (β (U.obj ((iterate U m).obj N))).hom ≫
          BM.map ((α _).hom ≫ W.map δ) = _
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun t ↦ V.map (pointIterate BE U ιE N m) ≫ t ≫ BM.map (W.map δ))
            (hs ((iterate U m).obj N))
      _ = V.map (pointIterate BE U ιE N m) ≫
          (β ((iterate U m).obj N)).hom ≫ BM.map δ ≫
          ιM ((iterate W m).obj (S.obj N)) := by
        rw [← hn]
      _ = _ := by
        change _ = (β N).hom ≫
          (pointIterate BM W ιM (S.obj N) m ≫ ιM ((iterate W m).obj (S.obj N)))
        dsimp only [δ]
        simpa only [Category.assoc] using
          congrArg (fun t ↦ t ≫ ιM ((iterate W m).obj (S.obj N))) ih

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (C : IntegralComparisonSystem.{u} l)
  [hpoint : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x)]
  [hspace : ∀ x : (D.geometricFiber X₀).left,
    Invertible (l : (D.geometricFiber X₀).left.residueField x)]
  (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (ι : E →ₐ[ℚ_[l]] M)
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : M →ₐ[ℚ_[l]] L)

private theorem finiteSheafPullbackConstructible {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (hM : IsConstructibleProEtaleModuleSheaf Y A M) :
    IsConstructibleProEtaleModuleSheaf X A (proEtaleConstantModulePullback g A M) := by
  rw [proEtaleModuleRestriction_constructible_iff] at hM ⊢
  obtain ⟨N, hN, ⟨e⟩⟩ :=
    ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
      (ULift.{u + 1, u} A) hM
  let := hN
  let := IsConstructibleSheaf.upperStar g N
  obtain ⟨d⟩ := AlgebraicGeometry.Scheme.proEtaleModuleRestriction_pullback g A M
  exact ProEtale.isConstructible_of_iso
    (((ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).app N).symm ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).mapIso e ≪≫ d.symm)
    (ProEtale.isConstructible_comparisonUpperStar_obj
      ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).obj N))

/-- The exact tensor pullback preserves bounded constructible derived objects.
Source: Stacks Tags 015F, 09AK and 099Y
(blueprint: lem-weil-isomorphism-derived-pullback). -/
private theorem finiteTensorPullbackConstructible {X Y : Scheme.{u}} (g : X ⟶ Y)
    (n : ℕ) (K : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)))
    (hK : intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) Y K) :
    intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X
      ((AlgebraicGeometry.Scheme.proEtaleConstantRingPullback
        (Padic.coefficientExtensionRing l E (n + 1)) g).mapDerivedCategory.obj K) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  let F := AlgebraicGeometry.Scheme.proEtaleConstantRingPullback A g
  change Set.Finite _ ∧ ∀ i, IsConstructibleProEtaleModuleSheaf X A _
  change Set.Finite _ ∧ ∀ i, IsConstructibleProEtaleModuleSheaf Y A _ at hK
  refine ⟨hK.1.subset (fun i hi hzero ↦ hi
    (F.isZero_homologyFunctor_mapDerivedCategory_obj hzero)), ?_⟩
  intro i
  have hc := finiteSheafPullbackConstructible g A
    ((DerivedCategory.homologyFunctor _ i).obj K) (hK.2 i)
  rw [proEtaleModuleRestriction_constructible_iff] at hc ⊢
  exact ProEtale.isConstructible_of_iso
    ((proEtaleModuleRestriction X A).mapIso
      ((F.mapDerivedCategoryHomologyFunctorIso i).app K)) hc

private theorem finitePullbackConstructible {X Y : Scheme.{u}} (g : X ⟶ Y)
    (n : ℕ) (K : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)))
    (hK : intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) Y K) :
    intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X ((finiteDerivedPullback l E n g).obj K) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  let P := intrinsicFiniteTorsionConstructible l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) X
  let : P.IsClosedUnderIsomorphisms :=
    (AlgebraicGeometry.Scheme.proEtale_bounded_constructible_isTriangulated X A).1
  exact P.prop_of_iso ((openSquareDerivedPullbackModel A g).app K)
    (finiteTensorPullbackConstructible l E g n K hK)

private theorem finiteI_naturality (n m : ℕ)
    (N J : (intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).FullSubcategory) (f : N ⟶ J) :
    finiteI D l hl E n N.obj m ≫
        (@Functor.mapDerivedCategory
          (integralOperationsFiniteModules l E (Spec (.of D.k)) n) _ _
          (HasDerivedCategory.standard _)
          (ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionRing l E (n + 1))))
          _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
          (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
          (pointFiniteSectionsAdditive D.k (Padic.coefficientExtensionRing l E (n + 1)))
          (pointFibreFiniteLimits D (Padic.coefficientExtensionRing l E (n + 1)))
          (pointFibreFiniteColimits D (Padic.coefficientExtensionRing l E (n + 1)))).map
          ((iterate (finiteDerivedPullback l E n (frobeniusPointIso D).hom) m).map f.hom) =
      ((pointFiniteFibre D l hl E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n))).map f).hom ≫ finiteI D l hl E n J.obj m := by
  let P := intrinsicFiniteTorsionConstructible l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))
  let U := finiteDerivedPullback l E n (frobeniusPointIso D).hom
  have hp (m : ℕ) (N : P.FullSubcategory) : P ((iterate U m).obj N.obj) := by
    induction m with
    | zero => exact N.property
    | succ m ih =>
      exact ((isomorphismFiniteDerivedPullback_termwise l E
        (frobeniusPointIso D).hom n).choose ((iterate U m).obj N.obj) ih).1
  induction m with
  | zero =>
    simp only [finiteI, pointIterate, iterate, Functor.id_map, Category.id_comp]
    exact (Category.comp_id _).symm
  | succ m ih =>
    have hn := (frobeniusPointTransport_natural D l hl E).2.2.2.2.2.2.2.2.1 n
      ⟨(iterate U m).obj N.obj, hp m N⟩ ⟨(iterate U m).obj J.obj, hp m J⟩
      (ObjectProperty.homMk ((iterate U m).map f.hom))
    have hh := congrArg (fun f ↦ f.hom) hn
    change (finiteI D l hl E n N.obj m ≫
      frobeniusPointTransportFinite D l hl E n ((iterate U m).obj N.obj)) ≫ _ = _
    change _ ≫ frobeniusPointTransportFinite D l hl E n ((iterate U m).obj J.obj) =
      frobeniusPointTransportFinite D l hl E n ((iterate U m).obj N.obj) ≫ _ at hh
    simp only [iterate, Functor.comp_map]
    erw [Category.assoc, ← hh, ← Category.assoc, ih, Category.assoc]
    rfl

private theorem integralI_naturality (m : ℕ)
    {N J : sfIntegralConstructibleCategory l E (Spec (.of D.k))} (f : N ⟶ J) :
    integralI D l hl E N m ≫ (pointIntegralFibre D l hl E).map
        ((iterate (constructibleIntegralPullback l E (frobeniusPointIso D).hom) m).map f) =
      (pointIntegralFibre D l hl E).map f ≫ integralI D l hl E J m := by
  unfold integralI
  apply pointIterate_naturality
  intro N J f
  exact (frobeniusPointTransport_natural D l hl E).2.2.2.2.2.2.2.2.2.1 N J f

private theorem rationalI_naturality (m : ℕ)
    {N J : sfRationalConstructibleCategory l E (Spec (.of D.k))} (f : N ⟶ J) :
    rationalI D l hl E N m ≫ (pointRationalFibre D l hl E).map
        ((iterate (rationalDerivedPullback l E (frobeniusPointIso D).hom) m).map f) =
      (pointRationalFibre D l hl E).map f ≫ rationalI D l hl E J m := by
  unfold rationalI
  apply pointIterate_naturality
  intro N J f
  have hw := (frobeniusPointTransport_natural D l hl E).2.2.2.2.2.2.2.2.2.2.1 N J f
  change (pointRationalFibre D l hl E).map f ≫
      (frobeniusPointTransportRational D l hl E J ≫
        (pointRationalFibre D l hl E).map
          (eqToHom (frobeniusPointRationalPullbackEq D l hl E J).symm)) =
    (frobeniusPointTransportRational D l hl E N ≫
      (pointRationalFibre D l hl E).map
        (eqToHom (frobeniusPointRationalPullbackEq D l hl E N).symm)) ≫
      (pointRationalFibre D l hl E).map
        ((rationalDerivedPullback l E (frobeniusPointIso D).hom).map f)
  rw [← Category.assoc, hw, Category.assoc, ← Functor.map_comp]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Functor.map_comp]
  rfl

private theorem integralComposition_naturality
    (hc : IntegralComparisonCompositionLaws l E C) {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V)
    {K J : sfIntegralConstructibleCategory l E V} (f : K ⟶ J) :
    (constructibleIntegralPullback l E (h ≫ k)).map f ≫
        (integralComparisonConstructibleComposition l E C h k J).hom =
      (integralComparisonConstructibleComposition l E C h k K).hom ≫
        (constructibleIntegralPullback l E h).map
          ((constructibleIntegralPullback l E k).map f) := by
  apply ObjectProperty.hom_ext
  exact hc.naturality h k K J f

private theorem pullback_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E f).obj K =
      (sfRationalConstructibleLocalization l E X).obj
        ((constructibleIntegralPullback l E f).obj K.obj) :=
  (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K

private theorem pullback_tmul {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K J : sfIntegralConstructibleCategory l E Y) (a : K ⟶ J)
    (b : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
    HEq ((rationalDerivedPullback l E f).map
      (b ⊗ₜ[Padic.coefficientExtensionIntegers l E] a))
      (b ⊗ₜ[Padic.coefficientExtensionIntegers l E]
        (constructibleIntegralPullback l E f).map a) :=
  (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 K J a b

private theorem rationalComposition_heq {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : sfRationalConstructibleCategory l E Z) :
    HEq (integralComparisonRationalComposition l E C h k K).hom
      ((sfRationalConstructibleLocalization l E X).map
        (integralComparisonConstructibleComposition l E C h k K.obj).hom) := by
  dsimp only [integralComparisonRationalComposition, localPullbackObjectIso,
    Iso.trans, Iso.symm, Functor.mapIso, eqToIso]
  erw [eqToHom_map]
  erw [← Category.assoc, ← Category.assoc, comp_eqToHom_heq_iff,
    comp_eqToHom_heq_iff, eqToHom_comp_heq_iff]

private theorem map_heq {C T : Type*} [Category C] [Category T]
    (Q : C ⥤ T) {U V U' V' : C} (hu : U = U') (hv : V = V')
    {f : U ⟶ V} {f' : U' ⟶ V'} (hf : HEq f f') : HEq (Q.map f) (Q.map f') := by
  subst U'
  subst V'
  exact heq_of_eq (congrArg Q.map (eq_of_heq hf))

private theorem rationalComposition_naturality {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (hc : IntegralComparisonCompositionLaws l E C)
    (K J : sfRationalConstructibleCategory l E Z) (v : K ⟶ J) :
    (integralComparisonRationalComposition l E C h k K).hom ≫
        (rationalDerivedPullback l E h).map ((rationalDerivedPullback l E k).map v) =
      (rationalDerivedPullback l E (h ≫ k)).map v ≫
        (integralComparisonRationalComposition l E C h k J).hom := by
  let _ : (rationalDerivedPullback l E h).Additive :=
    (rationalDerivedPullback_existsUnique l E h).exists.choose_spec.1
  let _ : (rationalDerivedPullback l E k).Additive :=
    (rationalDerivedPullback_existsUnique l E k).exists.choose_spec.1
  let _ : (rationalDerivedPullback l E (h ≫ k)).Additive :=
    (rationalDerivedPullback_existsUnique l E (h ≫ k)).exists.choose_spec.1
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    change (integralComparisonRationalComposition l E C h k K).hom ≫
        (rationalDerivedPullback l E h).map
          ((rationalDerivedPullback l E k).map (a + b : K ⟶ J)) =
      (rationalDerivedPullback l E (h ≫ k)).map (a + b : K ⟶ J) ≫
        (integralComparisonRationalComposition l E C h k J).hom
    rw [(rationalDerivedPullback l E k).map_add,
      (rationalDerivedPullback l E h).map_add,
      (rationalDerivedPullback l E (h ≫ k)).map_add,
      Preadditive.comp_add, Preadditive.add_comp, ha, hb]
  | tmul b a =>
    have hh : HEq ((rationalDerivedPullback l E h).map
        ((rationalDerivedPullback l E k).map (b ⊗ₜ[_] a)))
        (b ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          (constructibleIntegralPullback l E h).map
            ((constructibleIntegralPullback l E k).map a)) :=
      (map_heq _ (pullback_obj l E k K) (pullback_obj l E k J)
        (pullback_tmul l E k K.obj J.obj a b)).trans
          (pullback_tmul l E h _ _ ((constructibleIntegralPullback l E k).map a) b)
    apply eq_of_heq
    apply (heq_comp (pullback_obj l E (h ≫ k) K)
      (by rw [pullback_obj, pullback_obj]; rfl)
      (by rw [pullback_obj, pullback_obj]; rfl)
      (rationalComposition_heq l E C h k K) hh).trans
    apply HEq.trans _ (heq_comp (pullback_obj l E (h ≫ k) K)
      (pullback_obj l E (h ≫ k) J)
      (by rw [pullback_obj, pullback_obj]; rfl)
      (pullback_tmul l E (h ≫ k) K.obj J.obj a b)
      (rationalComposition_heq l E C h k J)).symm
    change HEq (ScalarLocalization.composition _ _ _ _ _ _
      (b ⊗ₜ[_] _) (1 ⊗ₜ[_] _))
      (ScalarLocalization.composition _ _ _ _ _ _ (1 ⊗ₜ[_] _) (b ⊗ₜ[_] _))
    erw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul,
      mul_one, one_mul]
    exact heq_of_eq (congrArg (fun f ↦ b ⊗ₜ[Padic.coefficientExtensionIntegers l E] f)
      (integralComposition_naturality l E C hc h k a).symm)

private theorem integralScalar_naturality {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    {K J : sfIntegralConstructibleCategory l E Y} (v : K ⟶ J) :
    (integralScalarExtension l E M ι X).map ((integralDerivedPullback l E f).map v.hom) ≫
        (integralComparisonScalar l E M ι C f J).hom =
      (integralComparisonScalar l E M ι C f K).hom ≫
        (integralDerivedPullback l M f).map
          ((integralScalarExtension l E M ι Y).map v.hom) := by
  let a := (C.coefficient E).system Y
  let b := (C.coefficient E).system X
  let d := (C.coefficient M).system Y
  let L := coefficientSequenceLimit l M X
  let T := integralComparisonDerivedSequenceScalar l E M ι X
  let F := integralComparisonDerivedSequencePullback l M f
  let q := integralComparisonPullbackCounit l E f a b ((C.coefficient E).roos X)
    ((C.coefficient E).pullback f)
  let t := integralComparisonScalarCounit l E M ι Y a d ((C.coefficient M).roos Y)
    ((C.scalar E M ι).model Y)
  let lam := Functor.whiskerLeft (integralDerivedPullback l E f)
      ((C.scalar E M ι).model X).realization.hom ≫
    Functor.whiskerRight q (T ⋙ L)
  let mu := Functor.whiskerLeft (integralScalarExtension l E M ι Y)
      ((C.coefficient M).pullback f).realization.hom ≫
    Functor.whiskerRight t (F ⋙ L) ≫
    Functor.whiskerRight (Functor.whiskerLeft a.reduction
      (integralComparisonSystemScalarPullback l E M ι f).inv) L
  have hlam := lam.naturality v.hom
  have hmu := mu.naturality v.hom
  change _ ≫ ((integralComparisonLambda l E M ι C f J).hom ≫
    (integralComparisonMu l E M ι C f J).inv) =
    ((integralComparisonLambda l E M ι C f K).hom ≫
      (integralComparisonMu l E M ι C f K).inv) ≫ _
  have hlam' : (integralScalarExtension l E M ι X).map
        ((integralDerivedPullback l E f).map v.hom) ≫
      (integralComparisonLambda l E M ι C f J).hom =
    (integralComparisonLambda l E M ι C f K).hom ≫
      (a.reduction ⋙ integralComparisonDerivedSequencePullback l E f ⋙ T ⋙ L).map v.hom := by
    exact hlam
  have hmu' : (integralDerivedPullback l M f).map
        ((integralScalarExtension l E M ι Y).map v.hom) ≫
      (integralComparisonMu l E M ι C f J).hom =
    (integralComparisonMu l E M ι C f K).hom ≫
      (a.reduction ⋙ integralComparisonDerivedSequencePullback l E f ⋙ T ⋙ L).map v.hom := by
    exact hmu
  apply (cancel_mono (integralComparisonMu l E M ι C f J).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hmu', Iso.inv_hom_id_assoc]
  exact hlam'

attribute [local irreducible] finiteComposition powerComparison
  integralComparisonConstructibleComposition integralComparisonRationalComposition
  constructibleIntegralPullback rationalDerivedPullback

omit hpoint hspace in
private theorem finiteReturn_naturality (n r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)))
    {K J : proEtaleDerivedCategory (D.geometricFiber X₀).left
      (Padic.coefficientExtensionRing l E (n + 1))} (f : K ⟶ J) :
    (iterate (finiteDerivedPullback l E n (frobeniusPointIso D).hom) (r + 1)).map
        ((finiteDerivedPullback l E n z).map f) ≫ (finiteReturn D l E X₀ n r z w J).hom =
      (finiteReturn D l E X₀ n r z w K).hom ≫
        (finiteDerivedPullback l E n z).map
          ((iterate (finiteDerivedPullback l E n (D.geometricFrobenius X₀).hom)
            (r + 1)).map f) := by
  let P := finiteDerivedPullback l E n z
  let eS : finiteDerivedPullback l E n
      ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≅
      iterate (finiteDerivedPullback l E n (frobeniusPointIso D).hom) (r + 1) :=
    NatIso.ofComponents
    (powerComparison (Spec (.of D.k)) (finiteDerivedPullback l E n)
      (fun h k N ↦ (finiteComposition l E n h k).app N)
      (frobeniusPointIso D).hom r)
    (fun f ↦ powerComparison_naturality _ (finiteDerivedPullback l E n)
      (fun h k N ↦ (finiteComposition l E n h k).app N)
      (fun h k {_ _} f ↦ (finiteComposition l E n h k).hom.naturality f) _ r f)
  let eX : finiteDerivedPullback l E n
      ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)) ≅
      iterate (finiteDerivedPullback l E n (D.geometricFrobenius X₀).hom) (r + 1) :=
    NatIso.ofComponents
    (powerComparison (D.geometricFiber X₀).left (finiteDerivedPullback l E n)
      (fun h k N ↦ (finiteComposition l E n h k).app N)
      (D.geometricFrobenius X₀).hom r)
    (fun f ↦ powerComparison_naturality _ (finiteDerivedPullback l E n)
      (fun h k N ↦ (finiteComposition l E n h k).app N)
      (fun h k {_ _} f ↦ (finiteComposition l E n h k).hom.naturality f) _ r f)
  let eW : finiteDerivedPullback l E n
      (((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z) ≅
      finiteDerivedPullback l E n
        (z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) :=
    NatIso.ofComponents
    (fun K ↦ eqToIso (congrArg (fun g ↦ (finiteDerivedPullback l E n g).obj K) w))
    (fun f ↦ indexedFunctorIso_naturality (finiteDerivedPullback l E n) w f)
  let e : P ⋙ iterate (finiteDerivedPullback l E n (frobeniusPointIso D).hom) (r + 1) ≅
      iterate (finiteDerivedPullback l E n (D.geometricFrobenius X₀).hom) (r + 1) ⋙ P :=
    Functor.isoWhiskerLeft P eS.symm ≪≫
      (finiteComposition l E n _ z).symm ≪≫ eW ≪≫ finiteComposition l E n z _ ≪≫
      Functor.isoWhiskerRight eX P
  have he := e.hom.naturality f
  dsimp only [e, eS, eX, eW, Functor.isoWhiskerLeft, Functor.isoWhiskerRight,
    NatIso.ofComponents, NatTrans.comp_app, Functor.whiskerLeft, Functor.whiskerRight,
    Iso.trans, Iso.symm, Functor.comp_map] at he
  dsimp only [finiteReturn, Iso.trans, Iso.symm, Functor.mapIso]
  exact he

omit hspace in
private theorem finiteNaturality_proof (n r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) :
    FiniteNaturality D l hl E X₀ n r z w := by
  constructor
  · intro N J f
    exact finiteI_naturality D l hl E n (r + 1) N J f
  · intro K J f
    let P := finiteDerivedPullback l E n z
    have hi := finiteI_naturality D l hl E n (r + 1)
      ⟨P.obj K.obj, finitePullbackConstructible l E z n K.obj K.property⟩
      ⟨P.obj J.obj, finitePullbackConstructible l E z n J.obj J.property⟩
      (ObjectProperty.homMk (P.map f.hom))
    unfold finiteTransport
    erw [Category.assoc, ← Functor.map_comp, ← finiteReturn_naturality D l E X₀,
      Functor.map_comp, ← Category.assoc, ← Category.assoc, hi, Category.assoc]

private theorem integralReturn_naturality
    (hc : IntegralComparisonCompositionLaws l E C) (r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)))
    {K J : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left} (f : K ⟶ J) :
    (iterate (constructibleIntegralPullback l E (frobeniusPointIso D).hom) (r + 1)).map
        ((constructibleIntegralPullback l E z).map f) ≫
        (integralReturn D l E X₀ C r z w J).hom =
      (integralReturn D l E X₀ C r z w K).hom ≫
        (constructibleIntegralPullback l E z).map
          ((iterate (constructibleIntegralPullback l E (D.geometricFrobenius X₀).hom)
            (r + 1)).map f) := by
  let P := constructibleIntegralPullback l E z
  let eS : constructibleIntegralPullback l E
      ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≅
      iterate (constructibleIntegralPullback l E (frobeniusPointIso D).hom) (r + 1) :=
    NatIso.ofComponents
    (powerComparison (Spec (.of D.k)) (fun f ↦ constructibleIntegralPullback l E f)
      (fun h k N ↦ integralComparisonConstructibleComposition l E C h k N)
      (frobeniusPointIso D).hom r)
    (fun f ↦ powerComparison_naturality _ (fun g ↦ constructibleIntegralPullback l E g)
      (fun h k N ↦ integralComparisonConstructibleComposition l E C h k N)
      (fun h k {_ _} f ↦ integralComposition_naturality l E C hc h k f) _ r f)
  let eX : constructibleIntegralPullback l E
      ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)) ≅
      iterate (constructibleIntegralPullback l E (D.geometricFrobenius X₀).hom) (r + 1) :=
    NatIso.ofComponents
    (powerComparison (D.geometricFiber X₀).left (fun f ↦ constructibleIntegralPullback l E f)
      (fun h k N ↦ integralComparisonConstructibleComposition l E C h k N)
      (D.geometricFrobenius X₀).hom r)
    (fun f ↦ powerComparison_naturality _ (fun g ↦ constructibleIntegralPullback l E g)
      (fun h k N ↦ integralComparisonConstructibleComposition l E C h k N)
      (fun h k {_ _} f ↦ integralComposition_naturality l E C hc h k f) _ r f)
  let cL : constructibleIntegralPullback l E
      (((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z) ≅
      P ⋙ constructibleIntegralPullback l E
        ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) := NatIso.ofComponents
    (integralComparisonConstructibleComposition l E C
      ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) z)
    (fun f ↦ integralComposition_naturality l E C hc _ z f)
  let cR : constructibleIntegralPullback l E
      (z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) ≅
      constructibleIntegralPullback l E
        ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)) ⋙ P := NatIso.ofComponents
    (integralComparisonConstructibleComposition l E C z
      ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)))
    (fun f ↦ integralComposition_naturality l E C hc z _ f)
  let eW : constructibleIntegralPullback l E
      (((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z) ≅
      constructibleIntegralPullback l E
        (z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) := NatIso.ofComponents
    (fun K ↦ eqToIso (congrArg (fun g ↦ (constructibleIntegralPullback l E g).obj K) w))
    (fun f ↦ indexedFunctorIso_naturality (fun g ↦ constructibleIntegralPullback l E g) w f)
  exact (Functor.isoWhiskerLeft P eS.symm ≪≫ cL.symm ≪≫ eW ≪≫ cR ≪≫
    Functor.isoWhiskerRight eX P).hom.naturality f

private theorem rationalReturn_naturality
    (hc : IntegralComparisonCompositionLaws l E C) (r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)))
    {K J : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left} (f : K ⟶ J) :
    (iterate (rationalDerivedPullback l E (frobeniusPointIso D).hom) (r + 1)).map
        ((rationalDerivedPullback l E z).map f) ≫
        (rationalReturn D l E X₀ C r z w J).hom =
      (rationalReturn D l E X₀ C r z w K).hom ≫
        (rationalDerivedPullback l E z).map
          ((iterate (rationalDerivedPullback l E (D.geometricFrobenius X₀).hom)
            (r + 1)).map f) := by
  let P := rationalDerivedPullback l E z
  let eS : rationalDerivedPullback l E
      ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≅
      iterate (rationalDerivedPullback l E (frobeniusPointIso D).hom) (r + 1) :=
    NatIso.ofComponents
    (powerComparison (Spec (.of D.k)) (fun f ↦ rationalDerivedPullback l E f)
      (fun h k N ↦ integralComparisonRationalComposition l E C h k N)
      (frobeniusPointIso D).hom r)
    (fun f ↦ powerComparison_naturality _ (fun g ↦ rationalDerivedPullback l E g)
      (fun h k N ↦ integralComparisonRationalComposition l E C h k N)
      (fun h k {_ _} f ↦ (rationalComposition_naturality l E C h k hc _ _ f).symm) _ r f)
  let eX : rationalDerivedPullback l E
      ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)) ≅
      iterate (rationalDerivedPullback l E (D.geometricFrobenius X₀).hom) (r + 1) :=
    NatIso.ofComponents
    (powerComparison (D.geometricFiber X₀).left (fun f ↦ rationalDerivedPullback l E f)
      (fun h k N ↦ integralComparisonRationalComposition l E C h k N)
      (D.geometricFrobenius X₀).hom r)
    (fun f ↦ powerComparison_naturality _ (fun g ↦ rationalDerivedPullback l E g)
      (fun h k N ↦ integralComparisonRationalComposition l E C h k N)
      (fun h k {_ _} f ↦ (rationalComposition_naturality l E C h k hc _ _ f).symm) _ r f)
  let cL : rationalDerivedPullback l E
      (((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z) ≅
      P ⋙ rationalDerivedPullback l E
        ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) := NatIso.ofComponents
    (integralComparisonRationalComposition l E C
      ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) z)
    (fun f ↦ (rationalComposition_naturality l E C _ z hc _ _ f).symm)
  let cR : rationalDerivedPullback l E
      (z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) ≅
      rationalDerivedPullback l E
        ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)) ⋙ P := NatIso.ofComponents
    (integralComparisonRationalComposition l E C z
      ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)))
    (fun f ↦ (rationalComposition_naturality l E C z _ hc _ _ f).symm)
  let eW : rationalDerivedPullback l E
      (((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z) ≅
      rationalDerivedPullback l E
        (z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) := NatIso.ofComponents
    (fun K ↦ eqToIso (congrArg (fun g ↦ (rationalDerivedPullback l E g).obj K) w))
    (fun f ↦ indexedFunctorIso_naturality (fun g ↦ rationalDerivedPullback l E g) w f)
  exact (Functor.isoWhiskerLeft P eS.symm ≪≫ cL.symm ≪≫ eW ≪≫ cR ≪≫
    Functor.isoWhiskerRight eX P).hom.naturality f

private theorem integralNaturality_proof
    (hc : IntegralComparisonCompositionLaws l E C) (r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) :
    IntegralNaturality D l hl E X₀ C r z w := by
  constructor
  · intro N J f
    exact integralI_naturality D l hl E (r + 1) f
  · intro K J f
    exact transport_naturality (constructibleIntegralPullback l E z)
      (iterate (constructibleIntegralPullback l E (D.geometricFrobenius X₀).hom) (r + 1))
      (iterate (constructibleIntegralPullback l E (frobeniusPointIso D).hom) (r + 1))
      (pointIntegralFibre D l hl E) (fun N ↦ integralI D l hl E N (r + 1))
      (integralReturn D l E X₀ C r z w)
      (fun f ↦ integralI_naturality D l hl E (r + 1) f)
      (fun f ↦ integralReturn_naturality D l E X₀ C hc r z w f) f

private theorem rationalNaturality_proof
    (hc : IntegralComparisonCompositionLaws l E C) (r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) :
    RationalNaturality D l hl E X₀ C r z w := by
  constructor
  · intro N J f
    exact rationalI_naturality D l hl E (r + 1) f
  · intro K J f
    exact transport_naturality (rationalDerivedPullback l E z)
      (iterate (rationalDerivedPullback l E (D.geometricFrobenius X₀).hom) (r + 1))
      (iterate (rationalDerivedPullback l E (frobeniusPointIso D).hom) (r + 1))
      (pointRationalFibre D l hl E) (fun N ↦ rationalI D l hl E N (r + 1))
      (rationalReturn D l E X₀ C r z w)
      (fun f ↦ rationalI_naturality D l hl E (r + 1) f)
      (fun f ↦ rationalReturn_naturality D l E X₀ C hc r z w f) f

attribute [local semireducible] constructibleIntegralPullback

private theorem integralScalar_naturality_full {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    {K J : sfIntegralConstructibleCategory l E Y} (v : K ⟶ J) :
    (integralComparisonConstructibleScalar l E M ι X).map
        ((constructibleIntegralPullback l E f).map v) ≫
        (ObjectProperty.isoMk _ (integralComparisonScalar l E M ι C f J)).hom =
      (ObjectProperty.isoMk _ (integralComparisonScalar l E M ι C f K)).hom ≫
        (constructibleIntegralPullback l M f).map
          ((integralComparisonConstructibleScalar l E M ι Y).map v) := by
  apply ObjectProperty.hom_ext
  exact integralScalar_naturality l E C M ι f v

private theorem systemPowerNormalization_proof
    (hC : IntegralComparisonRealizationCoherence l E M ι C)
    (Y : Scheme.{u}) [∀ y : Y, Invertible (l : Y.residueField y)]
    (g : Y ⟶ Y) (m : ℕ) : SystemPowerNormalization l E M ι L j Y g m := by
  constructor
  · intro N
    exact scalarIterate_unit _ _ _ _ (hC.systemScalarIdentity g) m N
  · intro N
    exact scalarIterate_tower _ _ _ _ _ _ _ _ _ _
      (fun f ↦ (integralComparisonSequenceScalarPullback.{u, u} l M L j g).hom.naturality f)
      (hC.systemScalarTower L j g) m N

private theorem integralPowerNormalization_proof
    (hC : IntegralComparisonRealizationCoherence l E M ι C)
    (Y : Scheme.{u}) [∀ y : Y, Invertible (l : Y.residueField y)]
    (g : Y ⟶ Y) (m : ℕ) : IntegralPowerNormalization l E C M ι L j Y g m := by
  constructor
  · intro N
    apply scalarIterate_unit
    intro N
    apply ObjectProperty.hom_ext
    exact hC.scalarIdentity g N
  · intro N
    apply scalarIterate_tower
    · intro N J f
      exact integralScalar_naturality_full l M C L j g f
    · intro N
      apply ObjectProperty.hom_ext
      exact hC.scalarTower L j g N

private theorem rationalPowerNormalization_proof
    (hC : IntegralComparisonRealizationCoherence l E M ι C)
    (Y : Scheme.{u}) [∀ y : Y, Invertible (l : Y.residueField y)]
    (g : Y ⟶ Y) (m : ℕ) : RationalPowerNormalization l E C M ι L j Y g m := by
  have h := rationalScalarSingleStepNormalization l E C M ι L j hC Y g
  dsimp only [RationalPowerNormalization, PowerScalarUnit, PowerScalarTower,
    rationalPowerScalar, scalarIterate, iterate, Iso.trans_hom, Functor.mapIso_hom,
    Functor.comp_obj, Functor.id_obj, Iso.refl_hom, Functor.comp_map] at h
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h
  constructor
  · intro N
    apply scalarIterate_unit
    intro N
    exact h.1 N
  · intro N
    apply scalarIterate_tower
    · intro N J f
      exact (integralComparisonRationalScalar l M C L j g).hom.naturality f
    · intro N
      exact h.2 N

attribute [local semireducible] rationalDerivedPullback

private theorem rationalPointScalarEquation_proof
    (hC : IntegralComparisonRealizationCoherence l E M ι C) (m : ℕ) :
    RationalPointScalarEquation D l hl E C M ι m := by
  have hs := (pointScalarSingleStepCoherence D l hl E C M ι M
    (AlgHom.id ℚ_[l] M) hC).1
  intro N
  unfold rationalI rationalPowerScalar
  exact pointIterate_scalar
    (rationalDerivedPullback l E (frobeniusPointIso D).hom)
    (rationalDerivedPullback l M (frobeniusPointIso D).hom)
    (sfRationalScalarExtension l E (Spec (.of D.k)) 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι)
    (pointRationalFibre D l hl E) (pointRationalFibre D l hl M)
    (DerivedCategory.pointFdScalarExtension ι.toRingHom)
    (fun K ↦ (integralComparisonRationalScalar l E C M ι
      (frobeniusPointIso D).hom).app K)
    (fun K ↦ ((pointRationalFibreScalarIso D l hl E M ι).app K).symm)
    (fun K ↦ localPointTransport l E D hl K)
    (fun K ↦ localPointTransport l M D hl K) (by
      intro N J f
      have hn := (rationalI_naturality D l hl M 1 f).symm
      dsimp only [rationalI, pointIterate, iterate, Functor.comp_map,
        Functor.id_map, Functor.id_obj] at hn
      erw [Category.id_comp, Category.id_comp] at hn
      exact hn) (by
      intro N
      have he := hs N
      dsimp only [RationalPointScalarEquation, PointScalarEquation, rationalPowerScalar,
        rationalI, pointIterate, scalarIterate, iterate, Iso.trans_hom, Functor.mapIso_hom,
        Functor.comp_obj, Functor.id_obj, Iso.refl_hom, Functor.comp_map] at he
      erw [Category.id_comp, Category.id_comp] at he
      simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using he) m N
end IteratedReturnTransport

/-- Iterated point transport is natural at finite, integral and raw rational stages,
and the specified return and point comparisons satisfy both scalar identities,
including their identity and successive-extension normalizations.
Source: blueprint main-20261015, sec-trace-formula/sk-thm-trace-transport,
prop-trf-karoubi-independence.proof.md, final sentence
(blueprint: lem-trf-iterated-return-transport-scalar-calculus).

Proof (the six steps of the DAG):
1. Use lem-weil-frobenius-point-transport-natural for the one-step iota square.
   Induct on j: I^0 is identity, and the next square is the preceding square
   followed by the one-step square at U^j N. This applies to rational morphisms too.
2. Write v = s r inverse for the two iterated compositors from the common pullback
   along the equal scheme maps. Composition naturality at finite and integral
   stages gives naturality of v; raw rationalization extends integral naturality
   from pure tensors to their sums. Combine it with step 1 to obtain naturality of t.
3. The mixed composition/scalar equation of
   lem-trf-integral-pullback-comparison-realization gives r_M b = U_M^m(a) δ T_s(r_E)
   and s_M b = P_M(d) a T_s(s_E). The same b occurs because the composite scheme
   maps are equal. Substitute v = s r inverse and cancel r and T_s(r_E). This proves
   the return-square scalar equation on entire quotient diagrams, on integral
   realizations, and then in their raw rationalization.
4. Apply lem-weil-point-automorphism-transport-scalar-extension to geometric
   Frobenius on s. Its restriction and kappa recipe is exactly iota, and its
   canonical completion-normalized pullback comparison is the stipulated one.
   Invert the actual point-sections comparison to obtain the one-step β equation.
5. Expand δ^(j+1) = U_M(δ^j) α_(U_E^j N) and I^(j+1). Apply step 4 at U_E^j N,
   use naturality of iota at δ^j, and apply the induction hypothesis. At j=0 the
   equation is β = β; at j=m it is the second displayed scalar identity.
6. Identity coefficients reduce via the multiplication and completeness units.
   For a tower, substitute the completion-normalized tensor associators of
   lem-trf-integral-pullback-comparison-realization and the actual sections
   associator of lem-weil-point-sections-scalar-extension. Successive comparisons
   compose to the direct comparison in both equations. No finite Tor-amplitude
   hypothesis enters any integral step, and raw Hom tensor products add no idempotents. -/
theorem iteratedReturnTransportScalarCalculus
    (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (F G H : Padic.FiniteCoefficientFields c.l c.Qbar)
    (hFG : F ≤ G) (hGH : G ≤ H)
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (C : IntegralComparisonSystem.{u} c.l)
    (_hC : IntegralComparisonRealizationCoherence c.l F.val G.val
      (IntermediateField.inclusion hFG) C)
    (r : ℕ) (z : Over.mk (𝟙 (Spec (.of D.k))) ⟶ D.geometricFiber X₀)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z.left =
      z.left ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) :
    IteratedReturnTransport.Properties D c.l c.different F.val X₀ C G.val
      (IntermediateField.inclusion hFG) H.val (IntermediateField.inclusion hGH) r z.left w := by
  let := frobeniusPointPrimeInvertible D c.l c.different
  let := sfWeilPrimeInvertible D c.l c.different X₀
  have hR := returnScalarSquares D c.l F.val C G.val (IntermediateField.inclusion hFG)
    _hC X₀ r z.left w
  have hP := pointScalarSingleStepCoherence D c.l c.different F.val C G.val
    (IntermediateField.inclusion hFG) H.val (IntermediateField.inclusion hGH) _hC
  refine ⟨?_, ?_, ?_, ⟨hR.1, hR.2.1, hR.2.2, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hP.2⟩
  · intro n
    exact IteratedReturnTransport.finiteNaturality_proof D c.l c.different F.val X₀
      n r z.left w
  · exact IteratedReturnTransport.integralNaturality_proof D c.l c.different F.val X₀ C
      (_hC.composition F.val) r z.left w
  · exact IteratedReturnTransport.rationalNaturality_proof D c.l c.different F.val X₀ C
      (_hC.composition F.val) r z.left w
  · exact IteratedReturnTransport.rationalPointScalarEquation_proof D c.l c.different
      F.val C G.val (IntermediateField.inclusion hFG) _hC (r + 1)
  · exact IteratedReturnTransport.systemPowerNormalization_proof c.l F.val C G.val
      (IntermediateField.inclusion hFG) H.val (IntermediateField.inclusion hGH) _hC _ _ _
  · exact IteratedReturnTransport.systemPowerNormalization_proof c.l F.val C G.val
      (IntermediateField.inclusion hFG) H.val (IntermediateField.inclusion hGH) _hC _ _ _
  · exact IteratedReturnTransport.integralPowerNormalization_proof c.l F.val C G.val
      (IntermediateField.inclusion hFG) H.val (IntermediateField.inclusion hGH) _hC _ _ _
  · exact IteratedReturnTransport.integralPowerNormalization_proof c.l F.val C G.val
      (IntermediateField.inclusion hFG) H.val (IntermediateField.inclusion hGH) _hC _ _ _
  · exact IteratedReturnTransport.rationalPowerNormalization_proof c.l F.val C G.val
      (IntermediateField.inclusion hFG) H.val (IntermediateField.inclusion hGH) _hC _ _ _
  · exact IteratedReturnTransport.rationalPowerNormalization_proof c.l F.val C G.val
      (IntermediateField.inclusion hFG) H.val (IntermediateField.inclusion hGH) _hC _ _ _

end WeilConjectures
