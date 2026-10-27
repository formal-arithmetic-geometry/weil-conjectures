# Finite general-ring canonical data extraction

## Reason

The two separate orientation and exponent proof obligations must refer to the existing
canonical data without importing the theorem that uses those obligations. Move the
existing definitions and finite-ring instance verbatim to FiniteGeneralRingData and
publicly re-export it. This is an organizational extraction, not a definition repair:
every existing signature, attribute, visibility, instance and definition body is unchanged.
The original six public imports also stay verbatim. No source-library file is edited.
Every target has exactly the same definitions and mathematical meaning.

## Old

The following declarations were in Sheaf.SecSmoothPurity.FiniteGeneralRing:

```lean
/-- The prime-power purity setting at the bottom subextension, hence at Q_ell itself.
The closure is only a presentation of that degree-one extension.
Source: general-ring purity, clause (1), E=Q_ell, level n
(blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingPrimeSetting (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p) (n : ℕ) (hn : 1 ≤ n) :
    WeilConjectures.PurityFiniteSetting.{u} where
  field := D
  coefficients := {
    l := ell
    different := hEll
    Qbar := ULift.{u} (AlgebraicClosure (Padic ell))
    isAlgClosure := {
      isAlgClosed := {
        splits := fun _p ↦ Polynomial.Splits.of_splits_map ULift.ringEquiv.toRingHom
          (IsAlgClosed.splits _) (fun a _ ↦ ⟨ULift.up a, rfl⟩) }
      isAlgebraic := Algebra.IsAlgebraic.of_injective
        ({ toRingEquiv := ULift.ringEquiv
           commutes' := fun _ ↦ rfl } :
          ULift.{u} (AlgebraicClosure (Padic ell)) ≃ₐ[Padic ell]
            AlgebraicClosure (Padic ell)).toAlgHom ULift.down_injective } }
  extension := ⊥
  level := n
  level_pos := hn

/-- Finiteness of the actual finite quotient, reused from the coefficient dependency.
Source: finite-coefficient conventions (blueprint: det-sp-finite-general-ring). -/
instance finiteGeneralRingRingFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- Scalar extension of the comparison-origin coefficient unit, using the published
site/scalar mate and the multiplication-normalized ordinary scalar unit.
Source: general-ring purity, clause (1) (blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingScalarUnitIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (phi : A →+* B) (T : Scheme.{u}) :
    (Etale.FiniteSmoothPurity.proScalar phi T).obj
        ((Etale.FiniteSmoothPurity.comparison A T).obj (Etale.ordinaryFiniteUnit A T)) ≅
      (Etale.FiniteSmoothPurity.comparison B T).obj (Etale.ordinaryFiniteUnit B T) :=
  (pbcComparisonReduction T phi).app (Etale.ordinaryFiniteUnit A T) ≪≫
    (Etale.FiniteSmoothPurity.comparison B T).mapIso
      ((Etale.scalarExtension phi T).mapIso
          (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T) ≪≫
        Etale.ExceptionalCoefficients.unitIso phi T ≪≫
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} B) T).symm)

/-- Actual intrinsic derived scalar extension, in fixed-coefficient coordinates.
This is scalarExtensionFunctor conjugated by the published realization equivalences.
Source: general-ring purity, (-)_A (blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingScalar {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (phi : A →+* B) (T : Scheme.{u}) :
    Etale.FiniteSmoothPurity.proCategory (ULift.{u + 1, u} A) T ⥤
      Etale.FiniteSmoothPurity.proCategory (ULift.{u + 1, u} B) T :=
  (sfIntrinsicDerivedEquivalence T A).functor ⋙ scalarExtensionFunctor phi T ⋙
    (sfIntrinsicDerivedEquivalence T B).inverse

/-- The scalar-presentation comparison is the inverse realization of the published
section-normalized scalar mate, followed by the realization unit.
Source: general-ring purity, coefficient comparison (blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingScalarIso {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (phi : A →+* B) (T : Scheme.{u})
    (K : Etale.FiniteSmoothPurity.proCategory (ULift.{u + 1, u} A) T) :
    (finiteGeneralRingScalar phi T).obj K ≅
      (Etale.FiniteSmoothPurity.proScalar
        (RingHom.ulift.{u + 1, u + 1, u, u} phi) T).obj K :=
  (sfIntrinsicDerivedEquivalence T B).inverse.mapIso
      ((reductionRealizationScalarIso phi T).app K) ≪≫
    (sfIntrinsicDerivedEquivalence T B).unitIso.symm.app _

/-- The comparison-origin unit. This is the actual constant A_T in degree zero.
Source: general-ring purity, omega=f^!A_Y (blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingUnit (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  (Etale.FiniteSmoothPurity.comparison A T).obj (Etale.ordinaryFiniteUnit A T)

/-- The map from nu* of the ordinary dualizing complex to f^! of the comparison unit.
Its formula uses the comparison-adjunction unit, so it is never an arbitrary iso.
Source: finite exceptional inverse image (blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingDualizingUnitMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (Etale.FiniteSmoothPurity.comparison A X).obj
        (Etale.dualizingComplex (ModuleCat.{u + 1} A) f) ⟶
      (Etale.FiniteSmoothPurity.exceptional A f).obj (finiteGeneralRingUnit A Y) :=
  (Etale.FiniteSmoothPurity.comparison A X).map
    ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).map
      ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app
        (Etale.ordinaryFiniteUnit A Y)))

/-- The actual exceptional scalar comparison evaluated at the unit, followed by the
canonical scalar unit identification. Its middle factor is the published transpose
of scalar extension of the compact-support counit after the inverse support comparison.
Source: det-sp-reduction-exceptional and clause (1)
(blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingReduction (P : WeilConjectures.PurityFiniteSetting.{u})
    {A : Type u} [CommRing A] [Finite A] (phi : P.Ring →+* A)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (finiteGeneralRingScalar phi X).obj (P.diagonalDualizing f) ⟶
      (Etale.FiniteSmoothPurity.exceptional (ULift.{u + 1, u} A) f).obj
        (finiteGeneralRingUnit (ULift.{u + 1, u} A) Y) :=
  (finiteGeneralRingScalarIso phi X (P.diagonalDualizing f)).hom ≫
    Etale.FiniteSmoothPurity.proCoefficientMap
      (RingHom.ulift.{u + 1, u + 1, u, u} phi) f
      (finiteGeneralRingUnit P.Coefficient Y) ≫
    (Etale.FiniteSmoothPurity.exceptional (ULift.{u + 1, u} A) f).map
      (finiteGeneralRingScalarUnitIso
        (RingHom.ulift.{u + 1, u + 1, u, u} phi) Y).hom

/-- Tensor a normalized Kummer sheaf comparison in the published ordered shifted model.
The empty power is the identity on the coefficient unit. No orientation is chosen.
Source: general-ring purity, exponent independence
(blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingLevelPower (A : Type (u + 1)) [CommRing A]
    (M N : ℕ) (hM : (M : A) = 0) (hN : (N : A) = 0) (T : Scheme.{u})
    (e : Scheme.finiteEtaleTateLine T M A hM ≅ Scheme.finiteEtaleTateLine T N A hN) :
    (d : ℕ) → Etale.FiniteSmoothPurity.line A M hM T d ≅
      Etale.FiniteSmoothPurity.line A N hN T d
  | 0 => Iso.refl _
  | d + 1 =>
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).mapIso
      (finiteGeneralRingLevelPower A M N hM hN T e d)).app _ ≪≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj
      (Etale.FiniteSmoothPurity.line A N hN T d)).mapIso
        ((shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso e))

/-- A Kummer level comparison in the ordinary sheaf presentation, fixed by the power
map into G_m and its action on every scalar/root generator. This is precisely the
root normalization of etaleFiniteTwistPullback, specialized to degree one.
Source: general-ring purity, proof (3) (blueprint: det-sp-finite-general-ring). -/
def FiniteGeneralRingKummerComparison (A : Type (u + 1)) [CommRing A]
    (M N : ℕ) (hM : (M : A) = 0) (hN : (N : A) = 0) (T : Scheme.{u})
    (q : T.rootsOfUnitySheaf M ⟶ T.rootsOfUnitySheaf N)
    (e : Scheme.finiteEtaleTateLine T M A hM ≅ Scheme.finiteEtaleTateLine T N A hN) :
    Prop :=
  q ≫ kernel.ι (N • 𝟙 T.gmSheaf) = (M / N) • kernel.ι (M • 𝟙 T.gmSheaf) ∧
    ∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf M).obj.obj W),
      e.hom.hom.app W (Scheme.finiteEtaleTateOneGenerator A M T hM W a z) =
        Scheme.finiteEtaleTateOneGenerator A N T hN W a (q.hom.app W z)

/-- The unital map from the Q_ell quotient to A through its uniquely specified
prime-ring identification. A unital ring equivalence with Z/N is unique, so this
conclusion datum cannot select a different scalar action.
Source: general-ring purity, R=Z/ell^n (blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingCoefficientMap (P : WeilConjectures.PurityFiniteSetting.{u})
    (A : Type u) [CommRing A] (hA : (P.diagonalExponent : A) = 0)
    (e : P.Ring ≃+* ULift.{u} (ZMod P.diagonalExponent)) : P.Ring →+* A :=
  (ZMod.castHom
    ((CharP.cast_eq_zero_iff A (ringChar A) P.diagonalExponent).mp hA) A).comp
      (ULift.ringEquiv.toRingHom.comp e.toRingHom)

/-- Scalar extension of the recorded Q_ell diagonal orientation, followed by the
actual site/scalar comparison and the generator-normalized Tate comparison.
Source: clause (1) (blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingOrientationExtension (P : WeilConjectures.PurityFiniteSetting.{u})
    {A : Type u} [CommRing A] [Finite A] (phi : P.Ring →+* A)
    (hA : (P.diagonalExponent : ULift.{u + 1, u} A) = 0)
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasCompactification f]
    (t : Etale.FiniteSmoothPurity.CoefficientLineComparison
      (RingHom.ulift.{u + 1, u + 1, u, u} phi) P.diagonalExponent P.diagonalExponent
      P.diagonalExponent_annihilates hA X) :
    (finiteGeneralRingScalar phi X).obj (P.diagonalDualizing f) ≅
      (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).obj
        (Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} A) P.diagonalExponent hA X d) :=
  (finiteGeneralRingScalar phi X).mapIso (P.diagonalDualizingObject d f aY) ≪≫
    finiteGeneralRingScalarIso phi X (P.diagonalTwist X d) ≪≫
    (pbcComparisonReduction X (RingHom.ulift.{u + 1, u + 1, u, u} phi)).app
      (P.diagonalTwistEtale X d) ≪≫
    (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).mapIso (t.tensorPower d)

/-- The actual purity map after the prescribed common-level Tate comparison.
This only names the displayed tensor composite; its arrow is not chosen.
Source: general-ring purity, exponent-independence formula
(blueprint: det-sp-finite-general-ring). -/
def finiteGeneralRingLevelGamma (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M N : ℕ) (hM : (M : A) = 0) (hN : (N : A) = 0) (d : ℕ)
    (b : Scheme.finiteEtaleTateLine X M A hM ≅ Scheme.finiteEtaleTateLine X N A hN)
    (alpha : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅
      Etale.FiniteSmoothPurity.line A N hN X d)
    (K : Etale.FiniteSmoothPurity.proCategory A Y) :
    (Etale.FiniteSmoothPurity.proSource A f
      (Etale.FiniteSmoothPurity.line A M hM X d)).obj K ⟶
      (Etale.FiniteSmoothPurity.exceptional A f).obj K :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((Etale.FiniteSmoothPurity.proPullback A f).obj K)).map
      ((Etale.FiniteSmoothPurity.comparison A X).map
        (finiteGeneralRingLevelPower A M N hM hN X b d).hom) ≫
    Etale.FiniteSmoothPurity.proGamma A f _ alpha K

/-- Invertibility and naturality of the specified projection-formula/counit purity map.
The coefficient ring is abstract so concrete coefficient structures are elaborated once.
Source: general-ring purity, clause (3) (blueprint: det-sp-finite-general-ring). -/
def FiniteGeneralRingTensorFormula (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : Etale.DerivedCategoryModule A X)
    (alpha : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅ L) : Prop :=
  (∀ K : Etale.FiniteSmoothPurity.proCategory A Y,
    Etale.FiniteSmoothPurity.IsCtf A Y K →
      Etale.FiniteSmoothPurity.IsCtf A X ((Etale.FiniteSmoothPurity.exceptional A f).obj K) ∧
      IsIso (Etale.FiniteSmoothPurity.proGamma A f L alpha K)) ∧
  (∀ (K K' : Etale.FiniteSmoothPurity.proCategory A Y),
    Etale.FiniteSmoothPurity.IsCtf A Y K →
    Etale.FiniteSmoothPurity.IsCtf A Y K' → ∀ a : K ⟶ K',
      (Etale.FiniteSmoothPurity.proSource A f L).map a ≫
          Etale.FiniteSmoothPurity.proGamma A f L alpha K' =
        Etale.FiniteSmoothPurity.proGamma A f L alpha K ≫
          (Etale.FiniteSmoothPurity.exceptional A f).map a)

/-- Equality of the full purity maps through the common maximum exponent, using
Kummer power maps fixed on scalar/root generators and the direct Rees normalization.
Source: general-ring purity, clause (3), final assertion and proof
(blueprint: det-sp-finite-general-ring). -/
def FiniteGeneralRingLevelIndependence (A : Type (u + 1)) [CommRing A] [Finite A]
    (ell n : ℕ) [Fact ell.Prime] (hA : ((ell ^ n : ℕ) : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] (d : ℕ) (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (geometry : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (hUnits : ∀ m : ℕ, 1 ≤ m → IsUnit ((ell ^ m : ℕ) : Γ(X, ⊤)))
    (alpha : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA X d) : Prop :=
  ∀ (n' : ℕ) (hn' : 1 ≤ n') (hA' : ((ell ^ n' : ℕ) : A) = 0),
    ∃ hM : ((ell ^ max n n' : ℕ) : A) = 0,
    ∃ (q : X.rootsOfUnitySheaf (ell ^ max n n') ⟶ X.rootsOfUnitySheaf (ell ^ n))
      (q' : X.rootsOfUnitySheaf (ell ^ max n n') ⟶ X.rootsOfUnitySheaf (ell ^ n'))
      (b : Scheme.finiteEtaleTateLine X (ell ^ max n n') A hM ≅
        Scheme.finiteEtaleTateLine X (ell ^ n) A hA)
      (b' : Scheme.finiteEtaleTateLine X (ell ^ max n n') A hM ≅
        Scheme.finiteEtaleTateLine X (ell ^ n') A hA')
      (alpha' : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅
        Etale.FiniteSmoothPurity.line A (ell ^ n') hA' X d),
      FiniteGeneralRingKummerComparison A _ _ hM hA X q b ∧
      FiniteGeneralRingKummerComparison A _ _ hM hA' X q' b' ∧
      Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n')
        (pow_pos (Fact.out : ell.Prime).pos n') hA' f d geometry (hUnits n' hn') alpha' ∧
      alpha.hom ≫ (finiteGeneralRingLevelPower A _ _ hM hA X b d).inv =
        alpha'.hom ≫ (finiteGeneralRingLevelPower A _ _ hM hA' X b' d).inv ∧
      ∀ K : Etale.FiniteSmoothPurity.proCategory A Y,
        Etale.FiniteSmoothPurity.IsCtf A Y K →
        finiteGeneralRingLevelGamma A f _ _ hM hA d b alpha K =
          finiteGeneralRingLevelGamma A f _ _ hM hA' d b' alpha' K

/-- The three general-ring clauses at one coefficient-independent compactification.
All auxiliary geometric witnesses are proofs. The only isomorphism data are either
fixed by the scalar/root formulas, or constrained by the actual diagonal/deformation
normalization and coefficient-comparison equation. The functor denoted exceptional
here unfolds to sfFiniteExceptionalAt on the selected compactification.
Source: general-ring purity, clauses (1)--(3) and proof (1)--(3)
(blueprint: det-sp-finite-general-ring). -/
def FiniteGeneralRingAt (P : WeilConjectures.PurityFiniteSetting.{u})
    (A : Type u) [CommRing A] [Finite A] (hA : (P.diagonalExponent : A) = 0)
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (hX : IsNoetherian X) (hY : IsNoetherian Y) (hqc : QuasiCompact f)
    (hc : HasCompactification f) : Prop :=
  letI := hX
  letI := hY
  letI := hqc
  letI := hc
  ∃ e : P.Ring ≃+* ULift.{u} (ZMod P.diagonalExponent),
  ∃ t : Etale.FiniteSmoothPurity.CoefficientLineComparison
      (RingHom.ulift.{u + 1, u + 1, u, u} (finiteGeneralRingCoefficientMap P A hA e))
      P.diagonalExponent P.diagonalExponent P.diagonalExponent_annihilates
      (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) X,
  ∃ theta :
      (Etale.FiniteSmoothPurity.exceptional (ULift.{u + 1, u} A) f).obj
        (finiteGeneralRingUnit (ULift.{u + 1, u} A) Y) ≅
      (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).obj
        (Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} A) P.diagonalExponent
          (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) X d),
  ∃ alpha : Etale.dualizingComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ≅
      Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} A) P.diagonalExponent
        (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) X d,
  ∃ geometry : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f),
    IsIso (finiteGeneralRingReduction P (finiteGeneralRingCoefficientMap P A hA e) f) ∧
    finiteGeneralRingReduction P (finiteGeneralRingCoefficientMap P A hA e) f ≫
        theta.hom =
      (finiteGeneralRingOrientationExtension P (finiteGeneralRingCoefficientMap P A hA e)
        (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) d f aY t).hom ∧
    IsIso (finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f) ∧
    finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f ≫ theta.hom =
      (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).map alpha.hom ∧
    Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} A)
      P.diagonalExponent (pow_pos P.coefficients.prime.out.pos P.level)
      (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) f d geometry
      (P.diagonalExponent_isUnit (f ≫ aY)) alpha ∧
    FiniteGeneralRingTensorFormula (ULift.{u + 1, u} A) f _ alpha ∧
    FiniteGeneralRingLevelIndependence (ULift.{u + 1, u} A)
      P.coefficients.l P.level
      (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) d f geometry
      (fun m hm ↦ ({ P with level := m, level_pos := hm } :
        WeilConjectures.PurityFiniteSetting).diagonalExponent_isUnit (f ≫ aY)) alpha
```

## New

The identical declarations above are now in
Sheaf.SecSmoothPurity.FiniteGeneralRingData. The old module publicly imports that module;
it keeps finiteGeneralRingSmoothPurity with exactly its original signature, and imports
three proof-step modules privately. No declaration is renamed or has its data changed.

## Users

`tools/downstream.py Sheaf.SecSmoothPurity.FiniteGeneralRing` reports all nine downstream
modules below. None requires adaptation: the extraction preserves public availability
and definitional equality. Holder is immaterial because no consumer is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicUnitTraceConstruction | Not adapted; claim unchanged | Identical public API and definitions. |
| Sheaf.Paper.AdicUnitTraceReductionData | Not adapted; claim unchanged | Identical public API and definitions. |
| Sheaf.Paper.AdicUnitTraceScalarData | Not adapted; claim unchanged | Identical public API and definitions. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | Not adapted; claim unchanged | Identical public API and definitions. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | Not adapted; claim unchanged | Identical public API and definitions. |
| Sheaf.Paper.FiniteDncNormalizationReduction | Not adapted; claim unchanged | Identical public API and definitions. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | Not adapted; claim unchanged | Identical public API and definitions. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | Not adapted; claim unchanged | Identical public API and definitions. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | Not adapted; claim unchanged | Identical public API and definitions. |

## Status

landed 20261025T124336-L-1979690 2026-10-25 (merge of deliver/X2/Sheaf.SecSmoothPurity.FiniteGeneralRing)
