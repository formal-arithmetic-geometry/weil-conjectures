# Normalized coefficient error-tower declarations

## Reason

Move the existing definitions verbatim into `Sheaf.Paper.NormalizedErrorTowerData` so that
the strict tensor-fiber lemma can use them without importing its consumer theorem.
All names, binders, universes, bodies, and visibility are unchanged. The original module
publicly imports the data module, preserving its public interface and its public imports
transitively. This is a location change, with no change to target meaning.

## Old

In `Sheaf.Paper.NormalizedErrorTowerVanishing`:

```lean
/-- Restrict a finite-level complex to the actual completed coefficient ring.
Source: sk-lem-sp-tower, coefficient tensor calculation
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
abbrev spErrorRestrict (n : ℕ) :=
  (SheafOfModules.restrictScalars.{max u (t + 1)}
    (spCompletedEllProjection l E T n)).mapHomologicalComplex (.up ℤ)

/-- Restriction of scalars preserves the underlying abelian-group sections exactly.
This identity with an explicit endpoint prevents repeated unfolding of coefficient maps.
Source: sk-lem-sp-tower, semilinear maps
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorSection {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S) (M : SheafOfModules.{r} S) (U : Cᵒᵖ)
    (x : ((SheafOfModules.restrictScalars φ).obj M).val.obj U) : M.val.obj U := x

/-- A pure tensor in the existing sheaf tensor product, using its sheafification unit.
Source: sk-lem-sp-tower, balanced tensor formulas; Stacks 03EK
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorPure {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
    (M N : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (M ⊗ N).val.obj U :=
  (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)).unit.app
        (M.val ⊗ N.val)).app U (x ⊗ₜ[R.obj.obj U] y))

/-- A sheafified pure tensor in the (p,q) summand of the existing direct-sum total tensor.
Source: sk-lem-sp-tower; Stacks 0G6E
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorGenerator {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
    (P Q : CochainComplex (Modules R) ℤ) (p q : ℤ) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((((total R).obj P).obj Q).X (p + q)).val.obj U :=
  (ι R P Q p q (p + q) rfl).val.app U (spErrorPure R (P.X p) (Q.X q) U x y)

/-- Canonical augmentation of the coefficient two-term complex. The chosen map is
uniquely determined by the reduction equation in SpRelativeFiberComparison: the target
is concentrated in degree zero. No coefficient object is chosen from mere existence.
Source: sk-lem-sp-tower, coefficient fiber calculation
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorCoefficientAugmentation (n m : ℕ) (h : m ≤ n) :=
  (sp_ell_coefficient_fiber l E T n n m le_rfl h).choose

/-- The recorded finite coefficient fiber over B_(n+1), with its normalized augmentation.
Source: sk-lem-sp-tower, coefficient fiber calculation
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
abbrev spErrorCoefficientFiber (n m : ℕ) (h : m ≤ n) :=
  spRelativeFiber l E T n n m le_rfl h (spErrorCoefficientAugmentation l E T n m h)

/-- Actual B_(n+1)-total tensor with B_(m+1), then restriction to R.
Source: sk-lem-sp-tower, S_n definition
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
abbrev spErrorReduction (Q : ∀ n : ℕ,
    CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (n m : ℕ) (h : m ≤ n) :=
  (spErrorRestrict l E T n).obj
    (((total ((spCoefficientCommRings l E T).obj (op n))).obj (Q n)).obj
      ((CochainComplex.singleFunctor _ 0).obj (spRelativeCoefficient l E T n m h)))

/-- Actual tensor Q_n tensor_(B_n) F_(n,m), restricted to R.
Source: sk-lem-sp-tower, left term
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
abbrev spErrorFiberTensor (Q : ∀ n : ℕ,
    CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (n m : ℕ) (h : m ≤ n) :=
  (spErrorRestrict l E T n).obj
    (((total ((spCoefficientCommRings l E T).obj (op n))).obj (Q n)).obj
      (spErrorCoefficientFiber l E T n m h))

/-- Actual total tensor Q_n tensor_R K_(m+1), with K in degrees -1,0.
Source: sk-lem-sp-tower, middle term
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
abbrev spErrorMiddle (Q : ∀ n : ℕ,
    CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (n m : ℕ) :=
  ((total (completedIntegralCommRingSheafUnrestricted l E T)).obj
    ((spErrorRestrict l E T n).obj (Q n))).obj
      (principalKoszul (completedIntegralCommRingSheafUnrestricted l E T)
        (spCompletedScalar l E T l) m)

/-- Pure tensors x tensor b in S_n, with the degree-zero coefficient unitor exposed.
Source: sk-lem-sp-tower, reduction formula
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorReductionGenerator (Q : ∀ n : ℕ,
    CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (n m : ℕ) (h : m ≤ n) (p : ℤ) (U : T.ProEtᵒᵖ)
    (x : ((Q n).X p).val.obj U) (b : (spCoefficientRing l E T m).obj.obj U) :
    ((spErrorReduction l E T Q n m h).X p).val.obj U :=
  (ι ((spCoefficientCommRings l E T).obj (op n)) (Q n)
    ((CochainComplex.singleFunctor _ 0).obj (spRelativeCoefficient l E T n m h))
      p 0 p (add_zero p)).val.app U
    (spErrorPure ((spCoefficientCommRings l E T).obj (op n)) ((Q n).X p) _ U x
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (spRelativeCoefficient l E T n m h)).inv.val.app U b))

/-- The actual two-term coefficient tensor before its associativity identification.
Source: sk-lem-sp-tower, middle identification
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
abbrev spErrorCoefficientTensor (Q : ∀ n : ℕ,
    CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (n m : ℕ) :=
  (spErrorRestrict l E T n).obj
    (((total ((spCoefficientCommRings l E T).obj (op n))).obj (Q n)).obj
      (spRelativeKoszul l E T n n m le_rfl))

/-- The degree -1 generator of a scalar cone on a degree-zero module.
Source: sk-lem-sp-tower, two-term Koszul convention
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorConeLeft {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} [Abelian (SheafOfModules.{r} R)]
    [HasBinaryBiproducts (SheafOfModules.{r} R)]
    {M : SheafOfModules.{r} R} (f : M ⟶ M) (U : Cᵒᵖ) (x : M.val.obj U) :=
  ((CochainComplex.mappingCone.inl ((CochainComplex.singleFunctor _ 0).map f)).v
      0 (-1) (by decide)).val.app U
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv.val.app U x)

/-- The degree zero generator of a scalar cone on a degree-zero module.
Source: sk-lem-sp-tower, two-term Koszul convention
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorConeRight {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} [Abelian (SheafOfModules.{r} R)]
    [HasBinaryBiproducts (SheafOfModules.{r} R)]
    {M : SheafOfModules.{r} R} (f : M ⟶ M) (U : Cᵒᵖ) (x : M.val.obj U) :=
  ((CochainComplex.mappingCone.inr ((CochainComplex.singleFunctor _ 0).map f)).f 0).val.app U
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv.val.app U x)

/-- The existing scalar arrow defining the completed Koszul complex.
Source: sk-lem-sp-tower, K_m definition
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
abbrev spErrorKoszulScalar (m : ℕ) :=
  endoPow (globalSectionMultiplication (completedIntegralCommRingSheafUnrestricted l E T)
    (spCompletedScalar l E T l)) (m + 1)

/-- A strict semilinear transition at any pair of coefficient levels.
Source: sk-lem-sp-tower, hypothesis on Q
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
abbrev SpErrorTransitions (Q : ∀ n : ℕ,
    CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ) :=
  ∀ (n m : ℕ) (h : m ≤ n), Q n ⟶
    ((SheafOfModules.restrictScalars.{max u (t + 1)}
      (spLevelReduction l E T n m h)).mapHomologicalComplex (.up ℤ)).obj (Q m)

/-- The underlying section map of a semilinear chain transition, with its target exposed.
Source: sk-lem-sp-tower, hypothesis on Q
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorTransitionValue (Q : ∀ n : ℕ,
    CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (q : SpErrorTransitions l E T Q) (n m : ℕ) (h : m ≤ n) (p : ℤ) (U : T.ProEtᵒᵖ)
    (x : ((Q n).X p).val.obj U) : ((Q m).X p).val.obj U :=
  spErrorSection (spLevelReduction l E T n m h) ((Q m).X p) U
    (((q n m h).f p).val.app U x)

/-- Exact normalization of the transition-induced reduction, on every tensor generator.
This is the map x tensor b ↦ b q(x), rather than an unspecified comparison map.
Source: sk-lem-sp-tower, normalization hypothesis
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def SpErrorReductionFormula (Q : ∀ n : ℕ,
    CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (q : SpErrorTransitions l E T Q) (n m : ℕ) (h : m ≤ n)
    (ρ : spErrorReduction l E T Q n m h ⟶ (spErrorRestrict l E T m).obj (Q m)) : Prop :=
  ∀ (p : ℤ) (U : T.ProEtᵒᵖ) (x : ((Q n).X p).val.obj U)
    (b : (spCoefficientRing l E T m).obj.obj U),
    spErrorSection (spCompletedEllProjection l E T m) ((Q m).X p) U
      ((ρ.f p).val.app U (spErrorReductionGenerator l E T Q n m h p U x b)) =
        b • spErrorTransitionValue l E T Q q n m h p U x

/-- Rearrange a strict R-tower using the recorded complex-of-towers construction.
Source: Stacks 0941; sk-lem-sp-tower, strict triangles
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
abbrev spErrorTowerComplex := koszulTowerComplex (completedIntegralCommRingSheafUnrestricted l E T)

/-- The identity-cone diagonal into the total derived limit of a constant tower.
It is the ordinary constant/limit unit followed by the derived comparison.
Source: sk-lem-sp-tower, diagonal normalization; Stacks 0940
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorDiagonal
    [HasDerivedCategory.{w}
      (SheafOfModules.{max u (t + 1)} (completedIntegralCoefficientSheafUnrestricted l E T))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤
      SheafOfModules.{max u (t + 1)} (completedIntegralCoefficientSheafUnrestricted l E T))]
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{max u (t + 1)}
        (completedIntegralCoefficientSheafUnrestricted l E T)) ⥤
      DerivedCategory.{w} (SheafOfModules.{max u (t + 1)}
        (completedIntegralCoefficientSheafUnrestricted l E T)))
    (κ : (lim : (ℕᵒᵖ ⥤ SheafOfModules.{max u (t + 1)}
        (completedIntegralCoefficientSheafUnrestricted l E T)) ⥤ _).mapHomologicalComplex
      (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (P : CochainComplex (SheafOfModules.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E T)) ℤ) :=
  DerivedCategory.Q.{w}.map
    ((Adjunction.mapHomologicalComplex (.up ℤ) (constLimAdj :
      (Functor.const ℕᵒᵖ : SheafOfModules.{max u (t + 1)}
        (completedIntegralCoefficientSheafUnrestricted l E T) ⥤ _) ⊣ lim)).unit.app P) ≫
      κ.app (((Functor.const ℕᵒᵖ : SheafOfModules.{max u (t + 1)}
        (completedIntegralCoefficientSheafUnrestricted l E T) ⥤ _).mapHomologicalComplex
            (.up ℤ)).obj P)

/-- The module category over the existing completed coefficient ring.
Source: sk-lem-sp-tower, D(R) (blueprint: lem-sp-normalized-error-tower-vanishing). -/
abbrev spErrorModules :=
  SheafOfModules.{max u (t + 1)} (completedIntegralCoefficientSheafUnrestricted l E T)

/-- The tail S, assembled from adjacent actual reduction-complex maps.
Source: sk-lem-sp-tower, n ≥ m (blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorTailS (Q : ∀ n : ℕ,
    CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (m : ℕ) (s : ∀ j : ℕ, spErrorReduction l E T Q (m + (j + 1)) m (by omega) ⟶
      spErrorReduction l E T Q (m + j) m (by omega)) :=
  Functor.ofOpSequence
    (X := fun j ↦ spErrorReduction l E T Q (m + j) m (by omega)) s

/-- The tail M, assembled from adjacent actual Koszul-tensor maps.
Source: sk-lem-sp-tower, middle tower
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorTailM (Q : ∀ n : ℕ,
    CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (m : ℕ) (t : ∀ j : ℕ, spErrorMiddle l E T Q (m + (j + 1)) m ⟶
      spErrorMiddle l E T Q (m + j) m) :=
  Functor.ofOpSequence (X := fun j ↦ spErrorMiddle l E T Q (m + j) m) t

/-- Scalar multiplication of the ordinary cochain-shift image of a chain map.
Source: sk-lem-sp-tower, powered error transitions
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorPoweredMap {A : Type c} [Category.{v} A] [Preadditive A]
    (b : ℕ) {P S : CochainComplex A ℤ} (f : P ⟶ S) :
    P⟦(1 : ℤ)⟧ ⟶ S⟦(1 : ℤ)⟧ :=
  b • (CategoryTheory.shiftFunctor (CochainComplex A ℤ) (1 : ℤ)).map f

/-- The powered shift tower: adjacent arrows are ell times the shifted S arrow.
Its composite over any gap is consequently ell to that gap times the usual shifted arrow.
Source: sk-lem-sp-tower, normalized left transitions
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorPoweredShift (Q : ∀ n : ℕ,
    CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (m : ℕ) (s : ∀ j : ℕ, spErrorReduction l E T Q (m + (j + 1)) m (by omega) ⟶
      spErrorReduction l E T Q (m + j) m (by omega)) :=
  Functor.ofOpSequence
    (X := fun j ↦ (spErrorReduction l E T Q (m + j) m (by omega))⟦(1 : ℤ)⟧)
    (fun j ↦ spErrorPoweredMap l (s j))

/-- The degree -1 generator of the shifted coefficient cone.
Source: sk-lem-sp-tower, coefficient reduction on the fiber
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorFiberLeftElement (n m : ℕ) (h : m ≤ n) (U : T.ProEtᵒᵖ)
    (b : (spCoefficientRing l E T n).obj.obj U) :
    ((spErrorCoefficientFiber l E T n m h).X (-1)).val.obj U :=
  (CochainComplex.shiftFunctorObjXIso
    (CochainComplex.mappingCone (spErrorCoefficientAugmentation l E T n m h))
      (-1) (-1) (-2) rfl).inv.val.app U
    (((CochainComplex.mappingCone.inl (spErrorCoefficientAugmentation l E T n m h)).v
      (-1) (-2) (by decide)).val.app U
        (spErrorConeLeft (l ^ (m + 1) • 𝟙 (spRelativeCoefficient l E T n n le_rfl)) U b))

/-- The degree zero generator of the shifted coefficient cone.
Source: sk-lem-sp-tower, coefficient reduction on the fiber
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorFiberMiddleElement (n m : ℕ) (h : m ≤ n) (U : T.ProEtᵒᵖ)
    (b : (spCoefficientRing l E T n).obj.obj U) :
    ((spErrorCoefficientFiber l E T n m h).X 0).val.obj U :=
  (CochainComplex.shiftFunctorObjXIso
    (CochainComplex.mappingCone (spErrorCoefficientAugmentation l E T n m h))
      (-1) 0 (-1) rfl).inv.val.app U
    (((CochainComplex.mappingCone.inl (spErrorCoefficientAugmentation l E T n m h)).v
      0 (-1) (by decide)).val.app U
        (spErrorConeRight (l ^ (m + 1) • 𝟙 (spRelativeCoefficient l E T n n le_rfl)) U b))

/-- The degree one generator of the shifted coefficient cone.
Source: sk-lem-sp-tower, identity on the B_m coordinate of the fiber transition
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorFiberRightElement (n m : ℕ) (h : m ≤ n) (U : T.ProEtᵒᵖ)
    (b : (spCoefficientRing l E T m).obj.obj U) :
    ((spErrorCoefficientFiber l E T n m h).X 1).val.obj U :=
  (CochainComplex.shiftFunctorObjXIso
    (CochainComplex.mappingCone (spErrorCoefficientAugmentation l E T n m h))
      (-1) 1 0 rfl).inv.val.app U
    (((CochainComplex.mappingCone.inr (spErrorCoefficientAugmentation l E T n m h)).f
      0).val.app U ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (spRelativeCoefficient l E T n m h)).inv.val.app U b))

/-- A generator of the actual R-restricted coefficient-fiber tensor.
Source: sk-lem-sp-tower, strict left tower
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def spErrorFiberTensorGenerator (Q : ∀ n : ℕ,
    CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (n m : ℕ) (h : m ≤ n) (p z : ℤ) (U : T.ProEtᵒᵖ)
    (x : ((Q n).X p).val.obj U)
    (y : ((spErrorCoefficientFiber l E T n m h).X z).val.obj U) :
    ((spErrorFiberTensor l E T Q n m h).X (p + z)).val.obj U :=
  spErrorGenerator ((spCoefficientCommRings l E T).obj (op n)) (Q n)
    (spErrorCoefficientFiber l E T n m h) p z U x y

/-- The strict tensor-fiber transition on its three coefficient generators. The first
 two coordinates reduce from B_n' to B_n, while the last B_m coordinate stays fixed.
Source: sk-lem-sp-tower, proof step 1, strict semilinear tensor transitions
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def SpErrorFiberTransitionFormula (Q : ∀ n : ℕ,
    CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (q : SpErrorTransitions l E T Q) (n' n m : ℕ) (hn : n ≤ n') (hm : m ≤ n)
    (f : spErrorFiberTensor l E T Q n' m (hm.trans hn) ⟶
      spErrorFiberTensor l E T Q n m hm) : Prop :=
  ∀ (p : ℤ) (U : T.ProEtᵒᵖ) (x : ((Q n').X p).val.obj U),
    (∀ b : (spCoefficientRing l E T n').obj.obj U,
      (f.f (p + -1)).val.app U
        (spErrorFiberTensorGenerator l E T Q n' m (hm.trans hn) p (-1) U x
          (spErrorFiberLeftElement l E T n' m (hm.trans hn) U b)) =
      spErrorFiberTensorGenerator l E T Q n m hm p (-1) U
        (spErrorTransitionValue l E T Q q n' n hn p U x)
        (spErrorFiberLeftElement l E T n m hm U
          ((spLevelReduction l E T n' n hn).hom.app U b))) ∧
    (∀ b : (spCoefficientRing l E T n').obj.obj U,
      (f.f (p + 0)).val.app U
        (spErrorFiberTensorGenerator l E T Q n' m (hm.trans hn) p 0 U x
          (spErrorFiberMiddleElement l E T n' m (hm.trans hn) U b)) =
      spErrorFiberTensorGenerator l E T Q n m hm p 0 U
        (spErrorTransitionValue l E T Q q n' n hn p U x)
        (spErrorFiberMiddleElement l E T n m hm U
          ((spLevelReduction l E T n' n hn).hom.app U b))) ∧
    (∀ b : (spCoefficientRing l E T m).obj.obj U,
      (f.f (p + 1)).val.app U
        (spErrorFiberTensorGenerator l E T Q n' m (hm.trans hn) p 1 U x
          (spErrorFiberRightElement l E T n' m (hm.trans hn) U b)) =
      spErrorFiberTensorGenerator l E T Q n m hm p 1 U
        (spErrorTransitionValue l E T Q q n' n hn p U x)
        (spErrorFiberRightElement l E T n m hm U b))

/-- The tensor associativity identification in the explicit two-term coefficient model.
The two equations say x tensor (b tensor 1) ↦ bx tensor 1 in degrees -1 and 0;
these generate the tensor, so they specify the whole identification.
Source: sk-lem-sp-tower, middle identification
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def SpErrorAssociativityFormula (Q : ∀ n : ℕ,
    CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (n m : ℕ) (e : spErrorCoefficientTensor l E T Q n m ≅ spErrorMiddle l E T Q n m) :
    Prop :=
  ∀ (p : ℤ) (U : T.ProEtᵒᵖ) (x : ((Q n).X p).val.obj U)
    (b : (spCoefficientRing l E T n).obj.obj U),
    ((e.hom.f (p + -1)).val.app U
      (spErrorGenerator ((spCoefficientCommRings l E T).obj (op n)) (Q n)
        (spRelativeKoszul l E T n n m le_rfl) p (-1) U x
          (spErrorConeLeft (l ^ (m + 1) • 𝟙 _) U b)) =
      spErrorGenerator (completedIntegralCommRingSheafUnrestricted l E T)
        ((spErrorRestrict l E T n).obj (Q n))
        (principalKoszul (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T l) m) p (-1) U (b • x)
            (spErrorConeLeft (spErrorKoszulScalar l E T m) U
              (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U))) ∧
    ((e.hom.f (p + 0)).val.app U
      (spErrorGenerator ((spCoefficientCommRings l E T).obj (op n)) (Q n)
        (spRelativeKoszul l E T n n m le_rfl) p 0 U x
          (spErrorConeRight (l ^ (m + 1) • 𝟙 _) U b)) =
      spErrorGenerator (completedIntegralCommRingSheafUnrestricted l E T)
        ((spErrorRestrict l E T n).obj (Q n))
        (principalKoszul (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T l) m) p 0 U (b • x)
            (spErrorConeRight (spErrorKoszulScalar l E T m) U
              (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)))

variable [HasDerivedCategory.{w} (spErrorModules l E T)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ spErrorModules l E T)]

/-- The comparison transformation for a total right-derived inverse-limit functor.
Source: Stacks 0940; sk-lem-sp-tower
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
abbrev spErrorLimitComparison
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ spErrorModules l E T) ⥤
      DerivedCategory.{w} (spErrorModules l E T)) :=
  (lim : (ℕᵒᵖ ⥤ spErrorModules l E T) ⥤ spErrorModules l E T).mapHomologicalComplex
      (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF

/-- The complete conclusion of the normalized error-tower calculation. This predicate
packages the specified strict maps, their formulas and their derived-limit properties;
it is a witness to the theorem, not an additional hypothesis on Q.

Source: sk-lem-sp-tower, proof paragraph, normalization and vanishing of the left term;
Bhatt--Scholze, Lemmas 3.5.4--3.5.7
(blueprint: lem-sp-normalized-error-tower-vanishing). -/
def SpNormalizedErrorDiagram
    (Q : ∀ n : ℕ,
      CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (q : SpErrorTransitions l E T Q) (m : ℕ)
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ spErrorModules l E T) ⥤
      DerivedCategory.{w} (spErrorModules l E T))
    (κ : spErrorLimitComparison l E T RF) : Prop :=
  ∃ (A : ℕᵒᵖ ⥤ CochainComplex (spErrorModules l E T) ℤ),
  ∃ (s : ∀ j : ℕ, spErrorReduction l E T Q (m + (j + 1)) m (by omega) ⟶
    spErrorReduction l E T Q (m + j) m (by omega)),
  ∃ (t : ∀ j : ℕ, spErrorMiddle l E T Q (m + (j + 1)) m ⟶
    spErrorMiddle l E T Q (m + j) m),
  ∃ (a : spErrorTailM l E T Q m t ⟶ spErrorTailS l E T Q m s),
  ∃ (left : A ⟶ spErrorTailM l E T Q m t),
  ∃ (ρ : spErrorTailS l E T Q m s ⟶
    (Functor.const ℕᵒᵖ).obj ((spErrorRestrict l E T m).obj (Q m))),
  ∃ (assoc : ∀ j : ℕ, spErrorCoefficientTensor l E T Q (m + j) m ≅
    spErrorMiddle l E T Q (m + j) m),
  ∃ (fiber : ∀ j : ℕ, spErrorFiberTensor l E T Q (m + j) m (by omega) ≅ A.obj (op j)),
  ∃ (η : spErrorPoweredShift l E T Q m s ⟶ A),
  ∃ (diagonal : DerivedCategory.Q.{w}.obj ((spErrorRestrict l E T m).obj (Q m)) ≅
    RF.obj (DerivedCategory.Q.{w}.obj
      (spErrorTowerComplex l E T
        ((Functor.const ℕᵒᵖ).obj ((spErrorRestrict l E T m).obj (Q m)))))),
  /- s_formula -/
  (∀ (j : ℕ) (p : ℤ) (U : T.ProEtᵒᵖ)
      (x : ((Q (m + (j + 1))).X p).val.obj U)
      (b : (spCoefficientRing l E T m).obj.obj U),
    ((s j).f p).val.app U
        (spErrorReductionGenerator l E T Q (m + (j + 1)) m (by omega) p U x b) =
      spErrorReductionGenerator l E T Q (m + j) m (by omega) p U
        (spErrorTransitionValue l E T Q q (m + (j + 1)) (m + j) (by omega) p U x) b) ∧
  /- t_formula -/
  (∀ (j : ℕ) (p z : ℤ) (U : T.ProEtᵒᵖ)
      (x : ((Q (m + (j + 1))).X p).val.obj U)
      (k : ((principalKoszul (completedIntegralCommRingSheafUnrestricted l E T)
        (spCompletedScalar l E T l) m).X z).val.obj U),
    ((t j).f (p + z)).val.app U
        (spErrorGenerator (completedIntegralCommRingSheafUnrestricted l E T)
          ((spErrorRestrict l E T (m + (j + 1))).obj (Q (m + (j + 1))))
          (principalKoszul (completedIntegralCommRingSheafUnrestricted l E T)
            (spCompletedScalar l E T l) m) p z U x k) =
      spErrorGenerator (completedIntegralCommRingSheafUnrestricted l E T)
        ((spErrorRestrict l E T (m + j)).obj (Q (m + j)))
        (principalKoszul (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T l) m) p z U
            (spErrorTransitionValue l E T Q q (m + (j + 1)) (m + j) (by omega) p U x) k) ∧
  /- a_left -/
  (∀ (j : ℕ) (p : ℤ) (U : T.ProEtᵒᵖ)
      (x : ((Q (m + j)).X p).val.obj U),
    (((a.app (op j)).f (p + -1)).val.app U
      (spErrorGenerator (completedIntegralCommRingSheafUnrestricted l E T)
        ((spErrorRestrict l E T (m + j)).obj (Q (m + j)))
        (principalKoszul (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T l) m) p (-1) U x
            (spErrorConeLeft (spErrorKoszulScalar l E T m) U
              (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)))) = 0) ∧
  /- a_right -/
  (∀ (j : ℕ) (p : ℤ) (U : T.ProEtᵒᵖ)
      (x : ((Q (m + j)).X p).val.obj U),
    (((a.app (op j)).f (p + 0)).val.app U
      (spErrorGenerator (completedIntegralCommRingSheafUnrestricted l E T)
        ((spErrorRestrict l E T (m + j)).obj (Q (m + j)))
        (principalKoszul (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T l) m) p 0 U x
            (spErrorConeRight (spErrorKoszulScalar l E T m) U
              (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)))) =
      spErrorGenerator ((spCoefficientCommRings l E T).obj (op (m + j))) (Q (m + j))
        ((CochainComplex.singleFunctor _ 0).obj
          (spRelativeCoefficient l E T (m + j) m (by omega))) p 0 U x
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (spRelativeCoefficient l E T (m + j) m (by omega))).inv.val.app U
            (1 : (spCoefficientRing l E T m).obj.obj U))) ∧
  /- assoc_formula -/
  (∀ j : ℕ, SpErrorAssociativityFormula l E T Q (m + j) m (assoc j)) ∧
  /- fiber_transition_formula -/
  (∀ j : ℕ,
    SpErrorFiberTransitionFormula l E T Q q (m + (j + 1)) (m + j) m (by omega) (by omega)
      ((fiber (j + 1)).hom ≫ A.map (homOfLE (Nat.le_succ j)).op ≫ (fiber j).inv)) ∧
  /- distinguished -/
  (∃ δ,
    Triangle.mk
      ((DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ spErrorModules l E T)).map
        (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E T) left))
      ((DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ spErrorModules l E T)).map
        (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E T) a)) δ ∈
      distTriang (DerivedCategory.{w} (ℕᵒᵖ ⥤ spErrorModules l E T))) ∧
  /- η_quasiIso -/
  (QuasiIso
    (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E T) η)) ∧
  /- η_levelwise -/
  (∀ j : ℕ, QuasiIso (η.app (op j))) ∧
  /- powered_transitions -/
  (∀ (j j' : ℕ) (h : j ≤ j'),
    (spErrorPoweredShift l E T Q m s).map (homOfLE h).op =
      spErrorPoweredMap (l ^ (j' - j))
        ((spErrorTailS l E T Q m s).map (homOfLE h).op)) ∧
  /- reduction_formula -/
  (∀ j : ℕ,
    SpErrorReductionFormula l E T Q q (m + j) m (by omega) (ρ.app (op j))) ∧
  /- reduction_quasiIso -/
  (∀ j : ℕ, QuasiIso (ρ.app (op j))) ∧
  /- limit_zero -/
  (IsZero (RF.obj (DerivedCategory.Q.{w}.obj (spErrorTowerComplex l E T A)))) ∧
  /- diagonal_formula -/
  (diagonal.hom =
    spErrorDiagonal l E T RF κ ((spErrorRestrict l E T m).obj (Q m))) ∧
  /- composite_isIso -/
  (IsIso
    (RF.map (DerivedCategory.Q.{w}.map
      (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E T) a)) ≫
      RF.map ((DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ spErrorModules l E T)).map
        (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E T) ρ)) ≫
      diagonal.inv))
```

## New

The declarations in the preceding block are verbatim in
`Sheaf.Paper.NormalizedErrorTowerData`; the original module re-exports them with:

```lean
public import Sheaf.Paper.NormalizedErrorTowerData
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NormalizedErrorTowerVanishing | K4 | Public re-export and proof from the strict construction |
| Sheaf.Paper.NormalizedStrictTensorFiber | new, K4 | Uses the relocated data in its statement |

`tools/downstream.py Sheaf.Paper.NormalizedErrorTowerVanishing --uses spErrorPure`
reports zero downstream modules, and the only original declaration-use module is the
item itself. A direct search for the original module name also finds no external importer.
The original DAG statement and parent dependencies remain; nothing is withdrawn.

## Status

landed 20261021T172402-L-3363646 2026-10-21 (merge of deliver/K4/Sheaf.Paper.NormalizedErrorTowerVanishing)
