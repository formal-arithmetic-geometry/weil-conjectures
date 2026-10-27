# WeilConjectures.OpenTensorQuotient comparison interfaces

## Reason

The two independent geometric and strict-cochain lemmas need to name the existing
interfaces, and the item must import those lemmas. Move the existing declaration
block verbatim to Sheaf.SixFunctors.OpenTensorQuotientData and publicly reexport it
from the original module. This removes the import cycle. This is an interface
extraction for proof dependencies, not a split to evade the compile limit.
Existing visibility, data, docstrings and universes are preserved. ScalarComparison.components
now uses ScalarComponents, whose body is its exact original universally quantified equation. No new data construction or choice from an unproved theorem occurs.
The block was compared with the original; the only substantive edit is naming the
ScalarComparison.components proposition to avoid repeating it in generated eliminators.

The original file also nearly exhausts the 60-second compile limit (55.8 seconds
in the server check). A profiled interface check shows repeated expansion of the
sheaf monoidal construction during type comparison. Local irreducibility
attributes bound this unfolding in the extracted interface and proof modules.
It changes no exported reducibility attribute or mathematical definition.

## Old

In Sheaf.SixFunctors.OpenTensorQuotientAugmentation, the following block:

```lean
/-- Strict towers, with their genuine quotient transitions. Source: Stacks 0941
(blueprint: lem-sf-open-tensor-quotient-augmentation). -/
abbrev Towers (W : Scheme.{u}) := ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E W) ℤ

/-- Postcomposition by the actual termwise open extension. Source: Stacks 0GL1
(blueprint: lem-sf-open-tensor-quotient-augmentation). -/
abbrev extendTower {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations l E j) : Towers l E U ⥤ Towers l E X :=
  (Functor.whiskeringRight _ _ _).obj (OpenSemilinearTensor.extensionComplex l E j o)

/-- A pure homogeneous tensor in the existing total complex. Source: Stacks 012Z
(blueprint: lem-sf-open-tensor-quotient-augmentation). -/
def totalSection (W : Scheme.{u})
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (p q : ℤ) (V : W.ProEtᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :=
  (OpenSemilinearTensor.summand l E W P Q p q (p + q) rfl).val.app V
    (tensorSection.{u + 1, u, u + 1} (ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
      (P.X p) (Q.X q) V x y)

/-- A strict tower of complexes read as a complex of strict towers. This is a real
transpose construction, so localization is in the category of systems itself.
Source: Stacks 0941 (blueprint: lem-sf-open-tensor-quotient-augmentation). -/
def transpose (W : Scheme.{u}) : Towers l E W ⥤
    CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ where
  obj T :=
    { X := fun i ↦ T ⋙ HomologicalComplex.eval _ _ i
      d := fun i k ↦
        { app := fun n ↦ (T.obj n).d i k
          naturality := fun _ _ f ↦ (T.map f).comm i k }
      shape := fun i k h ↦ NatTrans.ext (funext (fun n ↦ (T.obj n).shape i k h))
      d_comp_d' := fun i k m _ _ ↦ NatTrans.ext (funext (fun n ↦ (T.obj n).d_comp_d i k m)) }
  map f :=
    { f := fun i ↦
        { app := fun n ↦ (f.app n).f i
          naturality := fun _ _ g ↦ congrArg (fun a ↦ a.f i) (f.naturality g) }
      comm' := fun i k _ ↦ NatTrans.ext (funext (fun n ↦ (f.app n).comm i k)) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Functorial form of the existing strict reduction tower. Source: Stacks 06YY
(blueprint: lem-sf-open-tensor-quotient-augmentation). -/
def reductionTower (W : Scheme.{u}) :
    CochainComplex (scalarReductionSource l E W) ℤ ⥤ Towers l E W :=
  (Functor.ofOpSequence (X := fun n ↦ unrestrictedIntegralComplexFunctor l E W n)
    (unrestrictedIntegralTransition l E W)).flip

/-- The balancing comparison, with its full coefficient formula. The coefficient is
placed in the first factor and the second receives 1; factors are never exchanged.
Source: Stacks 03EK, 0GL1 (blueprint: lem-sf-open-tensor-quotient-augmentation). -/
structure Balanced (W : Scheme.{u})
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) where
  iso : (reductionTower l E W).obj
      ((OpenSemilinearTensor.total l E W).obj (P, Q)) ≅
    (integralOperationsTensorTowerFunctor l E W).obj (P, Q)
  coefficients : ∀ (n : ℕ) (p q : ℤ) (V : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V)
    (a : (integralCoefficientCommRingSheaf l E W n).obj.obj V),
    (((iso.hom.app (op n)).f (p + q)).val.app V)
      (unrestrictedIntegralTensorSection l E W n _ V a
        (totalSection l E W P Q p q V x y)) =
    integralOperationsTotalTensorSection l E W n P Q p q V
      (unrestrictedIntegralTensorSection l E W n (P.X p) V a x)
      (unrestrictedIntegralTensorSection l E W n (Q.X q) V 1 y)

/-- The existing signed total tensor before scalar restriction at the positive
coefficient level. Source: Stacks 012Z, 03EK
(blueprint: lem-sf-open-tensor-quotient-augmentation). -/
abbrev finiteTotal (W : Scheme.{u}) (n : ℕ) :=
  Functor.uncurry.obj ((MonoidalCategory.curriedTensor
    (integralOperationsFiniteModules l E W n)).map₂CochainComplex)

/-- The actual tensor quotient augmentation. Naturality is part of the map of strict
towers; normalization is on all homogeneous sections, not just derived evaluations.
Source: Stacks 03EK, 0941 (blueprint: lem-sf-open-tensor-quotient-augmentation). -/
structure Augmentation (W : Scheme.{u})
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) where
  map : (Functor.const ℕᵒᵖ).obj ((OpenSemilinearTensor.total l E W).obj (P, Q)) ⟶
    (integralOperationsTensorTowerFunctor l E W).obj (P, Q)
  sections : ∀ (n : ℕ) (p q : ℤ) (V : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    (((map.app (op n)).f (p + q)).val.app V)
      (totalSection l E W P Q p q V x y) =
    integralOperationsTotalTensorSection l E W n P Q p q V
      (unrestrictedIntegralTensorSection l E W n (P.X p) V 1 x)
      (unrestrictedIntegralTensorSection l E W n (Q.X q) V 1 y)

/-- Equality with the first coordinate of the specified tensor-completion chain map.
Its zero shifted coordinate is part of Tensor.canonical. Source: Bhatt--Scholze 3.4.10
(blueprint: lem-sf-open-tensor-quotient-augmentation). -/
def RoosNormalization (W : Scheme.{u}) (t : OpenFactorCoherence.Tensor l E W)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) (a : Augmentation l E W P Q) :
    Prop :=
  ∀ (n : ℕ) (i : ℤ), HEq ((a.map.app (op n)).f i)
    ((t.chain.app (P, Q) ≫ CochainComplex.mappingCocone.fst
      (constructibleTensorBoundary l E W P Q) ≫
      Pi.π (fun k ↦ (integralOperationsTensorLevel l E W k).obj (P, Q)) n).f i)

/-- Forget the coefficient system to completed-scalar towers, retaining all arrows.
Source: Stacks 0941 (blueprint: lem-sf-open-tensor-quotient-augmentation). -/
abbrev forgetSystems (W : Scheme.{u}) :=
  (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

/-- Scalar restriction commutes with open extension, before localization and naturally
on the entire strict system, including every quotient transition.
Source: Stacks 03DI, 0E8I (blueprint: lem-sf-open-tensor-quotient-augmentation). -/
structure ScalarCompatibility where
  finite : ∀ n : ℕ,
    IntegralOpenReduction.finiteExtension l E j o n ⋙ scalarReductionRestriction l E X n ≅
      scalarReductionRestriction l E U n ⋙ IntegralOpenReduction.extension l E j o
  systems : (IntegralOpenReduction.systemExtension l E j o).mapHomologicalComplex (.up ℤ) ⋙
      forgetSystems l E X ≅ forgetSystems l E U ⋙ extendTower l E j o
  evaluation : ∀ (C : CochainComplex (coefficientSequenceModules l E U) ℤ)
    (n : ℕ) (i : ℤ),
    HEq (((systems.hom.app C).app (op n)).f i)
      ((finite n).hom.app ((coefficientSequenceEvaluation l E U n).obj (C.X i)))

/-- The strict scalar map is the finite A_n-linear open comparison followed by the
canonical scalar-restriction identification. This fixes its inverse normalization.
Source: Stacks 0E8I, 0GL1 (blueprint: lem-sf-open-tensor-quotient-augmentation). -/
structure ScalarComparison (sc : ScalarCompatibility l E j o)
    (tc : IntegralOpenReduction.TensorComparison l E j o) where
  iso : OpenSemilinearTensor.extensionComplex l E j o ⋙ reductionTower l E X ≅
    reductionTower l E U ⋙ extendTower l E j o
  components : ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ) (n : ℕ) (i : ℤ),
    ((iso.hom.app Q).app (op n)).f i =
      (scalarReductionRestriction l E X n).map ((tc.ordinary n).hom.app (Q.X i)) ≫
        (sc.finite n).hom.app ((scalarReductionExtension l E U n).obj (Q.X i))

attribute [local irreducible] integralOperationsTensorTowerFunctor
  coefficientTotalTensor integralOperationsTensorLevel
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  unrestrictedIntegralComplexFunctor scalarReductionExistence unrestrictedIntegralReductionExistence

/-- The tensor augmentation square is an equality of strict chain-system maps.
Balancing identifies its finite tensor comparison with reduction of the same signed
open tensor chain isomorphism. Its localization is explicitly in D(strict towers).
Source: Stacks 0E8I, 0GL1 (blueprint: lem-sf-open-tensor-quotient-augmentation). -/
structure StrictSquare
    (tc : OpenSemilinearTensor.TotalComparison l E j o)
    (sc : ScalarCompatibility l E j o)
    (st : IntegralOpenReduction.TensorComparison l E j o)
    (r : ScalarComparison l E j o sc st)
    (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (F : CochainComplex (scalarReductionSource l E X) ℤ) where
  balancingX : Balanced l E X ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F
  balancingU : Balanced l E U Q ((OpenSemilinearTensor.restrictionComplex l E j o).obj F)
  upper : Augmentation l E X ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F
  lower : Augmentation l E U Q ((OpenSemilinearTensor.restrictionComplex l E j o).obj F)
  gamma : (integralOperationsTensorTowerFunctor l E X).obj
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F) ≅
    (extendTower l E j o).obj ((integralOperationsTensorTowerFunctor l E U).obj
      (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))
  finiteGamma : ∀ n : ℕ,
    (finiteTotal l E X n).obj
      ((unrestrictedIntegralFiniteComplex l E X n).obj
        ((OpenSemilinearTensor.extensionComplex l E j o).obj Q),
       (unrestrictedIntegralFiniteComplex l E X n).obj F) ≅
    ((IntegralOpenReduction.finiteExtension l E j o n).mapHomologicalComplex (.up ℤ)).obj
      ((finiteTotal l E U n).obj
        ((unrestrictedIntegralFiniteComplex l E U n).obj Q,
         (unrestrictedIntegralFiniteComplex l E U n).obj
           ((OpenSemilinearTensor.restrictionComplex l E j o).obj F)))
  finiteGammaRestriction : ∀ (n : ℕ) (i : ℤ),
    HEq ((gamma.hom.app (op n)).f i)
      ((scalarReductionRestriction l E X n).map ((finiteGamma n).hom.f i) ≫
        (sc.finite n).hom.app
          (((finiteTotal l E U n).obj
            ((unrestrictedIntegralFiniteComplex l E U n).obj Q,
             (unrestrictedIntegralFiniteComplex l E U n).obj
               ((OpenSemilinearTensor.restrictionComplex l E j o).obj F))).X i))
  reduction : ∀ (n : ℕᵒᵖ) (i : ℤ),
    HEq (((balancingX.iso.hom.app n).f i) ≫ ((gamma.hom.app n).f i))
      (((unrestrictedIntegralComplexFunctor l E X n.unop).map (tc.chain Q F).hom).f i ≫
        ((r.iso.hom.app ((OpenSemilinearTensor.total l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))).app n).f i ≫
        (IntegralOpenReduction.extension l E j o).map ((balancingU.iso.hom.app n).f i))
  lowerRoute : (Functor.const ℕᵒᵖ).obj ((OpenSemilinearTensor.total l E X).obj
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F)) ⟶
    (extendTower l E j o).obj ((integralOperationsTensorTowerFunctor l E U).obj
      (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))
  lowerRouteFormula : ∀ (n : ℕᵒᵖ) (i : ℤ),
    HEq ((lowerRoute.app n).f i)
      (((tc.chain Q F).hom.f i) ≫
        (IntegralOpenReduction.extension l E j o).map ((lower.map.app n).f i))
  square : upper.map ≫ gamma.hom = lowerRoute
  derivedSquare : DerivedCategory.Q.map ((transpose l E X).map upper.map) ≫
      DerivedCategory.Q.map ((transpose l E X).map gamma.hom) =
    DerivedCategory.Q.map ((transpose l E X).map lowerRoute)

/-- The actual integral derived tensor comparison on these representatives.
It is the localization of the same normalized total chain isomorphism.
Source: Stacks 0GL1 (blueprint: lem-sf-open-tensor-quotient-augmentation). -/
def derivedGamma (tc : OpenSemilinearTensor.TotalComparison l E j o)
    (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (F : CochainComplex (scalarReductionSource l E X) ℤ) :=
  DerivedCategory.Q.mapIso (tc.chain Q F)

/-- The finite cohomology, interval and stratification clauses, using exactly the
published finite extension and locally constant/stalk conventions. The instance lambda
supplies the existing finiteness and sheafification witnesses without assumptions.
Source: Bhatt--Scholze 6.5.8; Stacks 09AH
(blueprint: lem-sf-open-tensor-quotient-augmentation). -/
def FiniteGeometry (n : ℕ) (hn : 1 ≤ n) (a b : ℤ)
    (C : proEtaleDerivedCategory U (Padic.coefficientExtensionRing l E n)) : Prop :=
    (fun [_hfin : Finite (Padic.coefficientExtensionRing l E n)]
      [_hU : (ProEt.topology U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
      [_hV : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] ↦
      intrinsicFiniteTorsionConstructible l E n hn X
        ((sfIntrinsicExtensionByZero j
          (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
        C) ∧
        proEtaleCohomologicalSupport
          ((sfIntrinsicExtensionByZero j
            (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
          C) ⊆ Set.Icc a b ∧
        (∀ r : ℤ, Nonempty
          (((DerivedCategory.homologyFunctor
            (proEtaleRingModules X
              (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))) r).obj
                ((sfIntrinsicExtensionByZero j
                  (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
                C)) ≅
            (sfIntrinsicExtensionByZero j
              (Padic.coefficientExtensionRing l E n)).obj
                ((DerivedCategory.homologyFunctor
                  (proEtaleRingModules U
                    (proEtaleConstantRing U (Padic.coefficientExtensionRing l E n))) r).obj C))) ∧
        (∀ (r : ℤ) (S : FiniteLocallyClosedStratification U),
          (∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) →
          (∀ k : Fin S.n, IsLocallyConstantProEtaleModuleSheafOfUniverses
            (S.domain k) (Padic.coefficientExtensionRing l E n)
              (proEtaleConstantModulePullback (S.immersion k)
                (Padic.coefficientExtensionRing l E n)
                ((DerivedCategory.homologyFunctor
                  (proEtaleRingModules U
                    (proEtaleConstantRing U (Padic.coefficientExtensionRing l E n))) r).obj C))) →
          (∀ (k : Fin S.n) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (x : Spec (.of Ω) ⟶ S.domain k),
            Finite (proEtaleGeometricModuleStalk x
              (proEtaleConstantRing (S.domain k) (Padic.coefficientExtensionRing l E n))
              (proEtaleConstantModulePullback (S.immersion k)
                (Padic.coefficientExtensionRing l E n)
                ((DerivedCategory.homologyFunctor
                  (proEtaleRingModules U
                    (proEtaleConstantRing U (Padic.coefficientExtensionRing l E n))) r).obj C)))) →
          ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsReduced Z],
            Set.range i = (Set.range j)ᶜ →
            (∀ omitted : Set (Option (Fin S.n)),
              (∀ q ∈ omitted, match q with
                | none => IsEmpty Z
                | some h => IsEmpty (S.domain h)) →
              ∃ (T : FiniteLocallyClosedStratification X)
                  (e : Fin T.n ≃ {q : Option (Fin S.n) // q ∉ omitted}),
                (∀ k : Fin T.n, Topology.IsConstructible (T.stratum k)) ∧
                (∀ k : Fin T.n, match (e k).val with
                  | none => Nonempty (Over.mk (T.immersion k) ≅ Over.mk i)
                  | some h => Nonempty (Over.mk (T.immersion k) ≅
                      Over.mk (S.immersion h ≫ j))) ∧
                (∀ k : Fin T.n, IsLocallyConstantProEtaleModuleSheafOfUniverses
                  (T.domain k) (Padic.coefficientExtensionRing l E n)
                    (proEtaleConstantModulePullback (T.immersion k)
                      (Padic.coefficientExtensionRing l E n)
                      ((DerivedCategory.homologyFunctor
                        (proEtaleRingModules X
                          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))) r).obj
                            ((sfIntrinsicExtensionByZero j
                              (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
                            C)))) ∧
                (∀ (k : Fin T.n) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
                  (x : Spec (.of Ω) ⟶ T.domain k),
                  Finite (proEtaleGeometricModuleStalk x
                    (proEtaleConstantRing (T.domain k) (Padic.coefficientExtensionRing l E n))
                    (proEtaleConstantModulePullback (T.immersion k)
                      (Padic.coefficientExtensionRing l E n)
                      ((DerivedCategory.homologyFunctor
                        (proEtaleRingModules X
                          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))) r).obj
                            ((sfIntrinsicExtensionByZero j
                              (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
                            C)))))) ∧
            IsZero (proEtaleConstantModulePullback i (Padic.coefficientExtensionRing l E n)
              ((DerivedCategory.homologyFunctor
                (proEtaleRingModules X
                  (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))) r).obj
                    ((sfIntrinsicExtensionByZero j
                      (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
                    C)))))
      (_hfin := Padic.finite_coefficientExtensionRing l E n hn)
      (_hU := WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} U)
      (_hV := WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X)


/-- Compatibility of the fixed finite open extension with the intrinsic finite
constructibility interface. This is a comparison of the same normalized extension,
not an assumed replacement functor. Source: Stacks 03DI, 09AH
(blueprint: lem-sf-open-tensor-quotient-augmentation). -/
def FiniteExtensionModel : Prop :=
  ∀ n : ℕ,
    (fun [_hf : Finite (Padic.coefficientExtensionRing l E (n + 1))] ↦
      Nonempty (IntegralOpenReduction.finiteExtension l E j o n ≅
        sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1))))
      (_hf := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ n.zero_le))

/-- Restricting any finite constructible partition means taking its scheme-theoretic
intersection with U. The cartesian witnesses retain the actual immersed strata,
including empty intersections. Source: Stacks 09AH; Bhatt--Scholze 6.5.8
(blueprint: lem-sf-open-tensor-quotient-augmentation). -/
def RestrictionPartitions : Prop :=
  ∀ S : FiniteLocallyClosedStratification X,
    (∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) →
    ∃ (T : FiniteLocallyClosedStratification U) (e : Fin T.n ≃ Fin S.n),
      (∀ k : Fin T.n, T.stratum k = j ⁻¹' S.stratum (e k)) ∧
      (∀ k : Fin T.n, Topology.IsConstructible (T.stratum k)) ∧
      ∀ k : Fin T.n, ∃ p : T.domain k ⟶ S.domain (e k),
        IsPullback p (T.immersion k) (S.immersion (e k)) j

/-- Integral constructibility and the identical uniform quotient intervals are
preserved by both exact open operations. Source: Bhatt--Scholze 6.5.8(2),(3)
(blueprint: lem-sf-open-tensor-quotient-augmentation). -/
def IntegralGeometry : Prop :=
  (∀ K : DerivedCategory (scalarReductionSource l E U), sfIntegralConstructible l E U K →
    sfIntegralConstructible l E X ((IntegralOpenReduction.shriek l E j o).obj K)) ∧
  (∀ P : DerivedCategory (scalarReductionSource l E X), sfIntegralConstructible l E X P →
    sfIntegralConstructible l E U ((IntegralOpenReduction.star l E j o).obj P)) ∧
  (∀ (K : DerivedCategory (scalarReductionSource l E U)) (a b : ℤ),
    sfIntegralConstructible l E U K → a ≤ b →
    (∀ n : ℕ, proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension l E U n).obj K) ⊆ Set.Icc a b) →
    ∀ n : ℕ, proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension l E X n).obj
        ((IntegralOpenReduction.shriek l E j o).obj K)) ⊆ Set.Icc a b) ∧
  (∀ (P : DerivedCategory (scalarReductionSource l E X)) (a b : ℤ),
    sfIntegralConstructible l E X P → a ≤ b →
    (∀ n : ℕ, proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension l E X n).obj P) ⊆ Set.Icc a b) →
    ∀ n : ℕ, proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension l E U n).obj
        ((IntegralOpenReduction.star l E j o).obj P)) ⊆ Set.Icc a b)

/-- The simultaneous open scalar comparison is exactly the previously specified
r_j on complete inputs; the tensor square holds on every pair of flat-term K-flat
representatives and therefore on every pair of represented constructible objects.
Source: Stacks 0E8I, 0GL1; Bhatt--Scholze 6.5.8
(blueprint: lem-sf-open-tensor-quotient-augmentation). -/
structure Comparison
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SU : CoefficientDerivedSystemCalculus l E U)
    (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
    (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
    (st : IntegralOpenReduction.TensorComparison l E j o)
    (m : OpenSemilinearTensor.Comparison l E j o SX SU AX AU st)
    (c : IntegralOpenReduction.Comparison l E j o SX SU st) where
  tensorX : OpenFactorCoherence.Tensor l E X
  tensorU : OpenFactorCoherence.Tensor l E U
  scalar : ScalarCompatibility l E j o
  strictScalar : ScalarComparison l E j o scalar st
  completeAgreement : ∀ K : (IntegralOpenReduction.complete l E U).FullSubcategory,
    c.r.hom.app K = m.r.hom.app K.obj
  finiteModel : FiniteExtensionModel l E j o
  integralGeometry : IntegralGeometry l E j o
  finiteGeometry : ∀ K : DerivedCategory (scalarReductionSource l E U),
    sfIntegralConstructible l E U K → ∀ (n : ℕ) (a b : ℤ), a ≤ b →
    proEtaleCohomologicalSupport ((scalarReductionDerivedExtension l E U n).obj K) ⊆
      Set.Icc a b →
    FiniteGeometry l E j (n + 1) (Nat.succ_le_succ n.zero_le) a b
      ((scalarReductionDerivedExtension l E U n).obj K)
  restrictionPartitions : RestrictionPartitions j
  squares : ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (F : CochainComplex (scalarReductionSource l E X) ℤ),
    integralOperationsGoodComplex l E U Q → integralOperationsGoodComplex l E X F →
    sfIntegralConstructible l E U (DerivedCategory.Q.obj Q) →
    sfIntegralConstructible l E X (DerivedCategory.Q.obj F) →
    ∃ z : StrictSquare l E j o m.totalComparison scalar st strictScalar Q F,
      RoosNormalization l E X tensorX
        ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F z.upper ∧
      RoosNormalization l E U tensorU Q
        ((OpenSemilinearTensor.restrictionComplex l E j o).obj F) z.lower

```

## New

The block above, with ScalarComparison.components replaced by its definitionally identical
ScalarComponents predicate, is in Sheaf.SixFunctors.OpenTensorQuotientData, with the
same namespace and context; the original module publicly imports that module.
Its existing public prerequisites are still publicly reexported. The original plain
(proof-only) imports were not used by the declarations and are dropped (reviewer, 2026-10-25). The new local elaboration command, which is not exported, is:

```lean
attribute [local irreducible] SheafOfModules.monoidalCategory
  Padic Padic.normedField
```

The theorem openTensorQuotientAugmentation retains its exact signature and now
assembles the existing compatible context, two strictly smaller named lemmas,
finite-stage geometry from the published theorem, and actual pullback partitions.
Its original docstring is unchanged. The original local irreducibility attributes stay
at their original position. Both backward definitional equality transparency options
are true in the data module, respecting the local bounds, with no change to the mathematical normalization.
These are local elaboration settings. ScalarComponents is a public proposition definition
whose body is exactly the old components field type. No proof obligation is added by it.

## Users

Every user keeps all the same declarations through the original public import
(OpenTensorQuotientAugmentation publicly imports OpenTensorQuotientData), with identical
elaborated types and data. The only changed type is ScalarComparison.components, now the
definitionally equal ScalarComponents; no module outside this delivery uses
ScalarComparison or Comparison.strictScalar. No target statement changes, nor does any
definition used by a target change meaning.

Direct importers of the original module (each compiled against the delivered modules by the
reviewer, 2026-10-25):

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.OpenFactorOpenRealization | unclaimed | Public interfaces retained through reexport; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletionData | unclaimed | Public interfaces retained through reexport; no adaptation. |
| Sheaf.SixFunctors.OpenTensorAugmentationLimitSquare | unclaimed | Public interfaces retained through reexport; no adaptation. |

Modules of this delivery:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | E4 | Original theorem proof completed from two new independent remaining obligations. |
| Sheaf.SixFunctors.OpenTensorQuotientData | new E4 | Owns the unchanged interfaces. |
| Sheaf.SixFunctors.OpenTensorQuotientGeometry | new E4 | Geometric preservation obligation. |
| Sheaf.SixFunctors.OpenTensorQuotientCochains | new E4 | Strict normalized cochain comparison obligation. |

Transitive users (they reach the names through the importers above, unchanged):
CoefficientGammaRepresentatives, ExceptionalIntegralScalarMates, ExceptionalRefinementMates,
FieldWeilShriekShiftData, FiniteCompactSupportCoefficientSquare,
FiniteExceptionalCompositorCoefficients, FixedPairTruncationCohomology,
TensorHomCoefficientTransposes, VerdierHomChainComposition (Sheaf.Paper);
BasicRealizationShiftSquare, ExceptionalIntegralReconstruction, OpenClosedWeilMateStructures
(A5), OpenFactorProjectionRealization, OpenProjectionCompletedSquare,
OpenProjectionOrdinaryRoos, OpenProjectionRestrictionNormalization, OpenProjectionRoosCompletion
(Sheaf.SixFunctors).

## Status

landed 20261025T122806-L-1807639 2026-10-25 (merge of deliver/E4/Sheaf.SixFunctors.OpenTensorQuotientAugmentation)
