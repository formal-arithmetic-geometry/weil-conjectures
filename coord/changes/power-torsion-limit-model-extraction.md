# WeilConjectures.PowerTorsionLimit strict model declarations

## Reason

The assigned theorem must import three independent, model-specific proper steps.
Those new modules must refer to its existing strict functors, unit and coordinates,
without creating an import cycle. Move these constructions to the publicly re-exported
Sheaf.Paper.PowerTorsionSheafLimitModels. The old public imports and every declaration
name and signature remain available through the original module. This is an API
extraction for the decomposition, not a change to the mathematical objects.

The only construction-body edit replaces the tensorTower functor identity and
composition proofs by functor laws. Its object and map expressions are unchanged.
The original double extensionality descended into sheaf-module maps and spent much
of the per-file compile budget. No slow definition is being bypassed by the extraction;
this proof optimization addresses the identified cost directly. The local
implicit_reducible attribute only aligns the completed commutative ring sheaf during
elaboration. It changes no definition or exported attribute.

## Old

The following declarations occur in Sheaf.Paper.PowerTorsionSheafLimitComplete:

```lean
/-- The existing strict Roos functor in the tower-of-complexes presentation.
Source: Stacks 0941 (blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
abbrev roos : (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) ⥤
    CochainComplex (integralTowerModules l E T) ℤ :=
  letI := integralCoefficientAbSheafify.{t, u} T
  letI := integralCoefficientAbLocallyBijective.{t, u} T
  letI := integralOperationsCountableProducts.{t, u} l E T
  integralOperationsRoosFunctor

/-- The actual Koszul tensor tower, functorial in the input complex.
Source: the principal Koszul calculation in sk-lem-sp-tower
(blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
abbrev tensorTower : CochainComplex (integralTowerModules l E T) ℤ ⥤
    (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  letI := SheafOfModules.monoidalCategory
    (completedIntegralCommRingSheafUnrestricted l E T)
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  { obj := fun P ↦ koszulTensorTower
      (completedIntegralCommRingSheafUnrestricted l E T) P (uniformizer l E T)
    map := fun f ↦ Functor.whiskerLeft
      (principalKoszulTower (completedIntegralCommRingSheafUnrestricted l E T)
        (uniformizer l E T))
      ((MonoidalCategory.curriedTensor (integralTowerModules l E T)).map₂CochainComplex.flip.map f)
    map_id := fun P ↦ by ext n k; simp; rfl
    map_comp := fun f g ↦ by ext n k; simp; rfl }

/-- Koszul completion on strict complex representatives, with the existing Roos model.
Source: sk-lem-sp-tower (blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
abbrev completion : CochainComplex (integralTowerModules l E T) ℤ ⥤
    CochainComplex (integralTowerModules l E T) ℤ :=
  tensorTower l E T ⋙ roos l E T

/-- The strict Koszul augmentations give a zero-homotopy Roos cocycle.
Source: sk-lem-sp-tower, canonical degree-zero inclusions
(blueprint: lem-sp-power-torsion-sheaf-limit-complete).
Proof: the differential of the zero cochain is zero. Postcompose the product map
with every projection. The remaining equality says that the degree-zero Koszul
inclusion at j+1 followed by (pi,1) equals the inclusion at j; this is
koszulRepresentativeAugmentation_naturality. Thus the composite with one minus
shift is zero. This is precisely the condition defining the node's canonical unit. -/
theorem unit_condition (P : CochainComplex (integralTowerModules l E T) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P
          (∏ᶜ fun n : ℕ ↦ ((tensorTower l E T).obj P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (Pi.lift (koszulRepresentativeAugmentation
          (completedIntegralCommRingSheafUnrestricted l E T) P (uniformizer l E T)) ≫
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦ ((tensorTower l E T).obj P).obj (op n))
            (fun n ↦ ((tensorTower l E T).obj P).map (homOfLE n.le_succ).op)) = 0 := by
  let : EssentiallySmall.{max u (t + 1)} T.ProEt :=
    essentiallySmallSelf.{u} _
  let : (AlgebraicGeometry.Scheme.ProEt.topology T).HasSheafCompose
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}) :=
    hasSheafComposeEssentiallySmallSite _ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)} (forget₂ _ _)
  let := integralCoefficientAbSheafify.{t, u} T
  let := integralCoefficientAbLocallyBijective.{t, u} T
  let := integralOperationsCountableProducts.{t, u} l E T
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  let := SheafOfModules.monoidalCategory
    (completedIntegralCommRingSheafUnrestricted l E T)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  have h : (Pi.lift (koszulRepresentativeAugmentation
      (completedIntegralCommRingSheafUnrestricted l E T) P (uniformizer l E T)) :
      P ⟶ ∏ᶜ fun n : ℕ ↦ ((tensorTower l E T).obj P).obj (op n)) ≫
      towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ((tensorTower l E T).obj P).obj (op n))
        (fun n ↦ ((tensorTower l E T).obj P).map (homOfLE n.le_succ).op) = 0 := by
    apply Pi.hom_ext
    intro n
    simpa [towerTransitionEndomorphism, towerProductShift, Category.assoc] using
      sub_eq_zero.mpr (koszulRepresentativeAugmentation_naturality.{t + 1, t, max u (t + 1)}
        (completedIntegralCommRingSheafUnrestricted l E T) P (uniformizer l E T) n)
  rw [h]
  simp

/-- The completion unit is the specified strict augmentation with zero Roos homotopy.
Source: sk-lem-sp-tower, power-torsion calculation
(blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
def unit (P : CochainComplex (integralTowerModules l E T) ℤ) :
    P ⟶ (completion l E T).obj P :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ ((tensorTower l E T).obj P).obj (op n))
      (fun n ↦ ((tensorTower l E T).obj P).map (homOfLE n.le_succ).op))
    (Pi.lift (koszulRepresentativeAugmentation
      (completedIntegralCommRingSheafUnrestricted l E T) P (uniformizer l E T))) 0
    (unit_condition l E T P)

/-- The unshifted (p=0) coordinate of the strict Roos complex, at a fixed tower level.
Source: Stacks 0941 (blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
def coordinateZero (X : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (k : ℤ) (n : ℕ) : ((roos l E T).obj X).X k ⟶ (X.obj (op n)).X k :=
  (CochainComplex.mappingCocone.fst
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ X.obj (op n))
      (fun n ↦ X.map (homOfLE n.le_succ).op))).f k ≫
    (Pi.π (fun n : ℕ ↦ X.obj (op n)) n).f k

/-- The shifted (p=1) coordinate. The target degree is k-1.
Source: Stacks 0941 (blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
def coordinateOne (X : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (k : ℤ) (n : ℕ) : ((roos l E T).obj X).X k ⟶ (X.obj (op n)).X (k - 1) :=
  (CochainComplex.mappingCocone.snd
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ X.obj (op n))
      (fun n ↦ X.map (homOfLE n.le_succ).op))).v k (k - 1) (by omega) ≫
    (Pi.π (fun n : ℕ ↦ X.obj (op n)) n).f (k - 1)

/-- Evaluation of the existing Roos model as a chain map.
Source: Stacks 0941 (blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
def evaluation (X : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) (n : ℕ) :
    (roos l E T).obj X ⟶ X.obj (op n) :=
  CochainComplex.mappingCocone.fst
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ X.obj (op n))
      (fun n ↦ X.map (homOfLE n.le_succ).op)) ≫ Pi.π _ n

/-- The strict j-tower obtained by applying the n-Roos functor to each tensor column.
Source: sk-lem-sp-tower, double-product calculation
(blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
abbrev columns (Q : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) :=
  (Q ⋙ tensorTower l E T).flip ⋙ roos l E T

/-- The row coordinate of the iterated Roos complex.
Source: sk-lem-sp-tower, signed interchange calculation
(blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
def rowCoordinate (Q : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (p q : Bool) (k : ℤ) (n j : ℕ) :
    ((roos l E T).obj (Q ⋙ completion l E T)).X k ⟶
      (((tensorTower l E T).obj (Q.obj (op n))).obj (op j)).X
        (match p, q with
        | false, false => k
        | false, true => k - 1
        | true, false => k - 1
        | true, true => k - 1 - 1) := by
  cases p <;> cases q
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero] using
      (coordinateZero l E T (Q ⋙ completion l E T) k n ≫
        coordinateZero l E T ((tensorTower l E T).obj (Q.obj (op n))) k j)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero] using
      (coordinateZero l E T (Q ⋙ completion l E T) k n ≫
        coordinateOne l E T ((tensorTower l E T).obj (Q.obj (op n))) k j)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero] using
      (coordinateOne l E T (Q ⋙ completion l E T) k n ≫
        coordinateZero l E T ((tensorTower l E T).obj (Q.obj (op n))) (k - 1) j)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero] using
      (coordinateOne l E T (Q ⋙ completion l E T) k n ≫
        coordinateOne l E T ((tensorTower l E T).obj (Q.obj (op n))) (k - 1) j)

/-- The column coordinate of the iterated Roos complex.
Source: sk-lem-sp-tower, signed interchange calculation
(blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
def columnCoordinate (Q : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (p q : Bool) (k : ℤ) (n j : ℕ) :
    ((roos l E T).obj (columns l E T Q)).X k ⟶
      (((tensorTower l E T).obj (Q.obj (op n))).obj (op j)).X
        (match p, q with
        | false, false => k
        | false, true => k - 1
        | true, false => k - 1
        | true, true => k - 1 - 1) := by
  cases p <;> cases q
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero,
      Functor.flip, Functor.comp_obj] using
      (coordinateZero l E T (columns l E T Q) k j ≫
        coordinateZero l E T ((Q ⋙ tensorTower l E T).flip.obj (op j)) k n)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero,
      Functor.flip, Functor.comp_obj] using
      (coordinateOne l E T (columns l E T Q) k j ≫
        coordinateZero l E T ((Q ⋙ tensorTower l E T).flip.obj (op j)) (k - 1) n)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero,
      Functor.flip, Functor.comp_obj] using
      (coordinateZero l E T (columns l E T Q) k j ≫
        coordinateOne l E T ((Q ⋙ tensorTower l E T).flip.obj (op j)) k n)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero,
      Functor.flip, Functor.comp_obj] using
      (coordinateOne l E T (columns l E T Q) k j ≫
        coordinateOne l E T ((Q ⋙ tensorTower l E T).flip.obj (op j)) (k - 1) n)
```

## New

The declarations occur in Sheaf.Paper.PowerTorsionSheafLimitModels, publicly imported
by the original module:

```lean
/-- The existing strict Roos functor in the tower-of-complexes presentation.
Source: Stacks 0941 (blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
abbrev roos : (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) ⥤
    CochainComplex (integralTowerModules l E T) ℤ :=
  letI := integralCoefficientAbSheafify.{t, u} T
  letI := integralCoefficientAbLocallyBijective.{t, u} T
  letI := integralOperationsCountableProducts.{t, u} l E T
  integralOperationsRoosFunctor

attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted

/-- The actual Koszul tensor tower, functorial in the input complex.
Source: the principal Koszul calculation in sk-lem-sp-tower
(blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
abbrev tensorTower : CochainComplex (integralTowerModules l E T) ℤ ⥤
    (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  letI := SheafOfModules.monoidalCategory
    (completedIntegralCommRingSheafUnrestricted l E T)
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  { obj := fun P ↦ koszulTensorTower
      (completedIntegralCommRingSheafUnrestricted l E T) P (uniformizer l E T)
    map := fun f ↦ Functor.whiskerLeft
      (principalKoszulTower (completedIntegralCommRingSheafUnrestricted l E T)
        (uniformizer l E T))
      ((MonoidalCategory.curriedTensor (integralTowerModules l E T)).map₂CochainComplex.flip.map f)
    map_id := fun P ↦ by
      rw [CategoryTheory.Functor.map_id]
      apply NatTrans.ext
      funext n
      rfl
    map_comp := fun f g ↦ by
      simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.whiskerLeft_comp] }

/-- Koszul completion on strict complex representatives, with the existing Roos model.
Source: sk-lem-sp-tower (blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
abbrev completion : CochainComplex (integralTowerModules l E T) ℤ ⥤
    CochainComplex (integralTowerModules l E T) ℤ :=
  tensorTower l E T ⋙ roos l E T

/-- The strict Koszul augmentations give a zero-homotopy Roos cocycle.
Source: sk-lem-sp-tower, canonical degree-zero inclusions
(blueprint: lem-sp-power-torsion-sheaf-limit-complete).
Proof: the differential of the zero cochain is zero. Postcompose the product map
with every projection. The remaining equality says that the degree-zero Koszul
inclusion at j+1 followed by (pi,1) equals the inclusion at j; this is
koszulRepresentativeAugmentation_naturality. Thus the composite with one minus
shift is zero. This is precisely the condition defining the node's canonical unit. -/
theorem unit_condition (P : CochainComplex (integralTowerModules l E T) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P
          (∏ᶜ fun n : ℕ ↦ ((tensorTower l E T).obj P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (Pi.lift (koszulRepresentativeAugmentation
          (completedIntegralCommRingSheafUnrestricted l E T) P (uniformizer l E T)) ≫
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦ ((tensorTower l E T).obj P).obj (op n))
            (fun n ↦ ((tensorTower l E T).obj P).map (homOfLE n.le_succ).op)) = 0 := by
  let : EssentiallySmall.{max u (t + 1)} T.ProEt :=
    essentiallySmallSelf.{u} _
  let : (AlgebraicGeometry.Scheme.ProEt.topology T).HasSheafCompose
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}) :=
    hasSheafComposeEssentiallySmallSite _ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)} (forget₂ _ _)
  let := integralCoefficientAbSheafify.{t, u} T
  let := integralCoefficientAbLocallyBijective.{t, u} T
  let := integralOperationsCountableProducts.{t, u} l E T
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  let := SheafOfModules.monoidalCategory
    (completedIntegralCommRingSheafUnrestricted l E T)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E T)
  have h : (Pi.lift (koszulRepresentativeAugmentation
      (completedIntegralCommRingSheafUnrestricted l E T) P (uniformizer l E T)) :
      P ⟶ ∏ᶜ fun n : ℕ ↦ ((tensorTower l E T).obj P).obj (op n)) ≫
      towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ((tensorTower l E T).obj P).obj (op n))
        (fun n ↦ ((tensorTower l E T).obj P).map (homOfLE n.le_succ).op) = 0 := by
    apply Pi.hom_ext
    intro n
    simpa [towerTransitionEndomorphism, towerProductShift, Category.assoc] using
      sub_eq_zero.mpr (koszulRepresentativeAugmentation_naturality.{t + 1, t, max u (t + 1)}
        (completedIntegralCommRingSheafUnrestricted l E T) P (uniformizer l E T) n)
  rw [h]
  simp

/-- The completion unit is the specified strict augmentation with zero Roos homotopy.
Source: sk-lem-sp-tower, power-torsion calculation
(blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
def unit (P : CochainComplex (integralTowerModules l E T) ℤ) :
    P ⟶ (completion l E T).obj P :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ ((tensorTower l E T).obj P).obj (op n))
      (fun n ↦ ((tensorTower l E T).obj P).map (homOfLE n.le_succ).op))
    (Pi.lift (koszulRepresentativeAugmentation
      (completedIntegralCommRingSheafUnrestricted l E T) P (uniformizer l E T))) 0
    (unit_condition l E T P)

/-- The unshifted (p=0) coordinate of the strict Roos complex, at a fixed tower level.
Source: Stacks 0941 (blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
def coordinateZero (X : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (k : ℤ) (n : ℕ) : ((roos l E T).obj X).X k ⟶ (X.obj (op n)).X k :=
  (CochainComplex.mappingCocone.fst
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ X.obj (op n))
      (fun n ↦ X.map (homOfLE n.le_succ).op))).f k ≫
    (Pi.π (fun n : ℕ ↦ X.obj (op n)) n).f k

/-- The shifted (p=1) coordinate. The target degree is k-1.
Source: Stacks 0941 (blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
def coordinateOne (X : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (k : ℤ) (n : ℕ) : ((roos l E T).obj X).X k ⟶ (X.obj (op n)).X (k - 1) :=
  (CochainComplex.mappingCocone.snd
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ X.obj (op n))
      (fun n ↦ X.map (homOfLE n.le_succ).op))).v k (k - 1) (by omega) ≫
    (Pi.π (fun n : ℕ ↦ X.obj (op n)) n).f (k - 1)

/-- Evaluation of the existing Roos model as a chain map.
Source: Stacks 0941 (blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
def evaluation (X : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) (n : ℕ) :
    (roos l E T).obj X ⟶ X.obj (op n) :=
  CochainComplex.mappingCocone.fst
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ X.obj (op n))
      (fun n ↦ X.map (homOfLE n.le_succ).op)) ≫ Pi.π _ n

/-- The strict j-tower obtained by applying the n-Roos functor to each tensor column.
Source: sk-lem-sp-tower, double-product calculation
(blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
abbrev columns (Q : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) :=
  (Q ⋙ tensorTower l E T).flip ⋙ roos l E T

/-- The row coordinate of the iterated Roos complex.
Source: sk-lem-sp-tower, signed interchange calculation
(blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
def rowCoordinate (Q : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (p q : Bool) (k : ℤ) (n j : ℕ) :
    ((roos l E T).obj (Q ⋙ completion l E T)).X k ⟶
      (((tensorTower l E T).obj (Q.obj (op n))).obj (op j)).X
        (match p, q with
        | false, false => k
        | false, true => k - 1
        | true, false => k - 1
        | true, true => k - 1 - 1) := by
  cases p <;> cases q
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero] using
      (coordinateZero l E T (Q ⋙ completion l E T) k n ≫
        coordinateZero l E T ((tensorTower l E T).obj (Q.obj (op n))) k j)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero] using
      (coordinateZero l E T (Q ⋙ completion l E T) k n ≫
        coordinateOne l E T ((tensorTower l E T).obj (Q.obj (op n))) k j)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero] using
      (coordinateOne l E T (Q ⋙ completion l E T) k n ≫
        coordinateZero l E T ((tensorTower l E T).obj (Q.obj (op n))) (k - 1) j)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero] using
      (coordinateOne l E T (Q ⋙ completion l E T) k n ≫
        coordinateOne l E T ((tensorTower l E T).obj (Q.obj (op n))) (k - 1) j)

/-- The column coordinate of the iterated Roos complex.
Source: sk-lem-sp-tower, signed interchange calculation
(blueprint: lem-sp-power-torsion-sheaf-limit-complete). -/
def columnCoordinate (Q : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ)
    (p q : Bool) (k : ℤ) (n j : ℕ) :
    ((roos l E T).obj (columns l E T Q)).X k ⟶
      (((tensorTower l E T).obj (Q.obj (op n))).obj (op j)).X
        (match p, q with
        | false, false => k
        | false, true => k - 1
        | true, false => k - 1
        | true, true => k - 1 - 1) := by
  cases p <;> cases q
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero,
      Functor.flip, Functor.comp_obj] using
      (coordinateZero l E T (columns l E T Q) k j ≫
        coordinateZero l E T ((Q ⋙ tensorTower l E T).flip.obj (op j)) k n)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero,
      Functor.flip, Functor.comp_obj] using
      (coordinateOne l E T (columns l E T Q) k j ≫
        coordinateZero l E T ((Q ⋙ tensorTower l E T).flip.obj (op j)) (k - 1) n)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero,
      Functor.flip, Functor.comp_obj] using
      (coordinateZero l E T (columns l E T Q) k j ≫
        coordinateOne l E T ((Q ⋙ tensorTower l E T).flip.obj (op j)) k n)
  · simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero,
      Functor.flip, Functor.comp_obj] using
      (coordinateOne l E T (columns l E T Q) k j ≫
        coordinateOne l E T ((Q ⋙ tensorTower l E T).flip.obj (op j)) (k - 1) n)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PowerTorsionSheafLimitComplete | Y6 | Publicly imports the models and proves the same theorem from three proper steps. |
| Sheaf.Paper.PowerTorsionKoszulUnit | new, Y6 | Uses the same unit and tensor tower. |
| Sheaf.Paper.PowerTorsionKoszulRoosExchange | new, Y6 | Uses the same four coordinate functions. |
| Sheaf.Paper.PowerTorsionKoszulQuotientCompleteness | new, Y6 | Uses the same unit and quotient evaluations. |

`tools/downstream.py Sheaf.Paper.PowerTorsionSheafLimitComplete` reports zero current
Lean importers. Its DAG parents and the unit realization are preserved. There are
no adaptations to modules held by another group or to the adopted source library.
The original theorem signature is byte-identical. The moved definitions have the
same data expressions and meanings, including the zero-homotopy unit, tensor order,
indexing, and signs. No target signature or target interpretation is changed.

## Status

landed 20261025T164846-L-1111894 2026-10-25 (merge of deliver/Y6/Sheaf.Paper.PowerTorsionSheafLimitComplete)
