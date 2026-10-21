# CategoryTheory.KoszulRoos comparison data

## Reason

The projection-adjoint proof and the coefficient-coherence and chain-model existence lemmas
need the same definitions. Extract them into a shared module to avoid an import cycle.
This extraction is not a subdivision to evade a compile limit. The shared definitions
compile as one file in 38.4 seconds. Select the same local monoidal instance as the existing
PrincipalKoszulQuotientTowers source to avoid unnecessary localization-instance unfolding.
Those monoidality witnesses are proofs of propositions, so this does not change the tensor.

## Old

The following declarations were in
`Sheaf.Algebra.Homology.KoszulRoosProjectionComparison`:

```lean
/-- The existing category of ringed-site modules.
Source: Stacks 03CZ (blueprint: lem-sp-koszul-roos-projection-comparison). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)

/-- A global ring section regarded as a section of its unit module.
Source: Stacks 03CZ (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def unitSection (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) :
    (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections :=
  ⟨s.val, s.property⟩

/-- The existing two-term Koszul complex, with power m+1.
Source: Stacks 06YY (blueprint: lem-sp-koszul-roos-projection-comparison). -/
abbrev K (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) (m : ℕ) :=
  principalKoszul R (unitSection R s) m

/-- The existing quotient ring sheaf, with power m+1.
Source: Stacks 06YY (blueprint: lem-sp-koszul-roos-projection-comparison). -/
abbrev B (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) [HasSheafify J CommRingCat.{r}]
    (m : ℕ) := principalPowerRingQuotient R s (m + 1)

/-- The existing quotient ring projection.
Source: Stacks 06YY (blueprint: lem-sp-koszul-roos-projection-comparison). -/
abbrev quotient (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) [HasSheafify J CommRingCat.{r}]
    (m : ℕ) := principalPowerRingProjection R s (m + 1)

/-- Total tensor with the actual two-term Koszul complex, in scalar-first order.
Source: Stacks 012Z (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def tensor (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) (m : ℕ) :
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ :=
  (curriedTensor (Modules R)).map₂CochainComplex.obj (K R s m)

/-- Reassemble a strict tower of complexes using the existing tower construction.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def assemble (R : Sheaf J CommRingCat.{r}) :
    (ℕᵒᵖ ⥤ CochainComplex (Modules R) ℤ) ⥤ CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ where
  obj := koszulTowerComplex R
  map := koszulTowerComplexMap R
  map_id X := by ext i n; rfl
  map_comp f g := by ext i n; rfl

/-- A total-tensor summand, with its target explicitly given by the tensor functor.
Source: Stacks 012Z (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def summand (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) (m : ℕ)
    (P : CochainComplex (Modules R) ℤ) (a b q : ℤ) (hab : a + b = q) :
    (K R s m).X a ⊗ P.X b ⟶ ((tensor R s m).obj P).X q :=
  CochainComplex.ιMapBifunctor (K R s m) P (curriedTensor (Modules R)) a b q hab

/-- Apply a complex functor to each level of a strict tower.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def onTowers (R : Sheaf J CommRingCat.{r})
    (F : CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight _ _ _).obj F ⋙ assemble R

/-- Shift the nonnegative index by h; positive indices start at h+1.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def tailIndex (h : ℕ) : ℕ ⥤ ℕ :=
  (⟨fun n ↦ h + n, fun _ _ hnm ↦ Nat.add_le_add_left hnm h⟩ : ℕ →o ℕ).monotone.functor

/-- Delete a finite prefix of a strict tower complex.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def tail (R : Sheaf J CommRingCat.{r}) (h : ℕ) :=
  ((Functor.whiskeringLeft _ _ (Modules R)).obj (tailIndex h).op).mapHomologicalComplex
    (.up ℤ)

/-- Product coordinate deletion, applied in both copies of the Roos product.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def deletionProduct (R : Sheaf J CommRingCat.{r})
    (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (h : ℕ) :
    roosP X ⟶ roosP ((tail R h).obj X) :=
  Pi.lift (fun n : ℕ ↦ Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) (h + n))

/-- The canonical tensor/product comparison, specified by every coordinate.
Source: Stacks 0941, 012Z (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def tensorProduct (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) (m : ℕ)
    (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) :
    (tensor R s m).obj (roosP X) ⟶ roosP ((onTowers R (tensor R s m)).obj X) :=
  Pi.lift (fun n : ℕ ↦ (tensor R s m).map
    (Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) n))

/-- Koszul coefficient transition, using the already defined strict power tower.
Source: Stacks 06YY (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def koszulStep (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) {k m : ℕ} (hkm : k ≤ m) :
    K R s m ⟶ K R s k :=
  (principalKoszulTower R (unitSection R s)).map (homOfLE hkm).op

/-- The induced natural transition of total tensor functors.
Source: Stacks 06YY (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def tensorStep (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) {k m : ℕ} (hkm : k ≤ m) :
    tensor R s m ⟶ tensor R s k :=
  (curriedTensor (Modules R)).map₂CochainComplex.map (koszulStep R s hkm)

/-- The actual constant tower complex.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def constant (R : Sheaf J CommRingCat.{r}) (N : CochainComplex (Modules R) ℤ) :=
  (assemble R).obj ((Functor.const ℕᵒᵖ).obj N)

variable (R : Sheaf J CommRingCat.{r})
  (s : (R.obj ⋙ forget CommRingCat.{r}).sections) [HasSheafify J CommRingCat.{r}]
  [∀ S : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules S)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules R)]

/-- The recorded scalar extension model, with the actual principal quotient map.
Source: Stacks 06YY (blueprint: lem-sp-koszul-roos-projection-comparison). -/
abbrev ScalarModel (m : ℕ) :=
  SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w} (quotient R s m)

/-- The recorded exact restriction functor for the principal quotient.
Source: Stacks 03CZ (blueprint: lem-sp-koszul-roos-projection-comparison). -/
abbrev restriction (m : ℕ) := SheafOfModules.restrictedTensorScalars (quotient R s m)

/-- Its termwise action on complexes.
Source: Stacks 03CZ (blueprint: lem-sp-koszul-roos-projection-comparison). -/
abbrev restrictComplex (m : ℕ) := (restriction R s m).mapHomologicalComplex (.up ℤ)

/-- The canonical pure section of a presented scalar extension.
Source: Stacks 03CZ (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def pure (m : ℕ) (D : ScalarModel R s m) (M : Modules R) (U : Cᵒᵖ)
    (b : (B R s m).obj.obj U) (x : M.val.obj U) : (D.E.obj M).val.obj U :=
  (eqToHom (D.obj_eq M).symm).val.app U
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf (quotient R s m) M).presheaf).app U
      (b ⊗ₜ[R.obj.obj U, ((quotient R s m).hom.app U).hom] x))

/-- Roos coordinates with an arbitrary degree, using explicit equality transports.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def coordinates (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (q : ℤ) :
    (roosF.obj X).X q ≅ (roosP X).X (q - 1) ⊞ (roosP X).X q :=
  (roosF.obj X).XIsoOfEq (by omega) ≪≫ roosχ X (q - 1) ≪≫
    biprod.mapIso (Iso.refl _) ((roosP X).XIsoOfEq (by omega))

/-- Act on towers by a natural transformation between complex functors.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def onTowersMap {F G : CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ}
    (tau : F ⟶ G) : onTowers R F ⟶ onTowers R G :=
  Functor.whiskerRight
    (Functor.whiskerLeft HomologicalComplex.complexOfFunctorsToFunctorToComplex
      ((Functor.whiskeringRight _ _ _).map tau)) (assemble R)


/-- Termwise action of a normalized ordinary coefficient transition.
Source: Stacks 06YY (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def ordinaryTransition {k m : ℕ} (Dm : ScalarModel R s m) (Dk : ScalarModel R s k)
    (e : Dm.E ⋙ restriction R s m ⟶ Dk.E ⋙ restriction R s k) :
    Dm.E.mapHomologicalComplex (.up ℤ) ⋙ restrictComplex R s m ⟶
      Dk.E.mapHomologicalComplex (.up ℤ) ⋙ restrictComplex R s k :=
  e.mapHomologicalComplex (.up ℤ)

/-- Normalized comparison data. Every functor in this structure has its existing
universal property, and every chain comparison is pinned on total-tensor summands
and both Roos coordinates. No arbitrary cone completion is allowed.
Source: Stacks 0941, 06YY and 09T5; blueprint tower proof paragraph 1
(blueprint: lem-sp-koszul-roos-projection-comparison). -/
structure Models where
  /-- The total derived inverse-limit functor. -/
  RF : DerivedCategory (ℕᵒᵖ ⥤ Modules R) ⥤ DerivedCategory (Modules R)
  /-- Its ordinary-limit unit. -/
  eta : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF
  /-- Normalized strict Roos comparison to that functor. -/
  norm : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF
  /-- Existing K-flat extension models, separately at every coefficient power. -/
  scalar : ∀ m : ℕ, ScalarModel R s m
  /-- The normalized ordinary scalar adjunction. -/
  ordinaryAdj : ∀ m : ℕ, (scalar m).E ⊣ restriction R s m
  /-- Derived scalar extension and exact scalar restriction are adjoint. -/
  derivedAdj : ∀ m : ℕ, (scalar m).T ⊣ (restriction R s m).mapDerivedCategory
  /-- The canonical chain augmentation to ordinary scalar extension, then restriction. -/
  aug : ∀ m : ℕ, tensor R s m ⟶
    (scalar m).E.mapHomologicalComplex (.up ℤ) ⋙ restrictComplex R s m
  /-- Natural two-term computation of restricted derived extension. -/
  A : ∀ m : ℕ, tensor R s m ⋙ DerivedCategory.Q ≅
    DerivedCategory.Q ⋙ (scalar m).T ⋙ (restriction R s m).mapDerivedCategory
  /-- The natural chain isomorphism interchanging Koszul tensor and the Roos cone. -/
  chi : ∀ m : ℕ, roosF ⋙ tensor R s m ≅ onTowers R (tensor R s m) ⋙ roosF
  /-- Finite-prefix deletion as a strict chain map. -/
  delete : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (h : ℕ),
    roosF.obj X ⟶ roosF.obj ((tail R h).obj X)

/-- Normalization and computation properties of the displayed comparison data.
Source: blueprint tower proof paragraph 1, Stacks 0941, 06YY and 09T5
(blueprint: lem-sp-koszul-roos-projection-comparison). -/
structure Normalization (M : Models R s) : Prop where
  /-- Exactness of countable products on the pro-etale site. -/
  exactProducts : HasExactLimitsOfShape (Discrete ℕ) (Modules R)
  /-- Localized termwise products are the actual derived products. -/
  products : ∀ X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ,
    Nonempty (IsLimit (DerivedCategory.Q.mapCone
      (limit.cone (Discrete.functor (fun n : ℕ ↦ X.asFunctor.obj (op n))))))
  /-- It is the right derived functor of the actual inverse limit. -/
  universal : M.RF.IsRightDerivedFunctor M.eta (HomologicalComplex.quasiIso _ (.up ℤ))
  /-- Normalization on ordinary inverse limits. -/
  norm_unit : ∀ X, DerivedCategory.Q.map (roosι X) ≫ M.norm.hom.app X = M.eta.app X
  /-- The ordinary unit is x mapping to 1 tensor x. -/
  ordinary_unit : ∀ (m : ℕ) (P : Modules R) (U : Cᵒᵖ) (x : P.val.obj U),
    ((M.ordinaryAdj m).unit.app P).val.app U x = pure R s m (M.scalar m) P U 1 x
  /-- Normalization of the derived adjoint on K-flat representatives. -/
  derived_adjunction : ∀ (m : ℕ) (P : CochainComplex (Modules R) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (N : CochainComplex (Modules (B R s m)) ℤ)
    (f : ((M.scalar m).E.mapHomologicalComplex (.up ℤ)).obj P ⟶ N),
    ((M.derivedAdj m).homEquiv _ _).symm
      (DerivedCategory.Q.map
          (((M.ordinaryAdj m).mapHomologicalComplex (.up ℤ)).homEquiv P N f) ≫
        (restriction R s m).mapDerivedCategoryFactors.inv.app N) =
      (M.scalar m).ε.app P ≫ DerivedCategory.Q.map f
  /-- Its degree-zero inclusion is exactly the ordinary tensor unit. -/
  aug_unit : ∀ (m : ℕ) (P : CochainComplex (Modules R) ℤ),
    koszulRepresentativeAugmentation R P (unitSection R s) m ≫ (M.aug m).app P =
      ((M.ordinaryAdj m).mapHomologicalComplex (.up ℤ)).unit.app P
  /-- Augmentation vanishes on all other Koszul-degree summands. -/
  aug_zero : ∀ (m : ℕ) (P : CochainComplex (Modules R) ℤ) (a b : ℤ), a ≠ 0 →
    summand R s m P a b (a + b) rfl ≫
      ((M.aug m).app P).f (a + b) = 0
  /-- Its normalization is the actual augmentation on every K-flat complex. -/
  A_kflat : ∀ (m : ℕ) (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    (M.A m).hom.app P ≫
        (restriction R s m).mapDerivedCategory.map ((M.scalar m).ε.app P) ≫
        (restriction R s m).mapDerivedCategoryFactors.hom.app
          (((M.scalar m).E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((M.aug m).app P)
  /-- Finite total tensor commutes with the countable product. -/
  tensor_product : ∀ (m : ℕ) (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ),
    IsIso (tensorProduct R s m X)
  /-- Its previous-degree Roos coordinate, including the Koszul interchange sign. -/
  chi_first : ∀ (m : ℕ) (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (a b : ℤ),
    summand R s m (roosF.obj X) a b (a + b) rfl ≫ ((M.chi m).hom.app X).f (a + b) ≫
        (coordinates R ((onTowers R (tensor R s m)).obj X) (a + b)).hom ≫ biprod.fst =
      ((-1 : ℤˣ) ^ a) •
        ((K R s m).X a ◁ ((coordinates R X b).hom ≫ biprod.fst) ≫
          summand R s m (roosP X) a (b - 1) (a + b - 1) (by omega) ≫
          (tensorProduct R s m X).f (a + b - 1))
  /-- Its current-degree Roos coordinate is the literal tensor of product projections. -/
  chi_second : ∀ (m : ℕ) (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (a b : ℤ),
    summand R s m (roosF.obj X) a b (a + b) rfl ≫ ((M.chi m).hom.app X).f (a + b) ≫
        (coordinates R ((onTowers R (tensor R s m)).obj X) (a + b)).hom ≫ biprod.snd =
      (K R s m).X a ◁ ((coordinates R X b).hom ≫ biprod.snd) ≫
        summand R s m (roosP X) a b (a + b) rfl ≫ (tensorProduct R s m X).f (a + b)
  /-- Both cone coordinates are coordinate deletion. -/
  delete_coordinates : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (h : ℕ) (q : ℤ),
    (M.delete X h).f (q + 1) ≫ (roosχ ((tail R h).obj X) q).hom =
      (roosχ X q).hom ≫
        biprod.map ((deletionProduct R X h).f q) ((deletionProduct R X h).f (q + 1))
  /-- Prefix deletion is a quasi-isomorphism, including the empty prefix. -/
  delete_quasiIso : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (h : ℕ),
    QuasiIso (M.delete X h)
  /-- It retains each remaining projection. -/
  delete_projection : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (h n : ℕ),
    M.delete X h ≫ roosEval ((tail R h).obj X) n = roosEval X (h + n)
  /-- It is natural for strict maps of towers. -/
  delete_natural : ∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ} (f : X ⟶ Y) (h : ℕ),
    roosF.map f ≫ M.delete Y h = M.delete X h ≫ roosF.map ((tail R h).map f)
  /-- Scalar restriction detects derived isomorphisms. -/
  reflects : ∀ m : ℕ, (restriction R s m).mapDerivedCategory.ReflectsIsomorphisms

namespace Models

/-- The actual derived-limit projection, fixed by the normalized Roos comparison.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def projection (M : Models R s) (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (n : ℕ) :
    M.RF.obj (DerivedCategory.Q.obj X) ⟶ DerivedCategory.Q.obj (X.asFunctor.obj (op n)) :=
  M.norm.inv.app X ≫ DerivedCategory.Q.map (roosEval X n)


/-- The prescribed composite: inverse two-term comparison, tensor/cone interchange,
tail deletion, then normalized Roos realization. This is a real composite of the
specified maps, never a choice of a cone filler.
Source: blueprint tower proof paragraph 1, Stacks 0941 and 06YY
(blueprint: lem-sp-koszul-roos-projection-comparison). -/
def comparison (M : Models R s) (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (m h : ℕ) :
    ((M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory).obj
        (M.RF.obj (DerivedCategory.Q.obj X)) ⟶
      M.RF.obj (DerivedCategory.Q.obj ((tail R h).obj
        ((onTowers R (tensor R s m)).obj X))) :=
  ((M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory).map (M.norm.inv.app X) ≫
    (M.A m).inv.app (roosF.obj X) ≫ DerivedCategory.Q.map ((M.chi m).hom.app X) ≫
    DerivedCategory.Q.map (M.delete ((onTowers R (tensor R s m)).obj X) h) ≫
    M.norm.hom.app ((tail R h).obj ((onTowers R (tensor R s m)).obj X))


/-- The strict map to the constant restricted target, obtained from the actual
Koszul augmentations and the supplied compatible B_m-linear chain maps.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def familyMap (M : Models R s) (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (m : ℕ)
    (N : CochainComplex (Modules (B R s m)) ℤ)
    (f : ((tail R m).obj X).asFunctor ⋙
      (M.scalar m).E.mapHomologicalComplex (.up ℤ) ⟶ (Functor.const ℕᵒᵖ).obj N) :
    (tail R m).obj ((onTowers R (tensor R s m)).obj X) ⟶
      constant R ((restrictComplex R s m).obj N) :=
  (assemble R).map
    (Functor.whiskerLeft ((tail R m).obj X).asFunctor (M.aug m) ≫
      Functor.whiskerRight f (restrictComplex R s m))


end Models

/-- All compatibility clauses for the normalized data. The adjoint equation refers
to the actual composite of the definition `Models.comparison` and a strict map of
Roos complexes, so equality is not inferred from projections into a homotopy limit.
Source: blueprint tower proof paragraph 1; Stacks 0941, 06YY and 09T5
(blueprint: lem-sp-koszul-roos-projection-comparison). -/
structure Compatibility (M : Models R s) : Prop extends Normalization R s M where
  /-- The prescribed comparison is an isomorphism. -/
  isIso : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (m h : ℕ),
    IsIso (M.comparison R s X m h)
  /-- Every remaining projection is the derived tensor of the original projection. -/
  projection : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (m h n : ℕ),
    M.comparison R s X m h ≫
        M.projection R s ((tail R h).obj ((onTowers R (tensor R s m)).obj X)) n =
      ((M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory).map
          (M.projection R s X (h + n)) ≫
        (M.A m).inv.app (X.asFunctor.obj (op (h + n)))
  /-- Constant tower evaluation is inverse to the diagonal after localization. -/
  constant_identification : ∀ N : CochainComplex (Modules R) ℤ,
    IsIso (DerivedCategory.Q.map (roosEval (constant R N) 0)) ∧
    ∃ diagonal : N ⟶ roosF.obj (constant R N),
      (∀ q : ℤ, diagonal.f (q + 1) ≫ (roosχ (constant R N) q).hom =
        biprod.lift 0 ((Pi.lift (fun _ : ℕ ↦ 𝟙 N)).f (q + 1))) ∧
      DerivedCategory.Q.map diagonal ≫
          DerivedCategory.Q.map (roosEval (constant R N) 0) = 𝟙 _ ∧
      DerivedCategory.Q.map (roosEval (constant R N) 0) ≫
          DerivedCategory.Q.map diagonal = 𝟙 _
  /-- The full augmentation/limit/constant-evaluation composite is the restriction
  of the normalized derived adjoint at the first retained level. -/
  adjoint : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (m : ℕ)
    (N : CochainComplex (Modules (B R s m)) ℤ)
    (f : ((tail R m).obj X).asFunctor ⋙
      (M.scalar m).E.mapHomologicalComplex (.up ℤ) ⟶ (Functor.const ℕᵒᵖ).obj N),
    M.comparison R s X m m ≫
        M.RF.map (DerivedCategory.Q.map (M.familyMap R s X m N f)) ≫
        M.norm.inv.app (constant R ((restrictComplex R s m).obj N)) ≫
        DerivedCategory.Q.map (roosEval (constant R ((restrictComplex R s m).obj N)) 0) =
      (restriction R s m).mapDerivedCategory.map
        (((M.derivedAdj m).homEquiv _ _).symm
          (M.projection R s X m ≫
            DerivedCategory.Q.map
              (((M.ordinaryAdj m).mapHomologicalComplex (.up ℤ)).homEquiv
                (X.asFunctor.obj (op m)) N (f.app (op 0))) ≫
            (restriction R s m).mapDerivedCategoryFactors.inv.app N)) ≫
        (restriction R s m).mapDerivedCategoryFactors.hom.app N
  /-- The specified Koszul transitions have components (t^(m-k),1).
  The equation uses the actual cone map, so it specifies both degrees. -/
  koszul_transition : ∀ (k m : ℕ) (hkm : k ≤ m),
    ∃ square :
      (CochainComplex.singleFunctor (Modules R) 0).map
          (endoPow (globalSectionMultiplication R (unitSection R s)) (m + 1)) ≫ 𝟙 _ =
        (CochainComplex.singleFunctor (Modules R) 0).map
            (endoPow (globalSectionMultiplication R (unitSection R s)) (m - k)) ≫
          (CochainComplex.singleFunctor (Modules R) 0).map
            (endoPow (globalSectionMultiplication R (unitSection R s)) (k + 1)),
      koszulStep R s hkm = CochainComplex.mappingCone.map _ _
        ((CochainComplex.singleFunctor (Modules R) 0).map
          (endoPow (globalSectionMultiplication R (unitSection R s)) (m - k)))
        (𝟙 _) square
  /-- The actual coefficient quotient transitions, their pure-tensor normalization,
  and the commuting augmentation, two-term, and derived-limit comparison squares.
  Different tails may be compared on any common tail, in particular their maximum. -/
  coefficients : ∀ (k m : ℕ) (hkm : k ≤ m),
    ∃ q : B R s m ⟶ B R s k,
      quotient R s m ≫ q = quotient R s k ∧
      ∃ e : (M.scalar m).E ⋙ restriction R s m ⟶
          (M.scalar k).E ⋙ restriction R s k,
        (∀ (P : Modules R) (U : Cᵒᵖ) (b : (B R s m).obj.obj U) (x : P.val.obj U),
          (e.app P).val.app U (pure R s m (M.scalar m) P U b x) =
            pure R s k (M.scalar k) P U ((q.hom.app U).hom b) x) ∧
        ∃ c : (M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory ⟶
            (M.scalar k).T ⋙ (restriction R s k).mapDerivedCategory,
          (∀ (P : CochainComplex (Modules R) ℤ),
            CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
            c.app (DerivedCategory.Q.obj P) ≫
                (restriction R s k).mapDerivedCategory.map ((M.scalar k).ε.app P) ≫
                (restriction R s k).mapDerivedCategoryFactors.hom.app
                  (((M.scalar k).E.mapHomologicalComplex (.up ℤ)).obj P) =
              (restriction R s m).mapDerivedCategory.map ((M.scalar m).ε.app P) ≫
                (restriction R s m).mapDerivedCategoryFactors.hom.app
                  (((M.scalar m).E.mapHomologicalComplex (.up ℤ)).obj P) ≫
                DerivedCategory.Q.map
                  ((ordinaryTransition R s (M.scalar m) (M.scalar k) e).app P)) ∧
          (∀ P : CochainComplex (Modules R) ℤ,
            (tensorStep R s hkm).app P ≫ (M.aug k).app P =
              (M.aug m).app P ≫ (ordinaryTransition R s (M.scalar m) (M.scalar k) e).app P) ∧
          (∀ P : CochainComplex (Modules R) ℤ,
            DerivedCategory.Q.map ((tensorStep R s hkm).app P) ≫ (M.A k).hom.app P =
              (M.A m).hom.app P ≫ c.app (DerivedCategory.Q.obj P)) ∧
          (∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (h : ℕ),
            c.app (M.RF.obj (DerivedCategory.Q.obj X)) ≫ M.comparison R s X k h =
              M.comparison R s X m h ≫ M.RF.map (DerivedCategory.Q.map
                ((tail R h).map ((onTowersMap R (tensorStep R s hkm)).app X))))
  /-- The comparison is natural in strict maps of towers. -/
  natural : ∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ} (f : X ⟶ Y) (m h : ℕ),
    ((M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory).map
        (M.RF.map (DerivedCategory.Q.map f)) ≫ M.comparison R s Y m h =
      M.comparison R s X m h ≫ M.RF.map (DerivedCategory.Q.map
        ((tail R h).map ((onTowers R (tensor R s m)).map f)))
  /-- Uniform cohomological bounds gain at most one degree under derived limit. -/
  bounded : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (a b : ℤ),
    (∀ (n : ℕ) (q : ℤ), q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Modules R) q).obj
        (DerivedCategory.Q.obj (X.asFunctor.obj (op n))))) →
    ∀ q : ℤ, q < a ∨ b + 1 < q →
      IsZero ((DerivedCategory.homologyFunctor (Modules R) q).obj
        (M.RF.obj (DerivedCategory.Q.obj X)))


/-- The full comparison assertion, including the available sheafification structure.
The existential sheafification proof is an implementation choice for the small site,
not an additional hypothesis on the scheme or coefficient ring.
Source: Stacks 0941 and the blueprint tower proof paragraph 1
(blueprint: lem-sp-koszul-roos-projection-comparison). -/
def Conclusion : Prop :=
  ∃ i : HasSheafify J CommRingCat.{r},
    letI := i
    ∃ M : Models R s, Compatibility R s M
```

## New

The exact same declaration text above is now in
`Sheaf.Algebra.Homology.KoszulRoosComparisonData`, publicly imported by the original module.
Every existing declaration name, signature, visibility and body is unchanged. Both files
use the existing source's local instances:

```lean
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
```

The original theorem's signature is unchanged. No target or mathematical definition changes.
The definition node `def-sp-koszul-roos-comparison-data` now carries the moved attachments;
the original node keeps its original theorem attachment. No source-library file is edited.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.KoszulRoosProjectionComparison` reported zero
existing downstream modules. Definitions remain publicly available from the original import.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.KoszulRoosProjectionComparison | X5 | Publicly reexports unchanged definitions and proves the comparison. |
| Sheaf.Algebra.Homology.KoszulRoosComparisonData | X5, new | Holds the unchanged definitions. |
| Sheaf.Algebra.Homology.KoszulRoosNormalizedModels | X5, new | Imports the shared definitions for the normalized-model lemma. |
| Sheaf.Algebra.Homology.KoszulRoosCoefficientCompatibility | X5, new | Imports the shared definitions for coefficient coherence. |

No forced adaptation of a module held by another group is made. No statement-review target
is reopened: definitions are moved verbatim, and the instance choices are definitionally equal.

## Status

landed 20261021T154754-L-3172406 2026-10-21 (merge of deliver/X5/Sheaf.Algebra.Homology.KoszulRoosProjectionComparison)
