# scalarMate shared identification declarations

## Reason

The existing tensor/pullback normalization imports the item solely for its definitions. The item needs that strictly simpler normalization to prove its mate equality. Move these shared declarations to an identification-only module, retain their names, public signatures and definition bodies, and publicly re-export them at the old module. This removes the import cycle without changing any operation or target statement. The two existence-and-uniqueness proofs specialize the existing arbitrary-ring-sheaf comparisons in DerivedScalarMateThickLocus. Their normalized selected data are definitionally those specializations. No arbitrary existential data are introduced.

## Old

In lean/Sheaf/Paper/ProEtaleScalarMateNormalization.lean:

```lean
/-- The actual scalar restriction, with unchanged underlying abelian sheaf.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable abbrev scalarMateRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  Scheme.proEtaleRingRestrictScalars (Scheme.proEtaleConstantRingMap (T := W) φ)

/-- The coefficient B_W with its A_W action, without deriving or resolving B.
Source: Stacks 0B56 (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable abbrev scalarMateCoefficient {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  (scalarMateRestriction φ W).obj (SheafOfModules.unit
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing W B)))

/-- The degree-zero coefficient complex B_W, as an A_W-module complex.
Source: Stacks 0B56 (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable abbrev scalarMateCoefficientComplex {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  (CochainComplex.singleFunctor (Scheme.proEtaleRingModules W
    (Scheme.proEtaleConstantRing W A)) (0 : ℤ)).obj (scalarMateCoefficient φ W)

/-- The existing ordinary tensor with B as its last factor.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable abbrev scalarMateOrdinaryTensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  (Scheme.proEtaleOrdinaryTensor W (Scheme.proEtaleConstantRing W A)).flip.obj
    (scalarMateCoefficient φ W)

/-- The original sheafification image of b tensor m in scalar extension.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateTensorSection {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (M : Scheme.proEtaleRingModules W (Scheme.proEtaleConstantRing W A))
    (U : W.ProEtᵒᵖ) (b : (Scheme.proEtaleConstantRing W B).obj.obj U)
    (m : M.val.obj U) :
    (SheafOfModules.changeOfRings (Scheme.proEtaleConstantRingMap (T := W) φ) M).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing W B))
    (𝟙 _)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
            (Scheme.proEtaleConstantRingMap (T := W) φ) M)).app U)
    (b ⊗ₜ[_, ((Scheme.proEtaleConstantRingMap (T := W) φ).hom.app U).hom] m)

/-- The normalization on all sectionwise pure tensors, including nonconstant local scalars.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
def IsScalarMateOrdinaryTensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (e : Scheme.proEtaleRingExtension (Scheme.proEtaleConstantRingMap (T := W) φ) ⋙
      scalarMateRestriction φ W ≅ scalarMateOrdinaryTensor φ W) : Prop :=
  ∀ (M : Scheme.proEtaleRingModules W (Scheme.proEtaleConstantRing W A))
    (U : W.ProEtᵒᵖ) (b : (Scheme.proEtaleConstantRing W B).obj.obj U)
    (m : M.val.obj U),
    ((scalarMateRestriction φ W).map
      (eqToHom (Scheme.proEtaleRingExtension_obj
        (Scheme.proEtaleConstantRingMap (T := W) φ) M).symm) ≫
      e.hom.app M).val.app U (scalarMateTensorSection φ W M U b m) =
        Scheme.proEtaleTensorPair W (Scheme.proEtaleConstantRing W A) M
          (scalarMateCoefficient φ W) U m b

/-- The canonical ordinary identification, uniquely fixed by balanced pure tensors.
Source: Stacks 03EK, 06YY (blueprint: lem-fix-proetale-scalar-mate-normalization).
Proof: the restricted scalar extension and tensor have the same balanced tensor
abelian presheaf, with factors reversed. Sheafify this identification. The inverse
reverses the factors back; both composites fix pure tensors. The balancing relation
proves linearity, and id tensor a proves naturality. Sheafification uniqueness proves
that the displayed formula determines the natural isomorphism uniquely. This is
step 1 of the node, retaining its specified normalization. -/
theorem scalarMateOrdinaryTensorIso_existsUnique
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u}) :
    ∃! e : Scheme.proEtaleRingExtension (Scheme.proEtaleConstantRingMap (T := W) φ) ⋙
        scalarMateRestriction φ W ≅ scalarMateOrdinaryTensor φ W,
      IsScalarMateOrdinaryTensor φ W e := by
  sorry

/-- The uniquely normalized ordinary identification; its data are determined by the formula.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateOrdinaryTensorIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u}) :=
  Classical.choose (scalarMateOrdinaryTensorIso_existsUnique φ W).exists

/-- The canonical restriction/direct-image comparison of the recorded ring-sheaf adjunction.
Source: Stacks 0D6E (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateRestrictionPush
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  Scheme.proEtaleRingRestrictionDerivedDirectImage f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRing T A) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingMap (T := T) φ)
    (Scheme.proEtaleConstantRingComparison f A) (Scheme.proEtaleConstantRingComparison f B)
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm


/-- On complexes, reverse the balanced tensors degreewise and use the degree-zero
single-factor identification. This is an actual chain isomorphism.
Source: Stacks 06YY (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateOrdinaryComplexIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (P : CochainComplex (Scheme.proEtaleRingModules W (Scheme.proEtaleConstantRing W A)) ℤ) :=
  (Functor.mapHomologicalComplexCompIso (scalarMateOrdinaryTensorIso φ W)
    (ComplexShape.up ℤ)).app P ≪≫
      (CochainComplex.mapBifunctorSingle₂Iso
        (Scheme.proEtaleOrdinaryTensor W (Scheme.proEtaleConstantRing W A))
        (scalarMateCoefficient φ W) P).symm

/-- The full normalization of h on two flat K-flat representatives, resolving B too.
The equation uses Q → B[0] only after tensoring with the K-flat first factor.
Source: Stacks 06YY, 07A4 (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
def IsScalarMateDerivedTensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (a : Scheme.ProEtaleTensorModel W (Scheme.proEtaleConstantRing W A))
    (h : directImageScalarExtension φ W ⋙ (scalarMateRestriction φ W).mapDerivedCategory ≅
      (Functor.curryObj a.tensor).flip.obj
        (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ W))) : Prop :=
  ∀ (P Q : CochainComplex (Scheme.proEtaleRingModules W
      (Scheme.proEtaleConstantRing W A)) ℤ)
    (hp : Scheme.proEtaleFlatRepresentatives W (Scheme.proEtaleConstantRing W A) P)
    (hq : Scheme.proEtaleFlatRepresentatives W (Scheme.proEtaleConstantRing W A) Q)
    (q : Q ⟶ scalarMateCoefficientComplex φ W), QuasiIso q →
    a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
      a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q)) ≫
      h.inv.app (DerivedCategory.Q.obj P) ≫
      (scalarMateRestriction φ W).mapDerivedCategory.map
        ((Scheme.proEtaleRingDerivedExtensionCounit
          (Scheme.proEtaleConstantRingMap (T := W) φ)).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
      (scalarMateRestriction φ W).mapDerivedCategoryFactorsh.hom.app
        (((Scheme.proEtaleRingExtension
          (Scheme.proEtaleConstantRingMap (T := W) φ)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
    DerivedCategory.Q.map
      (HomologicalComplex.mapBifunctorMap (𝟙 P) q
        (Scheme.proEtaleOrdinaryTensor W (Scheme.proEtaleConstantRing W A))
        (ComplexShape.up ℤ) ≫ (scalarMateOrdinaryComplexIso φ W P).inv)

/-- The restricted extension is the derived tensor with B, with its full normalization.
Source: Stacks 06YY, 07A4 (blueprint: lem-fix-proetale-scalar-mate-normalization).
Proof: use step 1 of the node. Resolve the first input P and B[0] by flat K-flat
complexes. The ordinary complex identification is identity on the balanced tensor,
with the symmetry putting B last. Tensoring P with the resolution of B is a
quasi-isomorphism because P is K-flat, even when B is nonflat. The scalar derived
counit is invertible on P. These maps construct h and give the displayed equation.
Naturality descends from the ordinary comparison through the resolving-class
localization. Every derived object has such a representative, so the equation
uniquely determines h, including compatibility with changes of resolutions. -/
theorem scalarMateDerivedTensorIso_existsUnique
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (a : Scheme.ProEtaleTensorModel W (Scheme.proEtaleConstantRing W A)) :
    ∃! h : directImageScalarExtension φ W ⋙ (scalarMateRestriction φ W).mapDerivedCategory ≅
        (Functor.curryObj a.tensor).flip.obj
          (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ W)),
      IsScalarMateDerivedTensor φ W a h := by
  sorry

/-- The comparison h selected by its unique representative normalization.
Source: Stacks 06YY (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateDerivedTensorIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (a : Scheme.ProEtaleTensorModel W (Scheme.proEtaleConstantRing W A)) :=
  Classical.choose (scalarMateDerivedTensorIso_existsUnique φ W a).exists


/-- The tensor unit in the existing constant-ring module category.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable abbrev scalarMateUnit (B : Type u) [CommRing B] (W : Scheme.{u}) :=
  SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing W B))

/-- The normalized ordinary B-unit pullback, supplied by the projection-arrow interface.
Source: Stacks 03EL (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateUnitPullback (B : Type u) [CommRing B]
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  Classical.choose (Scheme.proEtaleProjectionUnit_existsUnique f
    (Scheme.proEtaleConstantRing V B) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingComparison f B)).exists

/-- The ordinary identification u_A^*(B_V)=B_T, using scalar restriction and unit pullback.
Source: Stacks 03EL, 0D6D (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateCoefficientPullback
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  letI := Scheme.proEtaleRingRestrictionPullbackInv_isIso f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRing T A) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingMap (T := T) φ)
    (Scheme.proEtaleConstantRingComparison f A) (Scheme.proEtaleConstantRingComparison f B)
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm
  (asIso (Scheme.proEtaleRingRestrictionPullbackInv f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRing T A) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingMap (T := T) φ)
    (Scheme.proEtaleConstantRingComparison f A) (Scheme.proEtaleConstantRingComparison f B)
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm)).app (scalarMateUnit B V) ≪≫
    (scalarMateRestriction φ T).mapIso (scalarMateUnitPullback B f)

/-- The coefficient identification on degree-zero complexes, with exact pullback factors.
Source: Stacks 07A4 (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateDerivedCoefficientPullback
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  (Scheme.proEtaleRingDerivedPullbackFactors f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing T A)
    (Scheme.proEtaleConstantRingComparison f A)).app (scalarMateCoefficientComplex φ V) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.proEtaleConstantRingPullback A f) (ComplexShape.up ℤ) 0).app
          (scalarMateCoefficient φ V)) ≪≫
    DerivedCategory.Q.mapIso
      ((CochainComplex.singleFunctor
        (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)) (0 : ℤ)).mapIso
          (scalarMateCoefficientPullback φ f))

```

## New

In lean/Sheaf/Paper/ProEtaleScalarMateIdentifications.lean, publicly imported by the old module:

```lean
/-- The actual scalar restriction, with unchanged underlying abelian sheaf.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable abbrev scalarMateRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  Scheme.proEtaleRingRestrictScalars (Scheme.proEtaleConstantRingMap (T := W) φ)

/-- The coefficient B_W with its A_W action, without deriving or resolving B.
Source: Stacks 0B56 (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable abbrev scalarMateCoefficient {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  (scalarMateRestriction φ W).obj (SheafOfModules.unit
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing W B)))

/-- The degree-zero coefficient complex B_W, as an A_W-module complex.
Source: Stacks 0B56 (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable abbrev scalarMateCoefficientComplex {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  (CochainComplex.singleFunctor (Scheme.proEtaleRingModules W
    (Scheme.proEtaleConstantRing W A)) (0 : ℤ)).obj (scalarMateCoefficient φ W)

/-- The existing ordinary tensor with B as its last factor.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable abbrev scalarMateOrdinaryTensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  (Scheme.proEtaleOrdinaryTensor W (Scheme.proEtaleConstantRing W A)).flip.obj
    (scalarMateCoefficient φ W)

/-- The original sheafification image of b tensor m in scalar extension.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateTensorSection {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (M : Scheme.proEtaleRingModules W (Scheme.proEtaleConstantRing W A))
    (U : W.ProEtᵒᵖ) (b : (Scheme.proEtaleConstantRing W B).obj.obj U)
    (m : M.val.obj U) :
    (SheafOfModules.changeOfRings (Scheme.proEtaleConstantRingMap (T := W) φ) M).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing W B))
    (𝟙 _)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
            (Scheme.proEtaleConstantRingMap (T := W) φ) M)).app U)
    (b ⊗ₜ[_, ((Scheme.proEtaleConstantRingMap (T := W) φ).hom.app U).hom] m)

/-- The normalization on all sectionwise pure tensors, including nonconstant local scalars.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
def IsScalarMateOrdinaryTensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (e : Scheme.proEtaleRingExtension (Scheme.proEtaleConstantRingMap (T := W) φ) ⋙
      scalarMateRestriction φ W ≅ scalarMateOrdinaryTensor φ W) : Prop :=
  ∀ (M : Scheme.proEtaleRingModules W (Scheme.proEtaleConstantRing W A))
    (U : W.ProEtᵒᵖ) (b : (Scheme.proEtaleConstantRing W B).obj.obj U)
    (m : M.val.obj U),
    ((scalarMateRestriction φ W).map
      (eqToHom (Scheme.proEtaleRingExtension_obj
        (Scheme.proEtaleConstantRingMap (T := W) φ) M).symm) ≫
      e.hom.app M).val.app U (scalarMateTensorSection φ W M U b m) =
        Scheme.proEtaleTensorPair W (Scheme.proEtaleConstantRing W A) M
          (scalarMateCoefficient φ W) U m b

/-- The canonical ordinary identification, uniquely fixed by balanced pure tensors.
Source: Stacks 03EK, 06YY (blueprint: lem-fix-proetale-scalar-mate-normalization).
Proof: the restricted scalar extension and tensor have the same balanced tensor
abelian presheaf, with factors reversed. Sheafify this identification. The inverse
reverses the factors back; both composites fix pure tensors. The balancing relation
proves linearity, and id tensor a proves naturality. Sheafification uniqueness proves
that the displayed formula determines the natural isomorphism uniquely. This is
step 1 of the node, retaining its specified normalization. -/
theorem scalarMateOrdinaryTensorIso_existsUnique
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u}) :
    ∃! e : Scheme.proEtaleRingExtension (Scheme.proEtaleConstantRingMap (T := W) φ) ⋙
        scalarMateRestriction φ W ≅ scalarMateOrdinaryTensor φ W,
      IsScalarMateOrdinaryTensor φ W e := by
  exact Scheme.DerivedScalarMate.ordinaryTensorIso_existsUnique
    (Scheme.proEtaleConstantRingMap (T := W) φ)

/-- The uniquely normalized ordinary identification; its data are determined by the formula.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateOrdinaryTensorIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u}) :=
  Classical.choose (scalarMateOrdinaryTensorIso_existsUnique φ W).exists

/-- The canonical restriction/direct-image comparison of the recorded ring-sheaf adjunction.
Source: Stacks 0D6E (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateRestrictionPush
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  Scheme.proEtaleRingRestrictionDerivedDirectImage f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRing T A) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingMap (T := T) φ)
    (Scheme.proEtaleConstantRingComparison f A) (Scheme.proEtaleConstantRingComparison f B)
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm


/-- On complexes, reverse the balanced tensors degreewise and use the degree-zero
single-factor identification. This is an actual chain isomorphism.
Source: Stacks 06YY (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateOrdinaryComplexIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (P : CochainComplex (Scheme.proEtaleRingModules W (Scheme.proEtaleConstantRing W A)) ℤ) :=
  (Functor.mapHomologicalComplexCompIso (scalarMateOrdinaryTensorIso φ W)
    (ComplexShape.up ℤ)).app P ≪≫
      (CochainComplex.mapBifunctorSingle₂Iso
        (Scheme.proEtaleOrdinaryTensor W (Scheme.proEtaleConstantRing W A))
        (scalarMateCoefficient φ W) P).symm

/-- The full normalization of h on two flat K-flat representatives, resolving B too.
The equation uses Q → B[0] only after tensoring with the K-flat first factor.
Source: Stacks 06YY, 07A4 (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
def IsScalarMateDerivedTensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (a : Scheme.ProEtaleTensorModel W (Scheme.proEtaleConstantRing W A))
    (h : directImageScalarExtension φ W ⋙ (scalarMateRestriction φ W).mapDerivedCategory ≅
      (Functor.curryObj a.tensor).flip.obj
        (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ W))) : Prop :=
  ∀ (P Q : CochainComplex (Scheme.proEtaleRingModules W
      (Scheme.proEtaleConstantRing W A)) ℤ)
    (hp : Scheme.proEtaleFlatRepresentatives W (Scheme.proEtaleConstantRing W A) P)
    (hq : Scheme.proEtaleFlatRepresentatives W (Scheme.proEtaleConstantRing W A) Q)
    (q : Q ⟶ scalarMateCoefficientComplex φ W), QuasiIso q →
    a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
      a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q)) ≫
      h.inv.app (DerivedCategory.Q.obj P) ≫
      (scalarMateRestriction φ W).mapDerivedCategory.map
        ((Scheme.proEtaleRingDerivedExtensionCounit
          (Scheme.proEtaleConstantRingMap (T := W) φ)).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
      (scalarMateRestriction φ W).mapDerivedCategoryFactorsh.hom.app
        (((Scheme.proEtaleRingExtension
          (Scheme.proEtaleConstantRingMap (T := W) φ)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
    DerivedCategory.Q.map
      (HomologicalComplex.mapBifunctorMap (𝟙 P) q
        (Scheme.proEtaleOrdinaryTensor W (Scheme.proEtaleConstantRing W A))
        (ComplexShape.up ℤ) ≫ (scalarMateOrdinaryComplexIso φ W P).inv)

/-- The restricted extension is the derived tensor with B, with its full normalization.
Source: Stacks 06YY, 07A4 (blueprint: lem-fix-proetale-scalar-mate-normalization).
Proof: use step 1 of the node. Resolve the first input P and B[0] by flat K-flat
complexes. The ordinary complex identification is identity on the balanced tensor,
with the symmetry putting B last. Tensoring P with the resolution of B is a
quasi-isomorphism because P is K-flat, even when B is nonflat. The scalar derived
counit is invertible on P. These maps construct h and give the displayed equation.
Naturality descends from the ordinary comparison through the resolving-class
localization. Every derived object has such a representative, so the equation
uniquely determines h, including compatibility with changes of resolutions. -/
theorem scalarMateDerivedTensorIso_existsUnique
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (a : Scheme.ProEtaleTensorModel W (Scheme.proEtaleConstantRing W A)) :
    ∃! h : directImageScalarExtension φ W ⋙ (scalarMateRestriction φ W).mapDerivedCategory ≅
        (Functor.curryObj a.tensor).flip.obj
          (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ W)),
      IsScalarMateDerivedTensor φ W a h := by
  exact Scheme.DerivedScalarMate.derivedTensorIso_existsUnique
    (Scheme.proEtaleConstantRingMap (T := W) φ) a

/-- The comparison h selected by its unique representative normalization.
Source: Stacks 06YY (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateDerivedTensorIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (a : Scheme.ProEtaleTensorModel W (Scheme.proEtaleConstantRing W A)) :=
  Classical.choose (scalarMateDerivedTensorIso_existsUnique φ W a).exists


/-- The tensor unit in the existing constant-ring module category.
Source: Stacks 03EK (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable abbrev scalarMateUnit (B : Type u) [CommRing B] (W : Scheme.{u}) :=
  SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing W B))

/-- The normalized ordinary B-unit pullback, supplied by the projection-arrow interface.
Source: Stacks 03EL (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateUnitPullback (B : Type u) [CommRing B]
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  Classical.choose (Scheme.proEtaleProjectionUnit_existsUnique f
    (Scheme.proEtaleConstantRing V B) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingComparison f B)).exists

/-- The ordinary identification u_A^*(B_V)=B_T, using scalar restriction and unit pullback.
Source: Stacks 03EL, 0D6D (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateCoefficientPullback
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  letI := Scheme.proEtaleRingRestrictionPullbackInv_isIso f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRing T A) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingMap (T := T) φ)
    (Scheme.proEtaleConstantRingComparison f A) (Scheme.proEtaleConstantRingComparison f B)
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm
  (asIso (Scheme.proEtaleRingRestrictionPullbackInv f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRing T A) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingMap (T := T) φ)
    (Scheme.proEtaleConstantRingComparison f A) (Scheme.proEtaleConstantRingComparison f B)
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm)).app (scalarMateUnit B V) ≪≫
    (scalarMateRestriction φ T).mapIso (scalarMateUnitPullback B f)

/-- The coefficient identification on degree-zero complexes, with exact pullback factors.
Source: Stacks 07A4 (blueprint: lem-fix-proetale-scalar-mate-normalization). -/
noncomputable def scalarMateDerivedCoefficientPullback
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  (Scheme.proEtaleRingDerivedPullbackFactors f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing T A)
    (Scheme.proEtaleConstantRingComparison f A)).app (scalarMateCoefficientComplex φ V) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.proEtaleConstantRingPullback A f) (ComplexShape.up ℤ) 0).app
          (scalarMateCoefficient φ V)) ≪≫
    DerivedCategory.Q.mapIso
      ((CochainComplex.singleFunctor
        (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)) (0 : ℤ)).mapIso
          (scalarMateCoefficientPullback φ f))

```

## Users

The following complete transitive consumer list is from tools/downstream.py with --uses scalarMateDerivedTensorIso. Every scalarMate declaration is moved together and the old public import closure is retained. Only the representative normalization import changes; consumers of the final theorem still import its original module. No target meaning changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ProEtaleScalarMateNormalization | H1 | Same theorem signature; shared declarations publicly re-exported. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.AffineCompactificationComparisonNormalization | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.AffineCounitScalar | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.AffineLineCanonicalScalarCounit | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.BrownTowerBoundedTransport | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.BrownTowerGeometricTransport | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.BrownTowerRealization | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.BrownTowerSite | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ChartCounitScalarTransport | T8 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.CoefSupportOpenTensorModel | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.CoefSupportPointSectionsData | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | D6 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | A2 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ConcreteProjectionReductionSquare | D7 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | No change due to the declaration move; separately adapts the generalized theorem call. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.EtaleOriginScalarProjectionSquare | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y7 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.EtaleSumCounitScalar | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | P8 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportDomains | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | G6 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | T2 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.OpenExceptionalScalarLocality | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.OpenProEtaleCounitScalar | F3 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.P1CounitScalar | F4 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.P1SplittingScalar | G1 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.PfReductionProperOpenIdentities | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | Y5 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ProperEtaleOriginScalarData | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ProperEtaleOriginScalarIsomorphism | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.RawChartScalarCounitPasting | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ReductionSiteCoefficientPasting | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluing | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.UnboundedCoefficientPullbackModel | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleScalarBalancingChain | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | Import only the identification module; same scalarMate definitions. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SecSmoothPurity.Reduction | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | K5 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SecSmoothPurity.SupportedScalarTorInterval | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.CoefPairingFiniteNormalization | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.CoefPairingSystemDinaturality | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeRealization | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.FiniteCounitRestrictionSquare | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierModels | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Same public names, signatures and definition bodies remain re-exported; no adaptation. |

## Status

landed 20261025T101113-L-3657498 2026-10-25 (merge of deliver/H1/Sheaf.Paper.ProEtaleScalarMateNormalization)
