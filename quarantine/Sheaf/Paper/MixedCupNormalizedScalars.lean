module

public import Sheaf.Paper.PodMixedSupportCupProduct
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.AdmissibleCupCoefficientPassages
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison

/-! # Coefficient comparisons for the mixed-support cup

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
def-pod-mixed-support-cup-product, final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-normalized-scalars).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings
namespace WeilConjectures.MixedCupCoefficientChange
open scoped WeilConjectures.MixedCupCoefficientChange

variable {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)

/-- Final-object sections with their specified coefficient action.
Source: proof step 7 (blueprint: def-sf-mixed-cup-normalized-scalars). -/
abbrev sectionFunctor
    (R : Sheaf (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1})
    (A : Type (u + 1)) [CommRing A]
    (i : A →+* R.obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k)))))) :=
  AlgebraicGeometry.ProEtale.pointModuleSections D.k R ⋙ ModuleCat.restrictScalars i

/-- Ordinary point balancing is fixed on every pure tensor.
Source: proof step 7 and Stacks 03EL
(blueprint: def-sf-mixed-cup-normalized-scalars).
Proof: evaluation at the algebraically closed point commutes with sheafification
and tensor. The two coefficient-section maps are bijective, so the displayed
balanced map is an isomorphism. Pure tensors generate, proving uniqueness. -/
theorem sectionScalar_existsUnique
    {R T : Sheaf (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1}}
    (a : R ⟶ T) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B)
    (i : A →+* R.obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k))))))
    (j : B →+* T.obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k))))))
    (hi : Function.Bijective i) (hj : Function.Bijective j)
    (h : ∀ x, (a.hom.app (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k)))))).hom (i x) =
      j (φ x)) :
    ∃! e : sectionFunctor (D := D) R A i ⋙ ModuleCat.extendScalars φ ≅
        pbcExtend a ⋙ sectionFunctor (D := D) T B j,
      ∀ (M : pbcModules (Spec (.of D.k)) R) (b : B)
        (x : (sectionFunctor (D := D) R A i).obj M),
        e.hom.app M (b ⊗ₜ[A, φ] x) =
          pbcTensorSection a M (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k))))) (j b) x := by
  sorry

/-- The unique ordinary point comparison, with its pure-tensor normalization.
Source: proof step 7 (blueprint: def-sf-mixed-cup-normalized-scalars). -/
def sectionScalar
    {R T : Sheaf (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1}}
    (a : R ⟶ T) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B)
    (i : A →+* R.obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k))))))
    (j : B →+* T.obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k))))))
    (hi : Function.Bijective i) (hj : Function.Bijective j)
    (h : ∀ x, (a.hom.app (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k)))))).hom (i x) =
      j (φ x)) :=
  (sectionScalar_existsUnique a φ i j hi hj h).exists.choose

/-- The derived point map is the descent of the specified ordinary balancing map.
Source: proof step 7 and Stacks 06YY
(blueprint: def-sf-mixed-cup-normalized-scalars).
Proof: use flat K-flat representatives. Exact final-object evaluation sends their
scalar extension to the ordinary balanced tensor of their sections. The universal
derived counits give the displayed equation. Such representatives resolve every
object, hence the equation determines the comparison uniquely and gives its inverse. -/
theorem derivedSectionScalar_existsUnique
    {R T : Sheaf (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1}}
    (a : R ⟶ T) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B)
    (i : A →+* R.obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k))))))
    (j : B →+* T.obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k))))))
    [PreservesFiniteLimits (sectionFunctor (D := D) R A i)]
    [PreservesFiniteColimits (sectionFunctor (D := D) R A i)]
    [PreservesFiniteLimits (sectionFunctor (D := D) T B j)]
    [PreservesFiniteColimits (sectionFunctor (D := D) T B j)]
    (hi : Function.Bijective i) (hj : Function.Bijective j)
    (h : ∀ x, (a.hom.app (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k)))))).hom (i x) =
      j (φ x)) :
    ∃! e : (sectionFunctor (D := D) R A i).mapDerivedCategory ⋙
        ModuleCat.ordinaryDerivedExtendScalars φ ≅
      pbcDerivedExtend a ⋙ (sectionFunctor (D := D) T B j).mapDerivedCategory,
      ∀ (P : CochainComplex (pbcModules (Spec (.of D.k)) R) ℤ)
        (_hp : proEtaleFlatRepresentatives (Spec (.of D.k)) R P),
        (ModuleCat.ordinaryDerivedExtendScalars φ).map
            ((sectionFunctor (D := D) R A i).mapDerivedCategoryFactors.hom.app P) ≫
          (ModuleCat.ordinaryDerivedChangeOfRings φ).counit.app
            (((sectionFunctor (D := D) R A i).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (sectionScalar a φ i j hi hj h) (.up ℤ)).hom.app P) =
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (sectionFunctor (D := D) T B j).mapDerivedCategory.map (pbcComplexCounit a P) ≫
          (sectionFunctor (D := D) T B j).mapDerivedCategoryFactors.hom.app
            (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj P) := by
  sorry

/-- Canonical point scalar extension fixed by ordinary balancing and both counits.
Source: proof step 7 (blueprint: def-sf-mixed-cup-normalized-scalars). -/
def derivedSectionScalar
    {R T : Sheaf (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1}}
    (a : R ⟶ T) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B)
    (i : A →+* R.obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k))))))
    (j : B →+* T.obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k))))))
    [PreservesFiniteLimits (sectionFunctor (D := D) R A i)]
    [PreservesFiniteColimits (sectionFunctor (D := D) R A i)]
    [PreservesFiniteLimits (sectionFunctor (D := D) T B j)]
    [PreservesFiniteColimits (sectionFunctor (D := D) T B j)]
    (hi : Function.Bijective i) (hj : Function.Bijective j)
    (h : ∀ x, (a.hom.app (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k)))))).hom (i x) =
      j (φ x)) :=
  (derivedSectionScalar_existsUnique a φ i j hi hj h).exists.choose

/-- The actual constant coefficient system, with constant-section pullback.
Source: proof step 2 (blueprint: def-sf-mixed-cup-normalized-scalars). -/
def constantCoefficients (A : Type u) [CommRing A] : PurCompactSupport.Coefficients.{u} where
  ring W := (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).obj
    (.of (ULift.{u + 1, u} A))
  pull g := proEtaleConstantRingComparison g A

/-- Constant-section pullback is natural in the coefficient ring.
Source: Stacks 03EL (blueprint: def-sf-mixed-cup-normalized-scalars).
Proof: transpose under inverse image/direct image. Both arrows send every constant
section to the same section. The sheafification universal property gives equality. -/
theorem constantCoefficientSquare {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (g : U ⟶ V) :
    ((constantCoefficients A).pull g).hom ≫
        (constantSheaf (ProEt.topology U) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ)) =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        ((constantSheaf (ProEt.topology V) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ))) ≫
        ((constantCoefficients B).pull g).hom := by
  sorry

/-- The specified map of constant coefficient systems.
Source: proof step 2 (blueprint: def-sf-mixed-cup-normalized-scalars). -/
def constantChange {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    PurCompactSupport.Change (constantCoefficients A) (constantCoefficients B) where
  map W := (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ))
  square g := constantCoefficientSquare φ g

/-- Ringed realizations are used only at finite and integral stages.
The other branches supply the constant coefficient unit and do not identify
rationalized/common-stage categories with ambient module categories.
Source: proof steps 2--4 (blueprint: def-sf-mixed-cup-normalized-scalars). -/
def coefficients : (a : Stage C) → PurCompactSupport.Coefficients.{u}
  | .finite F n => constantCoefficients
      (Padic.coefficientExtensionRing C.l (FieldAt C F) (n + 1))
  | .integral F => PurCompactSupport.completed C.l (FieldAt C F)
  | .rational F => constantCoefficients (FieldAt C F)
  | .closed => constantCoefficients C.Qbar

/-- Actual constant-to-section maps, including the completed integral map.
Source: proof step 7 (blueprint: def-sf-mixed-cup-normalized-scalars). -/
def sectionMap : (a : Stage C) → ring C a →+*
    ((coefficients C a).ring (Spec (.of D.k))).obj.obj
      (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k)))))
  | .finite F n => pointConstantSectionMap D.k
      (Padic.coefficientExtensionRing C.l (FieldAt C F) (n + 1))
  | .integral F => pointIntegralSectionMap C.l (FieldAt C F) D.k
  | .rational F => pointConstantSectionMap D.k (FieldAt C F)
  | .closed => pointConstantSectionMap D.k C.Qbar

/-- Constants give the actual section ring at the algebraically closed point.
Source: proof step 7 (blueprint: def-sf-mixed-cup-normalized-scalars).
Proof: finite and field constants use final-object sheafification. The completed
case is the inverse limit of the same finite quotient identifications; the DVR is
complete, so its constant-to-limit map is bijective. -/
theorem sectionMap_bijective (a : Stage C) : Function.Bijective (sectionMap C a) := by
  sorry

/-- The elementary passages that have an ambient ringed-site presentation.
Source: proof steps 2--3 (blueprint: def-sf-mixed-cup-normalized-scalars). -/
inductive RingedPassage : {a b : Stage C} → Passage C a b → Type (u + 1) where
  | finite {F G : Padic.FiniteCoefficientFields C.l C.Qbar} {n m : ℕ}
      (φ : Padic.coefficientExtensionRing C.l (FieldAt C F) (n + 1) →+*
        Padic.coefficientExtensionRing C.l (FieldAt C G) (m + 1)) :
      RingedPassage (.finite φ)
  | reduction (F : Padic.FiniteCoefficientFields C.l C.Qbar) (n : ℕ) :
      RingedPassage (.reduction F n)
  | integral {F G : Padic.FiniteCoefficientFields C.l C.Qbar} (h : F ≤ G) :
      RingedPassage (.integral h)

/-- The recorded coefficient sheaf map, never a freely supplied morphism.
Source: proof steps 2--3 (blueprint: def-sf-mixed-cup-normalized-scalars). -/
def ringedChange : {a b : Stage C} → (f : Passage C a b) → RingedPassage C f →
    PurCompactSupport.Change (coefficients C a) (coefficients C b)
  | _, _, _, .finite φ => constantChange φ
  | _, _, _, .reduction F n => PurCompactSupport.reduction C.l (FieldAt C F) (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
  | _, _, _, .integral (F := F) (G := G) h => PurCompactSupport.completedChange C.l
      (FieldAt C F) (FieldAt C G)
      (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar F G h)

/-- The coefficient map and the actual section maps form the prescribed square.
Source: proof step 7 (blueprint: def-sf-mixed-cup-normalized-scalars).
Proof: at finite stages use naturality of constant sections. For reduction use
the completed projection equation. For integral extension project to each finite
quotient, where the coefficient-inclusion square is the constant-section square;
the projections of the completed target are jointly monic. -/
theorem sectionMap_square {a b : Stage C} (f : Passage C a b) (hf : RingedPassage C f)
    (x : ring C a) :
    (((ringedChange C f hf).map (Spec (.of D.k))).hom.app
        (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k)))))).hom (sectionMap C a x) =
      sectionMap C b ((coefficientMap C f).hom x) := by
  sorry

/-- Exact final-object evaluation with restriction along any section-ring map.
Source: Stacks 0946 (blueprint: def-sf-mixed-cup-normalized-scalars). -/
instance sectionLimits
    (R : Sheaf (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1})
    (A : Type (u + 1)) [CommRing A]
    (i : A →+* R.obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k)))))) :
    PreservesFiniteLimits (sectionFunctor (D := D) R A i) := by
  let := ((@AlgebraicGeometry.ProEtale.point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2 R).1
  exact inferInstanceAs (PreservesFiniteLimits
    (AlgebraicGeometry.ProEtale.pointModuleSections D.k R ⋙ ModuleCat.restrictScalars i))

/-- Exact final-object evaluation also preserves finite colimits.
Source: Stacks 0946 (blueprint: def-sf-mixed-cup-normalized-scalars). -/
instance sectionColimits
    (R : Sheaf (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1})
    (A : Type (u + 1)) [CommRing A]
    (i : A →+* R.obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k)))))) :
    PreservesFiniteColimits (sectionFunctor (D := D) R A i) := by
  let := ((@AlgebraicGeometry.ProEtale.point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2 R).2.1
  exact inferInstanceAs (PreservesFiniteColimits
    (AlgebraicGeometry.ProEtale.pointModuleSections D.k R ⋙ ModuleCat.restrictScalars i))

/-- The normalized point comparison for a finite or integral elementary passage.
Source: proof step 7 (blueprint: def-sf-mixed-cup-normalized-scalars). -/
def ringedPoint {a b : Stage C} (f : Passage C a b) (hf : RingedPassage C f) :=
  derivedSectionScalar ((ringedChange C f hf).map (Spec (.of D.k)))
    (coefficientMap C f).hom (sectionMap C a) (sectionMap C b)
    (sectionMap_bijective C a) (sectionMap_bijective C b) (sectionMap_square C f hf)

/-- Exact ordinary scalar extension is identified with its universal left derived
functor by the actual derived counit on every complex.
Source: proof steps 4 and 7 (blueprint: def-sf-mixed-cup-normalized-scalars).
Proof: exactness makes the termwise functor a localization. Its factorization and
the universal left-derived counit identify the two functors uniquely; their maps
are inverse because the same universal equation fixes both composites. -/
theorem exactScalar_existsUnique {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) [PreservesFiniteLimits (ModuleCat.extendScalars φ)]
    [PreservesFiniteColimits (ModuleCat.extendScalars φ)] :
    ∃! e : ModuleCat.ordinaryDerivedExtendScalars φ ≅
        (ModuleCat.extendScalars φ).mapDerivedCategory,
      ∀ P : CochainComplex (ModuleCat.{u + 1} A) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (ModuleCat.extendScalars φ).mapDerivedCategoryFactors.hom.app P =
          (ModuleCat.ordinaryDerivedChangeOfRings φ).counit.app P := by
  sorry

/-- Exact scalar transport with its universal normalization.
Source: proof steps 4 and 7 (blueprint: def-sf-mixed-cup-normalized-scalars). -/
def exactScalar {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) [PreservesFiniteLimits (ModuleCat.extendScalars φ)]
    [PreservesFiniteColimits (ModuleCat.extendScalars φ)] :=
  (exactScalar_existsUnique φ).exists.choose

/-- Scalar extension commutes with the carrier/coefficient lift by its pure-tensor
formula. The derived comparison is fixed by both universal factorization maps.
Source: proof step 7 (blueprint: def-sf-mixed-cup-normalized-scalars).
Proof: send b tensor up(x) to up(down(b) tensor x). This is balanced and invertible
and natural on ordinary modules. Tensor with a field is exact; take its termwise
derived map and the specified localization factorizations. The pure tensors fix
the ordinary isomorphism, and localization fixes its derived lift. -/
theorem carrierScalar_existsUnique (F G : Type u) [Field F] [Field G] (φ : F →+* G) :
    ∃! e : (pointFibreModuleLift F).mapDerivedCategory ⋙
        (ModuleCat.extendScalars (RingHom.ulift.{u + 1, u + 1} φ)).mapDerivedCategory ≅
      (DerivedCategory.fieldDerivedScalarExtension φ) ⋙
        (pointFibreModuleLift G).mapDerivedCategory,
      ∃ e₀ : pointFibreModuleLift F ⋙
          ModuleCat.extendScalars (RingHom.ulift.{u + 1, u + 1} φ) ≅
        ModuleCat.extendScalars φ ⋙ pointFibreModuleLift G,
      (∀ (M : ModuleCat.{u} F) (b : ULift.{u + 1, u} G) (x : M),
        e₀.hom.app M (b ⊗ₜ[ULift.{u + 1, u} F, RingHom.ulift φ] ULift.up x) =
          ULift.up (b.down ⊗ₜ[F, φ] x)) ∧
      e = (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso e₀ ≪≫ Functor.mapDerivedCategoryCompIso _ _ := by
  sorry

/-- The pure-tensor carrier transport, with no new automorphism choices.
Source: proof step 7 (blueprint: def-sf-mixed-cup-normalized-scalars). -/
def carrierScalar (F G : Type u) [Field F] [Field G] (φ : F →+* G) :=
  (carrierScalar_existsUnique F G φ).exists.choose

end WeilConjectures.MixedCupCoefficientChange
