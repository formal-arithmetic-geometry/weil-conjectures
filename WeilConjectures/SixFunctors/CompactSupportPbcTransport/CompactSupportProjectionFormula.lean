/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SfProEtaleProjection.SfProEtaleProjectionFormula
import all WeilConjectures.SixFunctors.SfProEtaleProjection.SfProEtaleProjectionFormula
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
public import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
public import WeilConjectures.DeligneLaumon.ZlFrobeniusCompactSupportComparison
public import WeilConjectures.DeligneLaumon.FieldWeilShriekShiftData
public import WeilConjectures.SixFunctors.Rational.RationalCoefficientCategoryComparison
public import WeilConjectures.SixFunctors.WfTensorCompletion.WfTensorCompletionFrobenius
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
public import WeilConjectures.SixFunctors.CompactSupportCoefficientTensor.ProjectionTensorCoefficientComparison
public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
public import Mathlib.CategoryTheory.Products.Basic
import all WeilConjectures.SixFunctors.Supporting.ProjectionWeilTensorDomainBridge
import WeilConjectures.SixFunctors.PurCompactSupport.CompactSupportProjectionCoefficientChange
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingComposition
import WeilConjectures.SixFunctors.Compact.CompactSupportProjectionFiniteStages
import WeilConjectures.SixFunctors.Compact.CompactSupportProjectionIntegralStages
import WeilConjectures.SixFunctors.Compact.CompactSupportProjectionFieldStages
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationNaturalIso
/-! # Compact-support projection formula at every coefficient stage
Source: blueprint main-20261015, sec-six-functors/sk-rem-sf-pf-done,
fix-prop-projection-formula (blueprint: fix-prop-projection-formula).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

set_option genInjectivity false
set_option genSizeOfSpec false
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  Padic.coefficientExtensionIntegers HasDerivedCategory.standard
universe u v w v' w' a b c d ha hb hc hd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection
open scoped CategoryTheory.Functor
private theorem iso_cancel_middle
    {A : Type a} [Category.{ha} A] {X Y Z W : A}
    (e : Y ≅ Z) (f : X ⟶ Y) (g : Y ⟶ W) :
    (f ≫ e.hom) ≫ (e.inv ≫ g) = f ≫ g := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem unit_whisker_app
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{ha} A] [Category.{hb} B] [Category.{hc} C] [Category.{hd} D]
    (L : A ⥤ B) (Δ : B ⥤ C) (R : C ⥤ B) {S U : A ⥤ D} (T : D ⥤ C)
    (η : 𝟭 B ⟶ Δ ⋙ R) (α : L ⋙ Δ ⟶ S ⋙ T) (β : S ⟶ U) (K : A) :
    (L.rightUnitor.inv ≫ Functor.whiskerLeft L η ≫
        (Functor.associator L Δ R).inv ≫
          Functor.whiskerRight (α ≫ Functor.whiskerRight β T) R).app K =
      η.app (L.obj K) ≫ R.map (α.app K ≫ T.map (β.app K)) := by
  simp only [NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp]

private theorem localizedTransportIso_existsUnique
    (R : Type a) [CommRing R] (A : Type b) [Category.{ha} A]
    [Preadditive A] [Linear R A] [HasZeroObject A] [HasShift A ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A] [IsTriangulated A]
    [∀ n : ℤ, (shiftFunctor A n).Linear R] (p : R)
    (F G : A ⥤ A) [F.Additive] [G.Additive] [F.Linear R] [G.Linear R] (e : F ≅ G) :
    ∃! b : ScalarLocalization.transport R p F ≅ ScalarLocalization.map R A p G,
      ∀ K : A, HEq (b.hom.app ((ScalarLocalization.localization R A p).obj K))
        ((ScalarLocalization.localization R A p).map (e.hom.app K)) := by
  obtain ⟨b, hb, hu⟩ := ScalarLocalization.naturalIso_of_integral R A p
    (ScalarLocalization.transport R p F) (ScalarLocalization.map R A p G)
    (Functor.isoWhiskerRight e (ScalarLocalization.localization R A p))
  refine ⟨b, ?_, ?_⟩
  · intro K
    exact heq_of_eq (hb K)
  · intro b' hb'
    apply hu b'
    intro K
    exact eq_of_heq (hb' K)

private theorem inverseUnit_naturality
    {A : Type a} {B : Type b} [Category.{ha} A] [Category.{hb} B]
    {F H G : A ⥤ B} (η : F ⟶ H) (δ : F ≅ G)
    (e : ∀ K, H.obj K ≅ G.obj K)
    (he : ∀ K, η.app K ≫ (e K).hom = δ.hom.app K)
    {K L : A} (f : K ⟶ L) :
    H.map f ≫ (e L).hom = (e K).hom ≫ G.map f := by
  have hc : IsIso (η.app K ≫ (e K).hom) :=
    (he K).symm ▸ (inferInstance : IsIso (δ.hom.app K))
  have : IsIso (η.app K) := (isIso_comp_right_iff _ (e K).hom).mp hc
  apply (cancel_epi (η.app K)).mp
  calc
    η.app K ≫ (H.map f ≫ (e L).hom) =
        (F.map f ≫ η.app L) ≫ (e L).hom := by rw [← Category.assoc, η.naturality]
    _ = F.map f ≫ δ.hom.app L := by rw [Category.assoc, he L]
    _ = δ.hom.app K ≫ G.map f := δ.hom.naturality f
    _ = η.app K ≫ ((e K).hom ≫ G.map f) := by rw [← he K, Category.assoc]

private theorem fixedPair_obj_carrier
    {A : Type a} {B : Type b} [Category.{ha} A] [Category.{hb} B]
    {P : A ⥤ A} {Q : B ⥤ B} {G : A ⥤ B}
    (J : CategoryTheory.Endofunctor.IsoAlgebra P ⥤
      CategoryTheory.Endofunctor.IsoAlgebra Q)
    (α : G ⋙ Q ≅ P ⋙ G)
    (h : J = CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso α)
    (K : CategoryTheory.Endofunctor.IsoAlgebra P) :
    (J.obj K).carrier = G.obj K.carrier := by
  rw [h]
  rfl

private theorem fixedPair_map_heq
    {A : Type a} {B : Type b} [Category.{ha} A] [Category.{hb} B]
    {P : A ⥤ A} {Q : B ⥤ B} {G : A ⥤ B}
    (J : Endofunctor.IsoAlgebra P ⥤ Endofunctor.IsoAlgebra Q) (α : G ⋙ Q ≅ P ⋙ G)
    (h : J = Endofunctor.IsoAlgebra.mapOfNatIso α)
    {K L : Endofunctor.IsoAlgebra P} (f : K ⟶ L) :
    HEq (J.map f).hom.f (G.map f.hom.f) := by
  subst J
  rfl

private theorem fixedPair_mapIso_existsUnique
    {A : Type a} {B : Type b} [Category.{ha} A] [Category.{hb} B]
    {P : A ⥤ A} {Q : B ⥤ B}
    (J : Endofunctor.IsoAlgebra P ⥤ Endofunctor.IsoAlgebra Q)
    {K L : Endofunctor.IsoAlgebra P} (e : K ≅ L)
    {T : Type hb} (f : T) (hf : HEq (J.map e.hom).hom.f f) :
    ∃! e' : J.obj K ≅ J.obj L, HEq e'.hom.hom.f f := by
  refine ⟨J.mapIso e, hf, ?_⟩
  intro e' he'
  apply Iso.ext
  apply ObjectProperty.hom_ext
  apply Endofunctor.Algebra.Hom.ext
  exact eq_of_heq (he'.trans hf.symm)

namespace WeilConjectures

open CategoryTheory.Endofunctor

/-- A component of the counit projection mate, in product coordinates.
Source: def-exchange-projection, proper factor
(blueprint: fix-prop-projection-formula). -/
def compactProjectionProperMate {A : Type a} {B : Type b}
    [Category.{ha} A] [Category.{hb} B]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) {F : B ⥤ A} {G : A ⥤ B}
    (adj : F ⊣ G) (mu : ∀ M N : B,
      F.obj (TB.obj (M, N)) ≅ TA.obj (F.obj M, F.obj N)) (K : A) (L : B) :
    TB.obj (G.obj K, L) ⟶ G.obj (TA.obj (K, F.obj L)) :=
  adj.homEquiv _ _ ((mu (G.obj K) L).hom ≫
    TA.map (Prod.mkHom (adj.counit.app K) (𝟙 _)))

/-- The forward open projection mate; compact support uses its inverse.
Source: def-exchange-projection, open factor
(blueprint: fix-prop-projection-formula). -/
def compactProjectionOpenMate {A : Type a} {B : Type b}
    [Category.{ha} A] [Category.{hb} B]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) {J : A ⥤ B} {F : B ⥤ A}
    (adj : J ⊣ F) (mu : ∀ M N : B,
      F.obj (TB.obj (M, N)) ≅ TA.obj (F.obj M, F.obj N)) (K : A) (L : B) :
    J.obj (TA.obj (K, F.obj L)) ⟶ TB.obj (J.obj K, L) :=
  (adj.homEquiv _ _).symm
    (TA.map (Prod.mkHom (adj.unit.app K) (𝟙 _)) ≫ (mu (J.obj K) L).inv)

/-- Tensor of fixed pairs with the specified pullback/tensor comparison.
Source: step 13, tensor structure formula
(blueprint: fix-prop-projection-formula). -/
def compactProjectionTensorPair {A : Type a} [Category.{ha} A]
    (P : A ⥤ A) (T : A × A ⥤ A)
    (mu : ∀ M N : A, P.obj (T.obj (M, N)) ≅ T.obj (P.obj M, P.obj N))
    (K L : IsoAlgebra P) : IsoAlgebra P :=
  IsoAlgebra.mk (T.obj (K.carrier, L.carrier))
    (mu K.carrier L.carrier ≪≫ T.mapIso (K.str.prod L.str))

namespace CompactSupportWeilProjection
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The prescribed rational tensor on a geometric fibre, with inherited prime units.
Source: def-weil-derived-pullback-tensor-hom
(blueprint: fix-prop-projection-formula). -/
def tensor (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    sfRationalConstructibleCategory l E (D.geometricFiber T₀).left ×
      sfRationalConstructibleCategory l E (D.geometricFiber T₀).left ⥤
        sfRationalConstructibleCategory l E (D.geometricFiber T₀).left :=
  letI := sfWeilPrimeInvertible D l hl T₀
  rationalDerivedTensor l E (D.geometricFiber T₀).left

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical tensor/pullback comparison on the geometric morphism.
Source: completed quotient-tensor normalization
(blueprint: fix-prop-projection-formula). -/
def mu {U₀ T₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] (h₀ : U₀ ⟶ T₀)
    (K L : sfRationalConstructibleCategory l E (D.geometricFiber T₀).left) :
    (fieldWeilPull D l hl E h₀).obj ((tensor D l hl E T₀).obj (K, L)) ≅
      (tensor D l hl E U₀).obj
        ((fieldWeilPull D l hl E h₀).obj K, (fieldWeilPull D l hl E h₀).obj L) :=
  letI := sfWeilPrimeInvertible D l hl U₀
  letI := sfWeilPrimeInvertible D l hl T₀
  canonicalRationalPullbackTensor l E (zlFiberMap D h₀) K L

/-- Tensor on the actual framework Weil pairs, before the normalized PBC comparison.
Source: step 13, mu followed by tensor of the two Weil maps
(blueprint: fix-prop-projection-formula). -/
def tensorPair (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (K L : sfWeilComplex D l hl T₀ E) : sfWeilComplex D l hl T₀ E :=
  letI := sfWeilPrimeInvertible D l hl T₀
  compactProjectionTensorPair (sfWeilFrobeniusPullback D l hl T₀ E)
    (tensor D l hl E T₀)
    (canonicalRationalPullbackTensor l E (D.geometricFrobenius T₀).hom) K L
variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) (c₀ : Compactification f₀.left)

/-- The open mate for the retained model compactification.
Source: step 13, canonical open factor
(blueprint: fix-prop-projection-formula). -/
def openMate
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left)
    (L : sfRationalConstructibleCategory l E
      (D.geometricFiber (zlCompactificationMiddle D f₀ c₀)).left) :
    (fieldWeilOpen D l hl E (zlCompactificationOpen D f₀ c₀)).obj
        ((tensor D l hl E X₀).obj
          (K, (fieldWeilPull D l hl E (zlCompactificationOpen D f₀ c₀)).obj L)) ⟶
      (tensor D l hl E (zlCompactificationMiddle D f₀ c₀)).obj
        ((fieldWeilOpen D l hl E (zlCompactificationOpen D f₀ c₀)).obj K, L) :=
  compactProjectionOpenMate (tensor D l hl E X₀)
    (tensor D l hl E (zlCompactificationMiddle D f₀ c₀))
    (fieldWeilOpenAdj D l hl E (zlCompactificationOpen D f₀ c₀))
    (mu D l hl E (zlCompactificationOpen D f₀ c₀)) K L

/-- The inverse open factor is legitimate on every rational constructible pair.
Source: step 13 and open projection formula
(blueprint: fix-prop-projection-formula).
Proof: restrict the map along the open immersion. The adjunction unit is an
isomorphism and the displayed tensor comparison identifies the result with the
identity. On the complementary closed part both sides are zero. The open/closed
localization triangle detects its cone, proving that this particular mate is an
isomorphism. Rationalization preserves the same inverse. -/
theorem openMate_isIso
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left)
    (L : sfRationalConstructibleCategory l E
      (D.geometricFiber (zlCompactificationMiddle D f₀ c₀)).left) :
    IsIso (openMate D l hl E f₀ c₀ K L) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized factorization of inverse image along the compactification.
Source: pullback composition, with the actual factorization equality
(blueprint: fix-prop-projection-formula). -/
def pullFactor : fieldWeilPull D l hl E f₀ ≅
    fieldWeilPull D l hl E (zlCompactificationProper D f₀ c₀) ⋙
      fieldWeilPull D l hl E (zlCompactificationOpen D f₀ c₀) :=
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := sfWeilPrimeInvertible D l hl (zlCompactificationMiddle D f₀ c₀)
  eqToIso (congrArg (fun g ↦ rationalDerivedPullback l E g)
    (zlGeometricCompactification_comm D f₀ c₀)) ≪≫
    fieldRationalPullComp l E
      (zlFiberMap D (zlCompactificationOpen D f₀ c₀))
      (zlFiberMap D (zlCompactificationProper D f₀ c₀))

attribute [local irreducible] compactProjectionProperMate compactProjectionOpenMate
  mu pullFactor openMate fieldWeilProperAdj fieldWeilOpenAdj
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The exact proper-counit/open-inverse projection, in canonical adjoint coordinates.
Source: projection transformation, steps 13--14
(blueprint: fix-prop-projection-formula). -/
def component
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left)
    (L : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (tensor D l hl E Y₀).obj ((fieldWeilShriek D l hl E f₀ c₀).obj K, L) ⟶
      (fieldWeilShriek D l hl E f₀ c₀).obj
        ((tensor D l hl E X₀).obj (K, (fieldWeilPull D l hl E f₀).obj L)) :=
  letI : IsProper (zlCompactificationProper D f₀ c₀).left := c₀.isProper
  letI := openMate_isIso D l hl E f₀ c₀ K
    ((fieldWeilPull D l hl E (zlCompactificationProper D f₀ c₀)).obj L)
  compactProjectionProperMate
      (tensor D l hl E (zlCompactificationMiddle D f₀ c₀)) (tensor D l hl E Y₀)
      (fieldWeilProperAdj D l hl E (zlCompactificationProper D f₀ c₀))
      (mu D l hl E (zlCompactificationProper D f₀ c₀))
      ((fieldWeilOpen D l hl E (zlCompactificationOpen D f₀ c₀)).obj K) L ≫
    (fieldWeilProper D l hl E (zlCompactificationProper D f₀ c₀)).map
      (inv (openMate D l hl E f₀ c₀ K
        ((fieldWeilPull D l hl E (zlCompactificationProper D f₀ c₀)).obj L))) ≫
    (fieldWeilShriek D l hl E f₀ c₀).map
      ((tensor D l hl E X₀).map (Prod.mkHom (𝟙 _) ((pullFactor D l hl E f₀ c₀).inv.app L)))

/-- The prescribed compact-support functor on fixed pairs.
Source: Ex! followed by Rf!(theta)
(blueprint: fix-prop-projection-formula). -/
def supportPair : sfWeilComplex D l hl X₀ E ⥤ sfWeilComplex D l hl Y₀ E :=
  IsoAlgebra.mapOfNatIso (fieldWeilShriekExchange D l hl E f₀ c₀)

/-- The prescribed pullback functor on fixed pairs.
Source: inverse-image composition around the geometric Frobenius square
(blueprint: fix-prop-projection-formula). -/
def pullPair : sfWeilComplex D l hl Y₀ E ⥤ sfWeilComplex D l hl X₀ E :=
  IsoAlgebra.mapOfNatIso (fieldWeilPullSquare D l hl E f₀)

private theorem tensorPair_carrier (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (K L : sfWeilComplex D l hl T₀ E) :
    (tensorPair D l hl E T₀ K L).carrier =
      (tensor D l hl E T₀).obj (K.carrier, L.carrier) := rfl

omit [IsSeparated X₀.hom] [IsSeparated Y₀.hom] in
private theorem supportPair_carrier (K : sfWeilComplex D l hl X₀ E) :
    ((supportPair D l hl E f₀ c₀).obj K).carrier =
      (fieldWeilShriek D l hl E f₀ c₀).obj K.carrier := rfl

omit [IsSeparated X₀.hom] [IsSeparated Y₀.hom] in
private theorem pullPair_carrier (L : sfWeilComplex D l hl Y₀ E) :
    ((pullPair D l hl E f₀).obj L).carrier =
      (fieldWeilPull D l hl E f₀).obj L.carrier := rfl

/-- The canonical projection is an isomorphism of the prescribed fixed pairs.
No integral lift of either rational structure is required.
Source: projection-formula steps 13--15
(blueprint: fix-prop-projection-formula).
Proof: tensor, pullback and support have exactly their displayed Frobenius maps.
Transpose the proper projection square under the proper adjunction. The counit
mate identity and composition-compatible tensor comparison identify the two
transposes. The open unit calculation gives the same equation for the open mate
and hence its inverse. Pasting gives equivariance of component. Invertibility
follows from the rational projection formula, transported along the unique
proper/open adjoint comparisons and the recorded compact-support realization.
The inverse of an equivariant isomorphism is equivariant. The faithful forgetful
functor fixes both forward and inverse arrows uniquely. This calculation uses
the actual rational structure isomorphisms and their naturality, so clearing
localized denominators does not require an integral Weil lattice. -/
theorem restriction
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (K : sfWeilComplex D l hl X₀ E) (L : sfWeilComplex D l hl Y₀ E) :
    ∃! e : tensorPair D l hl E Y₀ ((supportPair D l hl E f₀ c₀).obj K) L ≅
        (supportPair D l hl E f₀ c₀).obj
          (tensorPair D l hl E X₀ K ((pullPair D l hl E f₀).obj L)),
      e.hom.hom.f = component D l hl E f₀ c₀ K.carrier L.carrier := by
  sorry

omit [FiniteDimensional (Padic l) E] in
/-- Transport the prescribed projection through any coefficient realization. -/
private theorem coefficient_forward
    [hfd : FiniteDimensional (Padic l) E]
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    {B : Type b} [Category.{hb} B] {Q : B ⥤ B}
    (G : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left ⥤ B)
    (J : sfWeilComplex D l hl Y₀ E ⥤ IsoAlgebra Q)
    (hJ : ∀ {M N : sfWeilComplex D l hl Y₀ E} (a : M ⟶ N),
      HEq (J.map a).hom.f (G.map a.hom.f))
    (K : sfWeilComplex D l hl X₀ E) (L : sfWeilComplex D l hl Y₀ E) :
    ∃! e : J.obj (tensorPair D l hl E Y₀ ((supportPair D l hl E f₀ c₀).obj K) L) ≅
        J.obj ((supportPair D l hl E f₀ c₀).obj
          (tensorPair D l hl E X₀ K ((pullPair D l hl E f₀).obj L))),
      HEq e.hom.hom.f (G.map (component D l hl E f₀ c₀ K.carrier L.carrier)) := by
  obtain ⟨e, he, _⟩ := restriction D l hl E f₀ c₀ K L
  have he' := hJ e.hom
  rw [he] at he'
  with_reducible
    apply fixedPair_mapIso_existsUnique J e
    simpa only [tensorPair_carrier, supportPair_carrier, pullPair_carrier] using he'

/-- The unique fixed-pair isomorphism with the specified projection as forward map.
Source: projection-formula Weil clause, steps 13--15
(blueprint: fix-prop-projection-formula). -/
def iso [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (K : sfWeilComplex D l hl X₀ E) (L : sfWeilComplex D l hl Y₀ E) :
    tensorPair D l hl E Y₀ ((supportPair D l hl E f₀ c₀).obj K) L ≅
      (supportPair D l hl E f₀ c₀).obj
        (tensorPair D l hl E X₀ K ((pullPair D l hl E f₀).obj L)) :=
  (restriction D l hl E f₀ c₀ K L).exists.choose

end CompactSupportWeilProjection

namespace CompactSupportPbcTransport
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (T₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
  (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completed Frobenius preserves the integral constructible domain.
Source: step 13, exact transport/completion comparison
(blueprint: fix-prop-projection-formula).
Proof: the actual completed pullback identifies with exact Frobenius transport by
pbcIsoCompletedPullback_identification. Exact transport preserves every integral
stratum, reduction and uniform bound. Invariance under that isomorphism gives the
stated membership, without identifying completion with ordinary transport. -/
theorem integral_mem (K : pbcIntegralStage C.l C.Qbar (D.geometricFiber T₀).left E₀) :
    PbcIsBoundedConstructibleComplete (D.geometricFiber T₀).left
      (pbcStageDatum.{u} C.l C.Qbar E₀)
      (completedPullbackObject (D.geometricFrobenius T₀).hom
        (pbcStageDatum.{u} C.l C.Qbar E₀) K.obj) := by
  have : IsIso (D.geometricFrobenius T₀).hom :=
    (D.geometricFrobenius T₀).isIso_hom
  have h := weilGeometricFiber_coefficientHypotheses D C T₀
  have : IsNoetherian (D.geometricFiber T₀).left := h.1
  have : Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber T₀).left ≤ n) := ⟨h.2.1⟩
  have : Fact (∀ t : (D.geometricFiber T₀).left,
      IsUnit (C.l : (D.geometricFiber T₀).left.presheaf.stalk t)) := ⟨h.2.2⟩
  exact ObjectProperty.prop_of_iso
    (PbcIsBoundedConstructibleComplete (D.geometricFiber T₀).left
      (pbcStageDatum.{u} C.l C.Qbar E₀))
    (pbcIsoCompletedPullback_identification (D.geometricFrobenius T₀).hom
      (pbcStageDatum.{u} C.l C.Qbar E₀) K).symm
    (pbcIsoAmbientPullback_preserves (D.geometricFrobenius T₀).hom
      (pbcStageDatum.{u} C.l C.Qbar E₀) K)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of the published normalized completion/transport comparison.
Source: step 13, canonical completion unit
(blueprint: fix-prop-projection-formula). -/
def integralBridge (K : pbcIntegralStage C.l C.Qbar (D.geometricFiber T₀).left E₀) :
    (⟨completedPullbackObject (D.geometricFrobenius T₀).hom
      (pbcStageDatum.{u} C.l C.Qbar E₀) K.obj,
        integral_mem D C T₀ E₀ K⟩ :
      pbcIntegralStage C.l C.Qbar (D.geometricFiber T₀).left E₀) ≅
    (pbcIsoIntegralPullback (D.geometricFrobenius T₀).hom
      (pbcStageDatum.{u} C.l C.Qbar E₀)).obj K :=
  ObjectProperty.isoMk _ (pbcIsoCompletedPullback_identification
    (D.geometricFrobenius T₀).hom (pbcStageDatum.{u} C.l C.Qbar E₀) K)
variable (F : FdCoefficientComparisonSystem.{u} C.l C.Qbar)
  (W : FdFrobeniusComparison C.l C.Qbar D C.different F T₀)

/-- Completed Frobenius in the comparison's original coefficient presentation.
Source: step 13, common-stage coefficient convention
(blueprint: fix-prop-projection-formula). -/
def completedFrobenius : pbcStageCategory C.l C.Qbar (D.geometricFiber T₀).left E₀ ⥤
    pbcStageCategory C.l C.Qbar (D.geometricFiber T₀).left E₀ :=
  letI := W.noetherian
  letI := W.dimension
  letI := W.invertible
  (pbcQbarPullFamily C.l C.Qbar (D.geometricFrobenius T₀).hom).Φ E₀

/-- The reflector-completed integral Frobenius functor.
Source: normalized completed pullback, projection-formula step 13
(blueprint: fix-prop-projection-formula). -/
def actualIntegralPull :=
  letI := W.noetherian
  letI := W.dimension
  letI := W.invertible
  pbcConditionalIntegral (pbcStageDatum.{u} C.l C.Qbar E₀)
    (pbcActualCompletedPull (D.geometricFrobenius T₀).hom
      (pbcStageDatum.{u} C.l C.Qbar E₀))
    (pbcQbarIntegralPull_mem C.l C.Qbar (D.geometricFrobenius T₀).hom E₀)

/-- The integral comparison starts at reflector completion: first undo the
strict-tower comparison and then use the strict completion/transport bridge.
Source: projection-formula step 13; Stacks 099N
(blueprint: fix-prop-projection-formula). -/
def actualIntegralBridge (K : pbcIntegralStage C.l C.Qbar (D.geometricFiber T₀).left E₀) :
    letI := (D.geometricFrobenius T₀).isIso_hom
    (actualIntegralPull D C T₀ E₀ F W).obj K ≅
      (pbcIsoIntegralPullback (D.geometricFrobenius T₀).hom
        (pbcStageDatum.{u} C.l C.Qbar E₀)).obj K :=
  letI := (D.geometricFrobenius T₀).isIso_hom
  ObjectProperty.isoMk _
    (((pbcActualCompletedPullback_tower (pbcStageDatum.{u} C.l C.Qbar E₀)
      (D.geometricFrobenius T₀).hom).exists.choose.app ⟨K.obj, K.property.1⟩).symm ≪≫
      (ObjectProperty.ι _).mapIso (integralBridge D C T₀ E₀ K))

private theorem actualIntegralBridge_unit
    (K : pbcIntegralStage C.l C.Qbar (D.geometricFiber T₀).left E₀) :
    letI := (D.geometricFrobenius T₀).isIso_hom
    (pbcActualCompletedPullUnit (D.geometricFrobenius T₀).hom
        (pbcStageDatum.{u} C.l C.Qbar E₀)).app K.obj ≫
      (actualIntegralBridge D C T₀ E₀ F W K).hom.hom =
    (pbcIsoOrdinaryDerivedComparison (D.geometricFrobenius T₀).hom
      (pbcStageDatum.{u} C.l C.Qbar E₀)).hom.app K.obj := by
  have : IsIso (D.geometricFrobenius T₀).hom := (D.geometricFrobenius T₀).isIso_hom
  let t := (pbcActualCompletedPullback_tower (pbcStageDatum.{u} C.l C.Qbar E₀)
    (D.geometricFrobenius T₀).hom).exists.choose
  let M : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete (D.geometricFiber T₀).left
        (pbcStageDatum.{u} C.l C.Qbar E₀)) := ⟨K.obj, K.property.1⟩
  have ht := (pbcActualCompletedPullback_tower (pbcStageDatum.{u} C.l C.Qbar E₀)
    (D.geometricFrobenius T₀).hom).exists.choose_spec M
  change _ ≫ (t.inv.app M ≫
      (pbcIsoCompletedPullback_identification (D.geometricFrobenius T₀).hom
        (pbcStageDatum.{u} C.l C.Qbar E₀) K).hom) = _
  calc
    _ = ((pbcActualStrictCompletedPullUnit (pbcStageDatum.{u} C.l C.Qbar E₀)
          (D.geometricFrobenius T₀).hom).app K.obj ≫ t.hom.app M) ≫
        (t.inv.app M ≫
          (pbcIsoCompletedPullback_identification (D.geometricFrobenius T₀).hom
            (pbcStageDatum.{u} C.l C.Qbar E₀) K).hom) :=
      congrArg (fun f ↦ f ≫ _) ht.symm
    _ = (pbcActualStrictCompletedPullUnit (pbcStageDatum.{u} C.l C.Qbar E₀)
          (D.geometricFrobenius T₀).hom).app K.obj ≫
        (pbcIsoCompletedPullback_identification (D.geometricFrobenius T₀).hom
          (pbcStageDatum.{u} C.l C.Qbar E₀) K).hom := by
      exact iso_cancel_middle (t.app M) _ _
    _ = _ := by
      have hs : (pbcActualStrictCompletedPullUnit (pbcStageDatum.{u} C.l C.Qbar E₀)
          (D.geometricFrobenius T₀).hom).app K.obj =
          completedPullbackComparison (D.geometricFrobenius T₀).hom
            (pbcStageDatum.{u} C.l C.Qbar E₀) K.obj := by
        exact unit_whisker_app
          (pbcActualDerivedPull (D.geometricFrobenius T₀).hom
            (pbcStageDatum.{u} C.l C.Qbar E₀))
          (completedDerivedConstant (pbcStageDatum.{u} C.l C.Qbar E₀)
            (D.geometricFiber T₀).left)
          (completedTowerRlim (pbcStageDatum.{u} C.l C.Qbar E₀)
            (D.geometricFiber T₀).left)
          (completedTowerPullback (D.geometricFrobenius T₀).hom
            (pbcStageDatum.{u} C.l C.Qbar E₀))
          (completedConstantRlimUnit (pbcStageDatum.{u} C.l C.Qbar E₀)
            (D.geometricFiber T₀).left)
          (completedPullbackConstantIso (D.geometricFrobenius T₀).hom
            (pbcStageDatum.{u} C.l C.Qbar E₀)).hom
          (completedReductionTowerUnit (pbcStageDatum.{u} C.l C.Qbar E₀)
            (D.geometricFiber T₀).left) K.obj
      exact (congrArg (fun f ↦ f ≫ _) hs).trans
        ((asIso (completedPullbackComparison (D.geometricFrobenius T₀).hom
          (pbcStageDatum.{u} C.l C.Qbar E₀) K.obj)).hom_inv_id_assoc _)

private theorem actualIntegralBridge_naturality
    {K L : pbcIntegralStage C.l C.Qbar (D.geometricFiber T₀).left E₀} (f : K ⟶ L) :
    letI := (D.geometricFrobenius T₀).isIso_hom
    (actualIntegralPull D C T₀ E₀ F W).map f ≫
        (actualIntegralBridge D C T₀ E₀ F W L).hom =
      (actualIntegralBridge D C T₀ E₀ F W K).hom ≫
        (pbcIsoIntegralPullback (D.geometricFrobenius T₀).hom
          (pbcStageDatum.{u} C.l C.Qbar E₀)).map f := by
  have := (D.geometricFrobenius T₀).isIso_hom
  apply ObjectProperty.hom_ext
  exact inverseUnit_naturality
    (Functor.whiskerLeft (ObjectProperty.ι _)
      (pbcActualCompletedPullUnit (D.geometricFrobenius T₀).hom
        (pbcStageDatum.{u} C.l C.Qbar E₀)))
    (Functor.isoWhiskerLeft (ObjectProperty.ι _)
      (pbcIsoOrdinaryDerivedComparison (D.geometricFrobenius T₀).hom
        (pbcStageDatum.{u} C.l C.Qbar E₀)))
    (fun M ↦ (ObjectProperty.ι _).mapIso (actualIntegralBridge D C T₀ E₀ F W M))
    (actualIntegralBridge_unit D C T₀ E₀ F W) f

attribute [local irreducible] ScalarLocalization.map ScalarLocalization.transport in
/-- The exact Weil convention and the reflector-completed convention are related
by the localization of the actual completion/transport comparison.
Source: projection-formula step 13 (blueprint: fix-prop-projection-formula).
Proof: insert the inverse strict-tower comparison before integralBridge. Its
composite with the reflector unit is the exact-transport comparison, by the
unit normalization of pbcActualCompletedPullback_tower. Naturality follows by
cancelling this invertible unit and using the naturality of exact transport.
Localize this integral natural isomorphism. Fully faithful precomposition with
raw localization extends it uniquely. Every rational object retains an integral
representative, so its component prescription also proves uniqueness. -/
theorem bridge_existsUnique :
    ∃! b : completedFrobenius D C T₀ E₀ F W ≅ weilFrobeniusPullback D C T₀ E₀,
      ∀ K : pbcIntegralStage C.l C.Qbar (D.geometricFiber T₀).left E₀,
        HEq (b.hom.app ((pbcStageLocalization C.l C.Qbar
          (D.geometricFiber T₀).left E₀).obj K))
          (fdRawTensor (pbcStageUniformizer.{u} C.l C.Qbar E₀) 1
            (actualIntegralBridge D C T₀ E₀ F W K).hom) := by
  have := (D.geometricFrobenius T₀).isIso_hom
  have := W.noetherian
  have := W.dimension
  have := W.invertible
  let I := actualIntegralPull D C T₀ E₀ F W
  let J := pbcIsoIntegralPullback (D.geometricFrobenius T₀).hom
    (pbcStageDatum.{u} C.l C.Qbar E₀)
  have : I.Additive := by
    dsimp only [I, actualIntegralPull]
    infer_instance
  have : I.Linear (PbcIntegralRing C.l (pbcFiniteField C.l C.Qbar E₀)) := by
    dsimp only [I, actualIntegralPull]
    infer_instance
  let e : I ≅ J := NatIso.ofComponents
    (actualIntegralBridge D C T₀ E₀ F W)
    (fun f ↦ actualIntegralBridge_naturality D C T₀ E₀ F W f)
  have hf : completedFrobenius D C T₀ E₀ F W =
      pbcDescentPullback C.l C.Qbar (D.geometricFrobenius T₀).hom
        (pbcQbarIntegralPull_mem C.l C.Qbar (D.geometricFrobenius T₀).hom) E₀ :=
    (pbcQbarPullFamily_existsUnique C.l C.Qbar
      (D.geometricFrobenius T₀).hom).exists.choose_spec.1 E₀
  rw [hf]
  obtain ⟨b, hb, _⟩ := localizedTransportIso_existsUnique _ _
    (pbcStageUniformizer.{u} C.l C.Qbar E₀) I J e
  have hn : ∀ K : pbcIntegralStage C.l C.Qbar (D.geometricFiber T₀).left E₀,
      HEq (b.hom.app ((pbcStageLocalization C.l C.Qbar
        (D.geometricFiber T₀).left E₀).obj K))
        (fdRawTensor (pbcStageUniformizer.{u} C.l C.Qbar E₀) 1
          (actualIntegralBridge D C T₀ E₀ F W K).hom) := by
    intro K
    exact (hb K).trans (by rfl)
  refine ⟨b, hn, ?_⟩
  intro b' hb'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  rcases K with ⟨K⟩
  exact eq_of_heq ((hb' K).trans (hn K).symm)

/-- The uniquely normalized bridge, retaining the completion comparison.
Source: step 13 (blueprint: fix-prop-projection-formula). -/
def bridge : completedFrobenius D C T₀ E₀ F W ≅ weilFrobeniusPullback D C T₀ E₀ :=
  (bridge_existsUnique D C T₀ E₀ F W).exists.choose

/-- Convert completed fixed pairs to the exact WeilD convention. Carriers and
arrows are unchanged; only the prescribed structure comparison is inserted.
Source: step 13 (blueprint: fix-prop-projection-formula). -/
def toExact : IsoAlgebra (completedFrobenius D C T₀ E₀ F W) ⥤ WeilD D C T₀ E₀ :=
  IsoAlgebra.mapOfNatIso
    ((weilFrobeniusPullback D C T₀ E₀).leftUnitor ≪≫
      (bridge D C T₀ E₀ F W).symm ≪≫
        (completedFrobenius D C T₀ E₀ F W).rightUnitor.symm)

/-- Inverse transport of fixed pairs along the same bridge.
Source: step 13 (blueprint: fix-prop-projection-formula). -/
def fromExact : WeilD D C T₀ E₀ ⥤ IsoAlgebra (completedFrobenius D C T₀ E₀ F W) :=
  IsoAlgebra.mapOfNatIso
    ((completedFrobenius D C T₀ E₀ F W).leftUnitor ≪≫
      bridge D C T₀ E₀ F W ≪≫ (weilFrobeniusPullback D C T₀ E₀).rightUnitor.symm)

/-- The named rational coefficient comparison with its inherited geometric facts.
Source: step 13 (blueprint: fix-prop-projection-formula). -/
def realization : sfRationalConstructibleCategory C.l
    (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left ⥤
      pbcStageCategory C.l C.Qbar (D.geometricFiber T₀).left E₀ :=
  CompactSupportCoefficientTensor.rational D C T₀ E₀ F W

/-- The coefficient realization followed by the normalized exact-pair bridge.
Source: step 13 (blueprint: fix-prop-projection-formula). -/
def pairRealization : sfWeilComplex D C.l C.different T₀
    (pbcFiniteField C.l C.Qbar E₀) ⥤ WeilD D C T₀ E₀ :=
  (W.finite E₀).functor ⋙ toExact D C T₀ E₀ F W

/-- The inverse coefficient realization after undoing the exact-pair bridge.
Source: step 13 (blueprint: fix-prop-projection-formula). -/
def pairInverse : WeilD D C T₀ E₀ ⥤ sfWeilComplex D C.l C.different T₀
    (pbcFiniteField C.l C.Qbar E₀) :=
  fromExact D C T₀ E₀ F W ⋙ (W.finite E₀).inverse

/-- Coefficient realization transports underlying arrows by its recorded functor. -/
private theorem pairRealization_map_heq
    {M N : sfWeilComplex D C.l C.different T₀ (pbcFiniteField C.l C.Qbar E₀)}
    (a : M ⟶ N) :
    HEq ((pairRealization D C T₀ E₀ F W).map a).hom.f
      ((realization D C T₀ E₀ F W).map a.hom.f) := by
  have := W.noetherian
  have := W.dimension
  have := W.invertible
  exact fixedPair_map_heq (W.finite E₀).functor
    ((F.pullback (D.geometricFrobenius T₀)).finite E₀).rational
    (eq_of_heq (W.finite_functors E₀)) a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The raw coefficient realization of the inverse Weil presentation cancels
by the actual finite equivalence counit; exact/completed transport leaves its
carrier unchanged.
Source: step 13 (blueprint: fix-prop-projection-formula).
Proof: use finite_functors to identify the underlying functor of W.finite with
the recorded rational realization. Apply its counit at fromExact K. Inserting
toExact cancels the same bridge with its inverse, without changing carriers.
This fixes the raw counit arrow, and forgetting Weil structures is faithful. -/
theorem cancellation_existsUnique (K : WeilD D C T₀ E₀) :
    ∃! e : (realization D C T₀ E₀ F W).obj
        ((pairInverse D C T₀ E₀ F W).obj K).carrier ≅ K.carrier,
      HEq e.hom
        (((W.finite E₀).counitIso.hom.app ((fromExact D C T₀ E₀ F W).obj K)).hom.f) := by
  have := W.noetherian
  have := W.dimension
  have := W.invertible
  let U := ((W.finite E₀).inverse).obj ((fromExact D C T₀ E₀ F W).obj K)
  let e := (IsoAlgebra.forget (completedFrobenius D C T₀ E₀ F W)).mapIso
    ((W.finite E₀).counitIso.app ((fromExact D C T₀ E₀ F W).obj K))
  have ho : ((W.finite E₀).functor.obj U).carrier =
      (realization D C T₀ E₀ F W).obj U.carrier :=
    fixedPair_obj_carrier (W.finite E₀).functor
      ((F.pullback (D.geometricFrobenius T₀)).finite E₀).rational
      (eq_of_heq (W.finite_functors E₀)) U
  let e' := eqToIso ho.symm ≪≫ e
  have he : HEq e'.hom e.hom := eqToHom_comp_heq e.hom ho.symm
  refine ⟨e', he, ?_⟩
  intro e'' he''
  apply Iso.ext
  exact eq_of_heq (he''.trans he.symm)

/-- The raw finite-counit cancellation with its fixed underlying arrow.
Source: step 13 (blueprint: fix-prop-projection-formula). -/
def cancellation (K : WeilD D C T₀ E₀) :
    (realization D C T₀ E₀ F W).obj
      ((pairInverse D C T₀ E₀ F W).obj K).carrier ≅ K.carrier :=
  (cancellation_existsUnique D C T₀ E₀ F W K).exists.choose

end CompactSupportPbcTransport

namespace CompactSupportPbcProjection
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (F : FdCoefficientComparisonSystem.{u} C.l C.Qbar)
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (WX : FdFrobeniusComparison C.l C.Qbar D C.different F X₀)
  (WY : FdFrobeniusComparison C.l C.Qbar D C.different F Y₀)
  (f₀ : X₀ ⟶ Y₀) (c₀ : Compactification f₀.left)
  (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)

/-- Source of projection in the actual WeilD category under the normalized coefficient
comparison. The two input Weil isomorphisms are entirely arbitrary rational arrows.
Source: step 13, coefficient-category comparison
(blueprint: fix-prop-projection-formula). -/
def source (K : WeilD D C X₀ E₀) (L : WeilD D C Y₀ E₀) : WeilD D C Y₀ E₀ :=
  (CompactSupportPbcTransport.pairRealization D C Y₀ E₀ F WY).obj
    (CompactSupportWeilProjection.tensorPair D C.l C.different
      (pbcFiniteField C.l C.Qbar E₀) Y₀
      ((CompactSupportWeilProjection.supportPair D C.l C.different
        (pbcFiniteField C.l C.Qbar E₀) f₀ c₀).obj
        ((CompactSupportPbcTransport.pairInverse D C X₀ E₀ F WX).obj K))
      ((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj L))

/-- Target of projection in actual WeilD, using the canonical support and pullback
Frobenius exchanges, and the same tensor comparison as at the source.
Source: step 13, coefficient-category comparison
(blueprint: fix-prop-projection-formula). -/
def target (K : WeilD D C X₀ E₀) (L : WeilD D C Y₀ E₀) : WeilD D C Y₀ E₀ :=
  (CompactSupportPbcTransport.pairRealization D C Y₀ E₀ F WY).obj
    ((CompactSupportWeilProjection.supportPair D C.l C.different
      (pbcFiniteField C.l C.Qbar E₀) f₀ c₀).obj
      (CompactSupportWeilProjection.tensorPair D C.l C.different
        (pbcFiniteField C.l C.Qbar E₀) X₀
        ((CompactSupportPbcTransport.pairInverse D C X₀ E₀ F WX).obj K)
        ((CompactSupportWeilProjection.pullPair D C.l C.different
          (pbcFiniteField C.l C.Qbar E₀) f₀).obj
          ((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj L))))

private theorem forward_on_presentations
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (U : sfWeilComplex D C.l C.different X₀ (pbcFiniteField C.l C.Qbar E₀))
    (V : sfWeilComplex D C.l C.different Y₀ (pbcFiniteField C.l C.Qbar E₀)) :
    ∃! e :
      (CompactSupportPbcTransport.pairRealization D C Y₀ E₀ F WY).obj
        (CompactSupportWeilProjection.tensorPair D C.l C.different
          (pbcFiniteField C.l C.Qbar E₀) Y₀
          ((CompactSupportWeilProjection.supportPair D C.l C.different
            (pbcFiniteField C.l C.Qbar E₀) f₀ c₀).obj
            U)
          V)
      ≅
      (CompactSupportPbcTransport.pairRealization D C Y₀ E₀ F WY).obj
        ((CompactSupportWeilProjection.supportPair D C.l C.different
          (pbcFiniteField C.l C.Qbar E₀) f₀ c₀).obj
          (CompactSupportWeilProjection.tensorPair D C.l C.different
            (pbcFiniteField C.l C.Qbar E₀) X₀
            U
            ((CompactSupportWeilProjection.pullPair D C.l C.different
              (pbcFiniteField C.l C.Qbar E₀) f₀).obj
              V))),
      HEq e.hom.hom.f
        ((CompactSupportPbcTransport.realization D C Y₀ E₀ F WY).map
          (CompactSupportWeilProjection.component D C.l C.different
            (pbcFiniteField C.l C.Qbar E₀) f₀ c₀ U.carrier V.carrier)) := by
  with_reducible
    exact CompactSupportWeilProjection.coefficient_forward D C.l C.different
      (pbcFiniteField C.l C.Qbar E₀) f₀ c₀
      (B := PbcRationalCategory (D.geometricFiber Y₀).left
        (pbcStageDatum.{u} C.l C.Qbar E₀) (pbcStageUniformizer.{u} C.l C.Qbar E₀))
      (Q := weilFrobeniusPullback D C Y₀ E₀)
      (CompactSupportPbcTransport.realization D C Y₀ E₀ F WY)
      (CompactSupportPbcTransport.pairRealization D C Y₀ E₀ F WY)
      (CompactSupportPbcTransport.pairRealization_map_heq D C Y₀ E₀ F WY) U V

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- There is a unique Weil isomorphism whose forward arrow is the normalized
coefficient image of the proper/open
projection, not a replacement isomorphism. The fixed-pair comparison acts on underlying
arrows by the recorded raw-localization comparison.
Source: steps 13--15 (blueprint: fix-prop-projection-formula).
Proof: the unique defining equation for the framework iso identifies its forward
arrow with component. Apply the coefficient functor. The finite_functors equation
in the Frobenius comparison identifies this with the underlying fixed-pair map.
The objects and localized tensors of FdRationalStageComparison retain the same
integral representatives and all rational denominators, giving precisely HEq. -/
theorem forward [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (K : WeilD D C X₀ E₀) (L : WeilD D C Y₀ E₀) :
    ∃! e : source D C F WX WY f₀ c₀ E₀ K L ≅ target D C F WX WY f₀ c₀ E₀ K L,
      HEq e.hom.hom.f
      ((CompactSupportPbcTransport.realization D C Y₀ E₀ F WY).map
        (CompactSupportWeilProjection.component D C.l C.different
          (pbcFiniteField C.l C.Qbar E₀) f₀ c₀
          ((CompactSupportPbcTransport.pairInverse D C X₀ E₀ F WX).obj K).carrier
          ((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj L).carrier)) := by
  delta source target
  have hh := forward_on_presentations D C F WY f₀ c₀ E₀
    ((CompactSupportPbcTransport.pairInverse D C X₀ E₀ F WX).obj K)
    ((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj L)
  -- The presentations use different proofs of finite-dimensionality. Rewrite these
  -- proof arguments explicitly: conversion otherwise unfolds the large category models.
  -- Extracting them from the types avoids referring to generated auxiliary names.
  run_tac Lean.Elab.Tactic.withMainContext do
    let expected ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let actual ← Lean.instantiateMVars
      (← Lean.Meta.inferType (← Lean.Meta.getLocalDeclFromUserName `hh).toExpr)
    let mut pending := [(actual, expected)]
    let mut alignment : Option (Lean.Expr × Lean.Expr) := none
    for _ in [:20000] do
      if alignment.isNone then
        match pending with
        | [] => pure ()
        | (x, y) :: rest =>
          pending := rest
          let x := x.consumeMData
          let y := y.consumeMData
          if x != y then
            let proof : Bool ← if x.hasLooseBVars || y.hasLooseBVars then pure false
              else if (← Lean.Meta.isProof x) then Lean.Meta.isProof y else pure false
            if proof then
              alignment := some (x, y)
            else
              match x, y with
              | .app f a, .app g b => pending := (f, g) :: (a, b) :: pending
              | .lam _ t b _, .lam _ u c _
              | .forallE _ t b _, .forallE _ u c _ =>
                pending := (t, u) :: (b, c) :: pending
              | .proj n i a, .proj m j b =>
                if n == m && i == j then pending := (a, b) :: pending
              | _, _ => pure ()
    let some (p, q) := alignment | throwError "no coefficient proof argument to align"
    let hp ← Lean.Meta.mkAppM ``Subsingleton.elim #[p, q]
    let goal ← Lean.Elab.Tactic.getMainGoal
    let (_, goal) ← (← goal.assert `coefficient_alignment (← Lean.Meta.inferType hp) hp).intro1P
    Lean.Elab.Tactic.replaceMainGoal [goal]
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| erw [$(Lean.mkIdent `coefficient_alignment):term] at $(Lean.mkIdent `hh):ident))
  with_reducible exact hh

/-- The canonical projection isomorphism on actual WeilD. Its underlying arrow
is fixed uniquely by forward, so this definition selects no arbitrary map.
Source: steps 13--15 (blueprint: fix-prop-projection-formula). -/
def iso [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (K : WeilD D C X₀ E₀) (L : WeilD D C Y₀ E₀) :
    source D C F WX WY f₀ c₀ E₀ K L ≅ target D C F WX WY f₀ c₀ E₀ K L :=
  (forward D C F WX WY f₀ c₀ E₀ K L).exists.choose

attribute [local irreducible] CompactSupportCoefficientTensor.comparison
  CompactSupportPbcTransport.cancellation
/-- Inclusion of the canonical finite-stage projection in the actual common-stage
WeilDQbar category. All choices of a common finite field are allowed, including an
identity extension; the input objects retain their actual Weil maps.
Source: step 14, common-stage prescription
(blueprint: fix-prop-projection-formula). -/
def commonIso [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (K : WeilDQbar D C X₀) (L : WeilDQbar D C Y₀)
    (hK : K.stage ≤ E₀) (hL : L.stage ≤ E₀) :
    ((weilScalarSystem D C Y₀).ι E₀).obj
        (source D C F WX WY f₀ c₀ E₀
          (((weilScalarSystem D C X₀).T hK).obj K.obj)
          (((weilScalarSystem D C Y₀).T hL).obj L.obj)) ≅
      ((weilScalarSystem D C Y₀).ι E₀).obj
        (target D C F WX WY f₀ c₀ E₀
          (((weilScalarSystem D C X₀).T hK).obj K.obj)
          (((weilScalarSystem D C Y₀).T hL).obj L.obj)) :=
  ((weilScalarSystem D C Y₀).ι E₀).mapIso
    (iso D C F WX WY f₀ c₀ E₀
      (((weilScalarSystem D C X₀).T hK).obj K.obj)
      (((weilScalarSystem D C Y₀).T hL).obj L.obj))

end CompactSupportPbcProjection
end WeilConjectures

namespace WeilConjectures

end WeilConjectures
