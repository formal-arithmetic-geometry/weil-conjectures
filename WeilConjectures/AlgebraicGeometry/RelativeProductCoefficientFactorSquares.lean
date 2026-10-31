/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProductFactors
import WeilConjectures.AlgebraicGeometry.RelativeProductFactorSquaresCore
import WeilConjectures.AlgebraicGeometry.RelativeProductProperCompatibilityCore

/-! # Coefficient and proper squares of the six relative-product factors

Source: current blueprint relative-product display and A5
(blueprint: lem-sf-relative-product-coefficient-factor-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

private theorem properCoordinates_of_directDomain
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {O : SixFunctorPushStage D B} {P : ∀ X, ObjectProperty (B X)}
    {T : ∀ X, B X ⥤ (P X).FullSubcategory ⥤ B X}
    (R : RelativeProductCoordinates O P T)
    (h : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y),
      IsProper f.hom.left → ∀ K : (P X).FullSubcategory, P Y ((O.direct f).obj K.obj)) :
    Nonempty (RelativeProductProperCoordinates R) := by
  let F {X Y : SixFunctorSpace D} (f : X ⟶ Y) (hf : IsProper f.hom.left) :=
    (P Y).lift ((P X).ι ⋙ O.direct f) (h f hf)
  let e {X Y : SixFunctorSpace D} (f : X ⟶ Y)
      (hf : IsProper f.hom.left) (c : Compactification f.hom.left) :
      R.operations.support f c ⋙ (P Y).ι ≅ F f hf ⋙ (P Y).ι :=
    eqToIso (R.supportNormalization f c) ≪≫
      Functor.isoWhiskerLeft (P X).ι
        (@SixFunctorPushStage.properIdentification _ _ _ O _ _ f hf c)
  refine ⟨{
    direct := @F
    direct_eq := fun _ _ ↦ rfl
    identification := fun f hf c ↦ Functor.fullyFaithfulCancelRight (P _).ι (e f hf c)
    identification_eq := ?_ }⟩
  intro X Y f hf c K
  simp only [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  dsimp [e]
  simp only [eqToHom_app]
  exact eqToHom_comp_heq _ _

/-- Every coefficient stage has the normalized finite-Tor presentation of the six
specified factors. This is existence of the restriction of fixed operations, not
an axiom assuming the six factor squares.
Source: the finite-Tor domains and naturality paragraph
(blueprint: lem-sf-relative-product-coefficient-factor-squares).

Proof: restrict pullback and compact support by the preservation fields of A1--A4.
Full inclusion lifts their maps and the composition comparison uniquely. The
closed tensor-Hom adjunction identifies its tensor with the actual partial tensor.
Lift the signed symmetry through this comparison. Restrict the supplied projection
and exchange transformations, and use A2 and A3 for their inverse components.
Their naturality and the naturality of inverses give the six natural isomorphisms.
No choice of an unrelated transformation is involved. -/
theorem relative_product_presentation_exists
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn) (s : PodCoefficientStage)
    (Q : SixFunctorCompactifiedSquare D) [IsSeparated Q.Y.obj.hom]
    [IsSeparated Q.f.hom.left] [IsSeparated Q.g.hom.left]
    [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left] :
    Nonempty (RelativeProductPresentation S s Q) := by
  sorry

/-- Proper direct images and the specified rho restrict to the same finite-Tor
coordinates. Their normalization is fixed by full inclusion, not a choice of rho.
Source: proper-replacement paragraph, proof step 6
(blueprint: lem-sf-relative-product-coefficient-factor-squares).

Proof: proper maps are separated. Restrict the datum's direct functors using A1
finite-Tor preservation. The comparison through the identity-open compactification
has both endpoints in the full domain, so lift it and its inverse through the full
inclusion. Its inverse identities and naturality are inherited by faithfulness.
This gives precisely the prescribed proper identification at every occurrence. -/
theorem relative_product_proper_coordinates_exists
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
    {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    (R : RelativeProductPresentation S s Q) :
    Nonempty (RelativeProductProperCoordinates R.coordinates) := by
  apply properCoordinates_of_directDomain R.coordinates
  intro X Y f hf K
  have : IsSeparated f.hom.left := inferInstance
  cases s with
  | finite => exact S.finiteCoherence.directDomain f K.obj K.property
  | integral => exact S.integralCoherence.directDomain f K.obj K.property
  | rational => trivial
  | common => trivial

/-- Each individual coefficient square commutes. The inputs to this theorem are
the datum and an admissible coefficient comparison, including its primitive A5
data. No square for an inverse factor or a relative-product composite is assumed.
The recursively assembled c_i compare exactly the displayed seven objects.
Source: the factor-square equation and proof steps 1--5
(blueprint: lem-sf-relative-product-coefficient-factor-squares).

Proof: restrict the fixed operations by their finite-Tor preservation, and lift the
specified transformations through full inclusion. The tensor-Hom comparisons and
fixed coefficient models give the signed tensor comparisons. Restrict the primitive
A5 comparisons of the given reduction, localization or scalar extension. The input
A is their full-subcategory restriction by RecordedComparison and its normalization
fields; hence the recursively constructed c_i use those fixed maps.
The composition square is A5 for A4. For an invertible transformation,
its comparison square implies the inverse square by multiplying by the two
inverses and using that a functor maps an inverse to the inverse. Apply this
calculation to the two projection maps and the exchange. Whisker the first
projection and the exchange by Rg_!, using naturality of its coefficient comparison.
Tensor functoriality inserts the identity of L. For the two symmetries use A5's
signed tensor equation: on homogeneous degrees r,s both routes carry (-1)^(r*s).
The same equations hold for completed tensor, rationalization and common-stage
inclusion, since those comparisons retain the defining tensor maps. These six
calculations give the indexed equation separately, without merely comparing the
composite relative-product morphisms.
For proper replacements insert rho recursively to obtain j_i. Naturality of tensor
and support gives each normalized factor j_i⁻¹ d_i j_(i+1). Projection coherence
identifies the proper projection with its direct-image counit mate. If f is proper,
base-change stability makes v proper. In the identity-open compactification the
compact exchange is direct exchange followed by open base change; the identity-open
unit cancels that open map. Naturality of direct exchange therefore gives precisely
the direct-image mate after rho_f and rho_v. This also retains the finite identity-open
normalization. A5's proper-identity square identifies the conjugated c_i with the
same direct-image coefficient comparison. Substitute these conjugates into the six
already proved squares and cancel j_i and their inverses. This proves all proper
factor squares, for any selected proper structural morphisms, including only h. -/
theorem relative_product_coefficient_factor_squares
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E E' : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] [Field E'] [Algebra (Padic C.l) E']
    [FiniteDimensional (Padic C.l) E'] {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}
    {S : SixFunctorDatum D C E n hn} {S' : SixFunctorDatum D C E' n' hn'}
    {s s' : PodCoefficientStage} {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.Y.obj.hom] [IsSeparated Q.f.hom.left]
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    (R : RelativeProductPresentation S s Q) (R' : RelativeProductPresentation S' s' Q)
    (A : RelativeProductCoefficientData R R')
    (_admissible : A.RecordedComparison)
    (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left) :
    A.FactorSquares cg ch ∧
    (∀ (i : Fin 6) K K' L L' (a : K ⟶ K') (b : L ⟶ L'),
      ((relativeProductTerms Q cg ch i.castSucc).eval
          R.coordinates.operations R.coordinates.tensor).map (Prod.mkHom a b) ≫
        (R.factors cg ch i).hom.app (K', L') =
      (R.factors cg ch i).hom.app (K, L) ≫
        ((relativeProductTerms Q cg ch i.succ).eval
          R.coordinates.operations R.coordinates.tensor).map (Prod.mkHom a b)) ∧
    Nonempty (RelativeProductProperCoordinates R.coordinates) ∧
    Nonempty (RelativeProductProperCoordinates R'.coordinates) ∧
    (∀ (J : RelativeProductProperCoordinates R.coordinates)
      (J' : RelativeProductProperCoordinates R'.coordinates),
      R.ProperNormalization J ∧ R'.ProperNormalization J' ∧
        A.ProperComparisonNormalization J J' ∧ A.ProperFactorSquares J J' cg ch) := by
  refine ⟨relative_product_factor_squares_core A cg ch, ?_,
    relative_product_proper_coordinates_exists R,
    relative_product_proper_coordinates_exists R', ?_⟩
  · intro i K K' L L' a b
    exact (R.factors cg ch i).hom.naturality (Prod.mkHom a b)
  · exact relative_product_proper_compatibility_core A cg ch

end WeilConjectures
