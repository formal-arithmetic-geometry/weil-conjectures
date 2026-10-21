/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Restriction transport at a geometric point

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151; the explicit
pro-etale restriction and completed-coefficient argument is agent-written
(blueprint: lem-weil-point-automorphism-restriction-natural).

The inverse image is expressed in the canonical sectionwise coordinates of
`isoSectionwiseInverseImage`. Its distinguished coprojection is the identity in
these coordinates. `none` denotes integral coefficients and `some n` denotes
finite coefficients at positive exponent `n + 1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The two allowed scalar rings, lifted only to accommodate the site universe.
Source: Deligne (1.1.3); the coefficient convention of the node
(blueprint: lem-weil-point-automorphism-restriction-natural). -/
def pointRestrictionScalars (a : Option ℕ) : RingCat.{max u (t + 1)} :=
  match a with
  | none => RingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
  | some n => RingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))

/-- The recorded finite constant or completed integral coefficient sheaf.
Source: completed coefficient convention, Stacks Tag 03CO
(blueprint: lem-weil-point-automorphism-restriction-natural). -/
def pointRestrictionRing (S : AlgebraicGeometry.Scheme.{t}) (a : Option ℕ) :
    Sheaf (ProEt.topology S) RingCat.{max u (t + 1)} :=
  match a with
  | none => completedIntegralCoefficientSheafUnrestricted l E S
  | some n => integralCoefficientSheaf l E S n

/-- The prescribed structure isomorphism, not an arbitrary coefficient map.
Source: Stacks Tags 0H7J and 03CO
(blueprint: lem-weil-point-automorphism-restriction-natural). -/
def pointRestrictionCoefficientMap {S : AlgebraicGeometry.Scheme.{t}}
    (g : S ⟶ S) [IsIso g] (a : Option ℕ) :
    (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).obj
      (pointRestrictionRing l E S a) ⟶ pointRestrictionRing l E S a :=
  match a with
  | none => inverseImageCompletedCoefficientMap l E g
  | some n => inverseImageFiniteCoefficientMap l E g n

/-- Invertibility inherited from the finite/completed coefficient constructions.
Source: Stacks Tags 09A5 and 03CO
(blueprint: lem-weil-point-automorphism-restriction-natural). -/
instance pointRestrictionCoefficientMapIsIso {S : AlgebraicGeometry.Scheme.{t}}
    (g : S ⟶ S) [IsIso g] (a : Option ℕ) :
    IsIso (pointRestrictionCoefficientMap l E g a) :=
  match a with
  | none => inverseImageCompletedCoefficientMap_isIso l E g
  | some _n => isoSectionwiseConstantMap_isIso g _

/-- Actual constant scalars at any site object; integral scalars use the limit lift.
Source: Stacks Tags 0H7J and 03CO
(blueprint: lem-weil-point-automorphism-restriction-natural). -/
def pointRestrictionScalarAt (S : AlgebraicGeometry.Scheme.{t}) (a : Option ℕ)
    (U : S.ProEt) :
    pointRestrictionScalars.{t, u} l E a →+* (pointRestrictionRing l E S a).obj.obj (op U) :=
  match a with
  | none =>
    (((integralConstantToCompletionOfUniverses l E S).hom.app (op U)).hom).comp
      (((forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
        ((toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app
            (op U))).hom)
  | some n =>
    ((forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
      ((toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
          (op U))).hom

/-- Evaluation followed by the actual constant-scalar restriction. This is the sections
functor of the node, with independent field and coefficient universes.
Source: Stacks Tag 03CW
(blueprint: lem-weil-point-automorphism-restriction-natural). -/
def pointRestrictionSections (k : Type t) [Field k] (a : Option ℕ) :
    SheafOfModules.{max u (t + 1)} (pointRestrictionRing l E (Spec (.of k)) a) ⥤
      ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E a) :=
  SheafOfModules.evaluation _ (op (ProEt.mk (𝟙 (Spec (.of k))))) ⋙
    ModuleCat.restrictScalars
      (pointRestrictionScalarAt l E (Spec (.of k)) a (ProEt.mk (𝟙 _)))

/-- The endofunctor G, with scalar action transported through c inverse.
Source: Stacks Tag 03D6
(blueprint: lem-weil-point-automorphism-restriction-natural). -/
abbrev pointRestrictionInverseImage {S : AlgebraicGeometry.Scheme.{t}}
    (g : S ⟶ S) [IsIso g] (a : Option ℕ) :=
  isoSectionwiseModuleInverseImage g (pointRestrictionCoefficientMap l E g a)

/-- The site arrow V → U has underlying scheme arrow g.
Source: Stacks Tag 09A5
(blueprint: lem-weil-point-automorphism-restriction-natural). -/
def pointRestrictionArrow {S : AlgebraicGeometry.Scheme.{t}} (g : S ⟶ S) [IsIso g] :
    (proEtaleIsoPostcompose g).obj (ProEt.mk (𝟙 S)) ⟶ ProEt.mk (𝟙 S) :=
  MorphismProperty.Over.homMk g (by
    change g ≫ 𝟙 S = 𝟙 S ≫ g
    simp only [Category.comp_id, Category.id_comp]) trivial

/-- Restriction followed by the distinguished coprojection, in the canonical
sectionwise coordinates (where that coprojection is the identity).
Source: Stacks Tags 00VE and 00WX
(blueprint: lem-weil-point-automorphism-restriction-natural). -/
def pointRestrictionRaw {S : AlgebraicGeometry.Scheme.{t}} (g : S ⟶ S) [IsIso g]
    (a : Option ℕ) (M : SheafOfModules.{max u (t + 1)} (pointRestrictionRing l E S a)) :
    (M.val.obj (op (ProEt.mk (𝟙 S)))) →+
      (((pointRestrictionInverseImage l E g a).obj M).val.obj
        (op (ProEt.mk (𝟙 S)))) :=
  (M.val.presheaf.map (pointRestrictionArrow g).op).hom

/-- Additivity of evaluation and scalar restriction, using their recorded constructions.
Source: Stacks Tag 03CW
(blueprint: lem-weil-point-automorphism-restriction-natural). -/
instance pointRestrictionSectionsAdditive (k : Type t) [Field k] (a : Option ℕ) :
    (pointRestrictionSections l E k a).Additive :=
  inferInstanceAs ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _ ⋙
    ModuleCat.restrictScalars _).Additive)

/-- The standard localization of scalar modules at quasi-isomorphisms.
Source: Stacks Tag 05RU
(blueprint: lem-weil-point-automorphism-restriction-natural). -/
instance pointRestrictionScalarDerived (a : Option ℕ) :
    HasDerivedCategory (ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E a)) :=
  HasDerivedCategory.standard _

/-- Restriction at an arbitrary automorphism of the geometric point is normalized
on finite and completed integral constant scalars and is natural on modules,
unbounded complexes and the entire derived category.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (motivation);
Stacks Tags 00VE, 00WX, 0H7J, 03CO, 03CW and 04VG (explicit construction)
(blueprint: lem-weil-point-automorphism-restriction-natural).

Proof: (1) At a site object T the index (B_T, (t,id)), with B_T = (T,g t),
is initial before taking opposites. Each other index has its unique arrow
from B_T, namely its second projection. Thus the distinguished coprojection
identifies the inverse-image colimit with evaluation at B_T.
(2) Postcomposition by g is a covering-preserving equivalence, so this
presheaf is already a sheaf. Sheafification changes nothing, and the
coprojection is identity in these natural coordinates. At U the composite
in the statement is therefore exactly restriction along g : V → U.
(3) At finite level the coefficient map is adjoint to the constant-section
map. The colimit adjunction evaluates it on the distinguished coprojection
as the same constant b, giving c sigma(b) = b.
(4) For completed coefficients compose with every finite projection.
The constructed limit structure map commutes with those projections;
finite-level normalization and joint injectivity of the projections give
the same identity in the completion itself, without discrete replacement.
(5) Module restriction is semilinear. Inverse image transports the action
map coordinatewise, so the scalar identity is sigma(bx) = c inverse(b)sigma(x).
Thus this map is linear for the specified target action, and additive.
(6) Naturality of restriction and of the coprojection gives module naturality.
Apply it to every differential and each component of a chain map to obtain
the termwise chain map and its naturality, in all integer degrees.
(7) Sections at Spec k are exact by lem-weil-point-proetale-sections-exact;
restricting scalar actions preserves exactness. The inverse-image module
functor is exact by def-weil-inverse-image-pullback-comparison. Hence both
complex functors invert quasi-isomorphisms. Apply
lem-weil-pbc-localization-universal-property to descend the functors and
the chain transformation. Its component equation fixes the descended
transformation and gives naturality for every derived morphism, without
constructibility, boundedness or completeness assumptions. -/
theorem point_automorphism_restriction_natural
    (D : FiniteFieldDatum.{t}) (_hl : l ≠ D.p)
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] (a : Option ℕ) :
    (∀ b : pointRestrictionScalars.{t, u} l E a,
      (pointRestrictionRing l E (Spec (.of D.k)) a).obj.map (pointRestrictionArrow g).op
          (pointRestrictionScalarAt l E (Spec (.of D.k)) a (ProEt.mk (𝟙 _)) b) =
        (inv (pointRestrictionCoefficientMap l E g a)).hom.app (op (ProEt.mk (𝟙 _)))
          (pointRestrictionScalarAt l E (Spec (.of D.k)) a (ProEt.mk (𝟙 _)) b)) ∧
    (∀ (M : SheafOfModules.{max u (t + 1)}
        (pointRestrictionRing l E (Spec (.of D.k)) a))
      (b : pointRestrictionScalars.{t, u} l E a)
      (x : M.val.obj (op (ProEt.mk (𝟙 _)))),
      pointRestrictionRaw l E g a M
          (pointRestrictionScalarAt l E (Spec (.of D.k)) a (ProEt.mk (𝟙 _)) b • x) =
        @SMul.smul _ (M.val.obj (op ((proEtaleIsoPostcompose g).obj (ProEt.mk (𝟙 _)))))
          inferInstance
          ((inv (pointRestrictionCoefficientMap l E g a)).hom.app (op (ProEt.mk (𝟙 _)))
            (pointRestrictionScalarAt l E (Spec (.of D.k)) a (ProEt.mk (𝟙 _)) b))
          (pointRestrictionRaw l E g a M x)) ∧
    ∃ σ : pointRestrictionSections l E D.k a ⟶
        pointRestrictionInverseImage l E g a ⋙ pointRestrictionSections l E D.k a,
      (∀ (M : SheafOfModules.{max u (t + 1)}
          (pointRestrictionRing l E (Spec (.of D.k)) a))
        (x : M.val.obj (op (ProEt.mk (𝟙 _)))),
        σ.app M x = pointRestrictionRaw l E g a M x) ∧
      ∃ (F H : DerivedCategory (SheafOfModules.{max u (t + 1)}
          (pointRestrictionRing l E (Spec (.of D.k)) a)) ⥤
            DerivedCategory (ModuleCat.{max u (t + 1)}
              (pointRestrictionScalars.{t, u} l E a)))
        (eF : DerivedCategory.Q ⋙ F ≅
          (pointRestrictionSections l E D.k a).mapHomologicalComplex (.up ℤ) ⋙
            DerivedCategory.Q)
        (eH : DerivedCategory.Q ⋙ H ≅
          Functor.mapHomologicalComplex
            (pointRestrictionInverseImage l E g a ⋙ pointRestrictionSections l E D.k a)
            (.up ℤ) ⋙ DerivedCategory.Q),
        ∃ τ : F ⟶ H, ∀ N : CochainComplex (SheafOfModules.{max u (t + 1)}
            (pointRestrictionRing l E (Spec (.of D.k)) a)) ℤ,
          τ.app (DerivedCategory.Q.obj N) ≫ eH.hom.app N =
            eF.hom.app N ≫
              DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ (.up ℤ)).app N) := by
  sorry

end AlgebraicGeometry.ProEtale
