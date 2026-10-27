/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.AlgebraicGeometry.SpaceNaiveCotangentComplex
public import Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData
import Sheaf.Algebra.Homology.TwoTermDerivedHomBoundary
import Sheaf.CategoryTheory.Sites.SheafifiedDifferentialsCokernel
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Étale sheaf-algebra extensions and cotangent Ext

Source: Stacks Project, Deformation Theory, Tags 0GQ5--0GQ8 and 08UG(2)
(blueprint: lem-sfb-etale-algebra-extension-ext).

The extension objects are the existing `SpaceSquareZeroExtension`, on the full small
étale site. Coefficients are restricted along the existing affine-basis equivalence
when computing derived Ext. Coefficient maps are arbitrary; quotient surjectivity is
local. The Baer relation uses the actual fibre product of ring presheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} {f : X ⟶ B}

/-- A map of extensions over an arbitrary coefficient map, fixing base and quotient.
Source: Stacks 0GQ8 (blueprint: lem-sfb-etale-algebra-extension-ext). -/
structure EtaleExtensionHom {G H : X.Modules} (v : G ⟶ H)
    (E : SpaceSquareZeroExtension f G) (F : SpaceSquareZeroExtension f H) where
  map : E.algebra.obj ⟶ F.algebra.obj
  quotient : map ≫ F.quotient = E.quotient
  kernel (U : X.EtaleSite) (g : G.val.obj (op U)) :
    map.app (op U) (E.inclusion U g) = F.inclusion U (v.val.app (op U) g)
  base (U : X.EtaleSite) (V : B.EtaleSite) (a : U.obj.left ⟶ V.obj.left)
    (ha : U.obj.hom ≫ f.hom.hom = yoneda.map a ≫ V.obj.hom) :
    E.base.app U V a ha ≫ map.app (op U) = F.base.app U V a ha

/-- Isomorphisms in the marked extension groupoid. Source: Stacks 0GQ5
(blueprint: lem-sfb-etale-algebra-extension-ext). -/
structure EtaleExtensionIso {G : X.Modules} (E F : SpaceSquareZeroExtension f G) where
  ringIso : E.algebra.obj ≅ F.algebra.obj
  compatible : EtaleExtensionHom (𝟙 G) E F
  hom_eq : compatible.map = ringIso.hom

/-- Connected components of the extension groupoid, with both ends marked.
Source: Stacks 0GQ5 (blueprint: lem-sfb-etale-algebra-extension-ext). -/
def etaleExtensionClasses (f : X ⟶ B) (G : X.Modules) :=
  Quot (fun E F : SpaceSquareZeroExtension f G ↦ Nonempty (EtaleExtensionIso E F))

/-- The component of an extension. Source: Stacks 0GQ5
(blueprint: lem-sfb-etale-algebra-extension-ext). -/
def etaleExtensionClass {G : X.Modules} (E : SpaceSquareZeroExtension f G) :
    etaleExtensionClasses f G := Quot.mk _ E

/-- A split extension, specified by its algebra section. Such a section gives the
canonical isomorphism `(a,g) ↦ s(a)+i(g)` from the trivial square-zero algebra.
Source: Stacks 0GQ5 (blueprint: lem-sfb-etale-algebra-extension-ext). -/
def EtaleExtensionIsSplit {G : X.Modules} (E : SpaceSquareZeroExtension f G) : Prop :=
  ∃ s : X.structurePresheaf ⟶ E.algebra.obj,
    s ≫ E.quotient = 𝟙 _ ∧
    ∀ (U : X.EtaleSite) (V : B.EtaleSite) (a : U.obj.left ⟶ V.obj.left)
      (ha : U.obj.hom ≫ f.hom.hom = yoneda.map a ≫ V.obj.hom),
      (forget₂ CommRingCat RingCat).map (Scheme.Γ.map a.left.op) ≫ s.app (op U) =
        E.base.app U V a ha

/-- The actual fibre-product-then-addition Baer diagram. A ring map out of the
fibre product over the quotient, over the base, sends `(i(g),i(h))` to `i(g+h)`.
Its target, already an extension, is therefore the coefficient pushout by addition.
Source: Stacks 0GQ6, explicit conormal-class calculation
(blueprint: lem-sfb-etale-algebra-extension-ext). -/
structure EtaleExtensionBaer {G : X.Modules}
    (E F T : SpaceSquareZeroExtension f G) where
  map : Limits.pullback E.quotient F.quotient ⟶ T.algebra.obj
  quotient : map ≫ T.quotient = pullback.fst E.quotient F.quotient ≫ E.quotient
  kernel (U : X.EtaleSite) (z : (Limits.pullback E.quotient F.quotient).obj (op U))
    (g h : G.val.obj (op U))
    (hg : (pullback.fst E.quotient F.quotient).app (op U) z = E.inclusion U g)
    (hh : (pullback.snd E.quotient F.quotient).app (op U) z = F.inclusion U h) :
    map.app (op U) z = T.inclusion U (g + h)
  base (U : X.EtaleSite) (V : B.EtaleSite) (a : U.obj.left ⟶ V.obj.left)
    (ha : U.obj.hom ≫ f.hom.hom = yoneda.map a ≫ V.obj.hom)
    (b : B.structurePresheaf.obj (op V))
    (z : (Limits.pullback E.quotient F.quotient).obj (op U))
    (he : (pullback.fst E.quotient F.quotient).app (op U) z = E.base.app U V a ha b)
    (hf : (pullback.snd E.quotient F.quotient).app (op U) z = F.base.app U V a ha b) :
    map.app (op U) z = T.base.app U V a ha b

/-- Derived Ext in the recorded cotangent calculus, restricting precisely the given
module along the affine basis. Source: Stacks 0GQ5
(blueprint: lem-sfb-etale-algebra-extension-ext). -/
abbrev etaleCotangentExt (f : X ⟶ B) [HasDerivedCategory.{w} X.SmallModules]
    (G : X.Modules) (n : ℤ) :=
  derivedExt X (naiveCotangent f)
    (cotangentCoefficient X (X.smallModuleRestriction.obj G)) n

/-- The usual coefficient map on derived Ext, expressed as postcomposition.
Source: Stacks 0GQ8 (blueprint: lem-sfb-etale-algebra-extension-ext). -/
def etaleCotangentExtMap [HasDerivedCategory.{w} X.SmallModules]
    {G H : X.Modules} (v : G ⟶ H) (n : ℤ) :
    etaleCotangentExt f G n → etaleCotangentExt f H n :=
  fun x ↦ x ≫ ((DerivedCategory.singleFunctor X.SmallModules 0).map
    (X.smallModuleRestriction.map v))⟦n⟧'

/-- The inverse-image coefficient section on a compatible pair of charts, obtained
from the actual adjunction unit, enlarged-chart restriction, and comparison counit.
Source: Stacks 03G8 and 0GQ6 (blueprint: lem-sfb-etale-algebra-extension-ext). -/
def cotangentInverseChartSection (f : X ⟶ B) (U : X.SmallEtaleModel)
    (V : B.EtaleSite) (a : (X.smallEtaleInclusion.obj U).obj.left ⟶ V.obj.left)
    (ha : yoneda.map a ≫ V.obj.hom =
      (X.smallEtaleInclusion.obj U).obj.hom ≫ f.hom.hom) :
    B.commStructureSheaf.obj.obj (op V) ⟶
      ((cotangentRingInverse f).obj B.smallStructureSheaf).obj.obj (op U) :=
  ((cotangentRingAdjunction f).unit.app B.commStructureSheaf).hom.app (op V) ≫
    (((enlargedCommEquivalence X).inverse.obj
      ((@Functor.leftAdjoint _ _ _ _ (cotangentRingDirect f)
        (cotangentRingDirect_rightAdjoint f)).obj B.commStructureSheaf)).obj.map
        (enlargedChartLift f (X.smallEtaleInclusion.obj U) V a ha).op) ≫
    (((enlargedCommEquivalence X).counitIso.hom.app
      ((@Functor.leftAdjoint _ _ _ _ (cotangentRingDirect f)
        (cotangentRingDirect_rightAdjoint f)).obj B.commStructureSheaf)).hom.app
        (op (X.smallEtaleInclusion.obj U))) ≫
    (((@Functor.leftAdjoint _ _ _ _ (cotangentRingDirect f)
        (cotangentRingDirect_rightAdjoint f)).map
      ((cotangentSmallEquivalence B).unitIso.hom.app B.commStructureSheaf)).hom.app
        (op (X.smallEtaleInclusion.obj U)))

/-- Polynomial coordinates for the canonical class, with the positive conormal
boundary. The lift respects the given base action on every compatible chart pair.
The comparison is fixed on conormal classes and universal differential tensors;
the projection is identity in degree minus one. Thus no sign or abstract derived
isomorphism is left unspecified. Source: Stacks 0GQ6 and 08TY
(blueprint: lem-sfb-etale-algebra-extension-ext). -/
structure EtaleExtensionCoordinates {G : X.Modules} (E : SpaceSquareZeroExtension f G) where
  presentation : SheafPolynomialCotangent.Presentation (cotangentRingMap f)
  model : SheafPolynomialCotangent.Model presentation
  lift : (SheafPolynomialCotangent.polynomialSheaf
      ((cotangentRingInverse f).obj B.smallStructureSheaf) presentation.generators).obj ⋙
        forget₂ CommRingCat RingCat ⟶ X.smallEtaleInclusion.op ⋙ E.algebra.obj
  lift_quotient : lift ≫ Functor.whiskerLeft X.smallEtaleInclusion.op E.quotient =
    Functor.whiskerRight
      (SheafPolynomialCotangent.evaluation (cotangentRingMap f) presentation.values).hom
      (forget₂ CommRingCat RingCat)
  lift_base (U : X.SmallEtaleModel) (V : B.EtaleSite)
    (a : (X.smallEtaleInclusion.obj U).obj.left ⟶ V.obj.left)
    (ha : yoneda.map a ≫ V.obj.hom =
      (X.smallEtaleInclusion.obj U).obj.hom ≫ f.hom.hom) :
    (forget₂ CommRingCat RingCat).map
      (cotangentInverseChartSection f U V a ha ≫
        (SheafPolynomialCotangent.base
          ((cotangentRingInverse f).obj B.smallStructureSheaf)
          presentation.generators).hom.app (op U)) ≫ lift.app (op U) =
      E.base.app (X.smallEtaleInclusion.obj U) V a ha.symm
  delta : model.complex.X (-1) ⟶ X.smallModuleRestriction.obj G
  delta_formula (U : X.SmallEtaleModel)
    (j : (SheafPolynomialCotangent.kernelIdeal presentation).sections U) :
    E.inclusion (X.smallEtaleInclusion.obj U)
      (delta.val.app (op U) (model.quotient.val.app (op U) j)) = lift.app (op U) j.val
  comparison : model.complex ⟶ naiveCotangentComplex f
  comparison_conormal (U : X.SmallEtaleModelᵒᵖ)
    (j : (SheafPolynomialCotangent.kernelIdeal presentation).sections U.unop)
    (j' : (SheafPolynomialCotangent.kernelIdeal
      (cotangentPresentation f)).sections U.unop)
    (hj : (j' : (SheafPolynomialCotangent.polynomialSheaf
        ((cotangentRingInverse f).obj B.smallStructureSheaf)
        (cotangentPresentation f).generators).obj.obj U) =
      (SheafPolynomialCotangent.polynomialMap
        ((cotangentRingInverse f).obj B.smallStructureSheaf) presentation.values).hom.app U j) :
    ((comparison.f (-1) ≫ eqToHom
      ((congrFun (CochainComplex.of_X (naiveCotangentTerm f) (naiveCotangentBoundary f)
        (naiveCotangentBoundary_comp f)) (-1)).trans (naiveCotangentTerm_degrees f).1)).val.app U)
      (model.quotient.val.app U j) = cotangentConormalClass f U j'
  comparison_differentials (U : X.SmallEtaleModelᵒᵖ)
    (b : X.smallStructureSheaf.obj.obj U)
    (p : (SheafPolynomialCotangent.polynomialSheaf
      ((cotangentRingInverse f).obj B.smallStructureSheaf)
      presentation.generators).obj.obj U) :
    ((comparison.f 0 ≫ eqToHom
      ((congrFun (CochainComplex.of_X (naiveCotangentTerm f) (naiveCotangentBoundary f)
        (naiveCotangentBoundary_comp f)) 0).trans (naiveCotangentTerm_degrees f).2)).val.app U)
      (model.degreeZero.inv.val.app U
        (SheafPolynomialCotangent.tensorD presentation U b p)) =
      SheafPolynomialCotangent.tensorD (cotangentPresentation f) U b
        ((SheafPolynomialCotangent.polynomialMap
          ((cotangentRingInverse f).obj B.smallStructureSheaf) presentation.values).hom.app U p)
  projection : model.complex ⟶
    (CochainComplex.singleFunctor X.SmallModules (-1)).obj (model.complex.X (-1))
  projection_normalization : projection.f (-1) ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
      (model.complex.X (-1))).hom = 𝟙 _

/-- The positive boundary of the conormal map in the chosen polynomial coordinates.
The comparison goes from that presentation to the fixed naive cotangent complex.
Source: Stacks 0GQ6 (blueprint: lem-sfb-etale-algebra-extension-ext). -/
def EtaleExtensionCoordinates.Represents [HasDerivedCategory.{w} X.SmallModules]
    {G : X.Modules} {E : SpaceSquareZeroExtension f G} (P : EtaleExtensionCoordinates E)
    (c : etaleCotangentExt f G 1) : Prop :=
  DerivedCategory.Q.map P.comparison ≫ c =
    DerivedCategory.Q.map P.projection ≫
      (DerivedCategory.singleFunctor X.SmallModules (-1)).map P.delta ≫
      ((DerivedCategory.singleFunctors X.SmallModules).shiftIso 1 (-1) 0 rfl).inv.app
        (X.smallModuleRestriction.obj G)

/-- All clauses of the canonical classification, including the additive automorphism
formula. Automorphisms are identified on every affine chart, which determines them on
the entire étale site by the affine-basis comparison.
Source: Stacks 0GQ5--0GQ8 and 08UG(2)
(blueprint: lem-sfb-etale-algebra-extension-ext). -/
structure EtaleAlgebraExtensionClassification (f : X ⟶ B)
    [HasDerivedCategory.{w} X.SmallModules] where
  classes (G : X.Modules) : etaleExtensionClasses f G ≃ etaleCotangentExt f G 1
  class_normalization {G : X.Modules} (E : SpaceSquareZeroExtension f G) :
    ∃ P : EtaleExtensionCoordinates E, P.Represents (classes G (etaleExtensionClass E))
  split_exists (G : X.Modules) : ∃ E : SpaceSquareZeroExtension f G, EtaleExtensionIsSplit E
  split (G : X.Modules) (E : SpaceSquareZeroExtension f G) :
    EtaleExtensionIsSplit E → classes G (etaleExtensionClass E) = 0
  pushout_exists {G H : X.Modules} (v : G ⟶ H) (E : SpaceSquareZeroExtension f G) :
    ∃ F : SpaceSquareZeroExtension f H, Nonempty (EtaleExtensionHom v E F)
  naturality {G H : X.Modules} (v : G ⟶ H) (E : SpaceSquareZeroExtension f G)
    (F : SpaceSquareZeroExtension f H) (_q : EtaleExtensionHom v E F) :
    classes H (etaleExtensionClass F) =
      etaleCotangentExtMap v 1 (classes G (etaleExtensionClass E))
  baer_exists {G : X.Modules} (E F : SpaceSquareZeroExtension f G) :
    ∃ T : SpaceSquareZeroExtension f G, Nonempty (EtaleExtensionBaer E F T)
  baer {G : X.Modules} (E F T : SpaceSquareZeroExtension f G)
    (_b : EtaleExtensionBaer E F T) :
    classes G (etaleExtensionClass T) =
      classes G (etaleExtensionClass E) + classes G (etaleExtensionClass F)
  augmentation : naiveCotangentComplex f ⟶
    (CochainComplex.singleFunctor X.SmallModules 0).obj
      (SheafDifferentials.omega (cotangentRingMap f))
  augmentation_formula (U : X.SmallEtaleModelᵒᵖ)
    (b : X.smallStructureSheaf.obj.obj U)
    (p : (SheafPolynomialCotangent.polynomialSheaf
      ((cotangentRingInverse f).obj B.smallStructureSheaf)
      (cotangentPresentation f).generators).obj.obj U) :
    ((augmentation.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafDifferentials.omega (cotangentRingMap f))).hom).val.app U)
      ((eqToHom
        (((congrFun (CochainComplex.of_X (naiveCotangentTerm f)
          (naiveCotangentBoundary f) (naiveCotangentBoundary_comp f)) 0).trans
            (naiveCotangentTerm_degrees f).2).symm)).val.app U
        (SheafPolynomialCotangent.tensorD (cotangentPresentation f) U b p)) =
      b • (SheafDifferentials.derivation (cotangentRingMap f)).d
        ((SheafPolynomialCotangent.evaluation (cotangentRingMap f)
          (cotangentPresentation f).values).hom.app U p)
  omegaIso : (naiveCotangentComplex f).homology 0 ≅
    SheafDifferentials.omega (cotangentRingMap f)
  omegaIso_hom : omegaIso.hom =
    (HomologicalComplex.homologyFunctor X.SmallModules (ComplexShape.up ℤ) 0).map
      augmentation ≫ (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.up ℤ) 0 (SheafDifferentials.omega (cotangentRingMap f))).hom
  homZero (G : X.Modules) : etaleCotangentExt f G 0 ≃+
    (SheafDifferentials.omega (cotangentRingMap f) ⟶ X.smallModuleRestriction.obj G)
  homZero_normalization (G : X.Modules) (x : etaleCotangentExt f G 0) :
    x ≫ (shiftFunctorZero X.DerivedModules ℤ).hom.app
      (cotangentCoefficient X (X.smallModuleRestriction.obj G)) =
    DerivedCategory.Q.map augmentation ≫
      (DerivedCategory.singleFunctor X.SmallModules 0).map (homZero G x)
  homZero_natural {G H : X.Modules} (v : G ⟶ H) (x : etaleCotangentExt f G 0) :
    homZero H (etaleCotangentExtMap v 0 x) = homZero G x ≫ X.smallModuleRestriction.map v
  automorphisms {G : X.Modules} (E : SpaceSquareZeroExtension f G) :
    etaleCotangentExt f G 0 ≃ EtaleExtensionIso E E
  automorphism_formula {G : X.Modules} (E : SpaceSquareZeroExtension f G)
    (x : etaleCotangentExt f G 0) (U : X.SmallEtaleModel)
    (a : E.algebra.obj.obj (op (X.smallEtaleInclusion.obj U))) :
    ((automorphisms E x).ringIso.hom.app (op (X.smallEtaleInclusion.obj U))) a =
      a + E.inclusion (X.smallEtaleInclusion.obj U)
        ((homZero G x).val.app (op U)
          ((SheafDifferentials.derivation (cotangentRingMap f)).d
            (E.quotient.app (op (X.smallEtaleInclusion.obj U)) a)))
  automorphism_add {G : X.Modules} (E : SpaceSquareZeroExtension f G)
    (x y : etaleCotangentExt f G 0) :
    (automorphisms E (x + y)).ringIso.hom =
      (automorphisms E y).ringIso.hom ≫ (automorphisms E x).ringIso.hom
  automorphism_natural {G H : X.Modules} (v : G ⟶ H)
    (E : SpaceSquareZeroExtension f G) (F : SpaceSquareZeroExtension f H)
    (q : EtaleExtensionHom v E F) (x : etaleCotangentExt f G 0) :
    (automorphisms E x).ringIso.hom ≫ q.map =
      q.map ≫ (automorphisms F (etaleCotangentExtMap v 0 x)).ringIso.hom

/-- Sheaf-algebra extensions are classified by cotangent Ext one, with additive,
coefficient-natural Ext-zero automorphisms and the explicit derivation formula.
Source: Stacks Project, Tags 0GQ5--0GQ8 and 08UG(2)
(blueprint: lem-sfb-etale-algebra-extension-ext).

Proof, following all nine steps of the DAG:
1. Use the recorded naive cotangent complex on the affine basis. Polynomial
   comparison and the two-term derived Hom boundary identify its degree-zero Hom
   with maps from differentials, hence relative derivations. No coherence is used.
2. Choose generators from the underlying extension sheaf, lift the polynomial
   presentation by sheafification, and restrict to its conormal quotient. Apply the
   boundary. The common presentation on the coproduct of generators and naturality
   make this class independent of choices and invariant under marked isomorphism.
3. For equal classes use the common fibre-product presentation. Boundary exactness
   gives a derivation correcting one lift by minus its kernel inclusion. The corrected
   algebra map descends to an isomorphism, by the local kernel and quotient calculation.
4. For a conormal representative delta of an Ext class, take the semidirect algebra
   (P/J²) ⋉ G modulo the ideal (m,-delta(m)). Its kernel is exactly G and its quotient
   is O; its class is the original class. This uses the representative node, not an
   injectivity or quasi-coherence assumption on G.
5. The split section kills the conormal map, so the trivial extension has class zero.
6. For any coefficient map v form (T ⋉ H)/(i(g),-v(g)). Local representatives prove
   exactness; its conormal map is v delta. Boundary naturality proves pushout naturality.
7. The common fibre-product presentation has conormal map (delta1,delta2). Pushing out
   by addition gives delta1+delta2, hence addition of Ext classes.
8. Send a derivation d to a ↦ a+i(d(p(a))). Leibniz and square zero prove
   multiplicativity; the inverse uses -d. Conversely the difference from identity
   descends through p to a unique relative derivation. Composition adds derivations.
9. For pushout q, qi_G=i_H v gives qT_d=T_(vd)q. The universal derivation and
   degree-zero derived Hom identifications are natural, giving both compatibilities.
-/
theorem etale_algebra_extension_ext (f : X ⟶ B) [HasDerivedCategory.{w} X.SmallModules] :
    Nonempty (EtaleAlgebraExtensionClassification f) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
