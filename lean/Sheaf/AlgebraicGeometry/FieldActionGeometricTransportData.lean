module

public import Sheaf.AlgebraicGeometry.FieldActionScalarTransportData
public import Sheaf.Paper.NormContinuousMonodromyData
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! # Normalized field-action transport interfaces

Source: Bhatt--Scholze Example 4.1.10, Definition 6.8.3 and Proposition 6.8.4;
main-20261015 direct-images paragraph (3), normalized ordinary derived sections
(blueprint: def-sfb-field-action-geometric-transport-data).

## Main definitions

* `GeometricTransport`: the two normalized presentations of geometric derived sections.
* `scalarProjection`, `pointProjection`: the specified adjunction-transpose constructions.
* `LisseTransport`: realization of the same field functor on continuous finite monodromy.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FieldActionTransport

open CondensedGalois

variable (k ks : Type u) [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks]

section Geometry
variable (X : Scheme.{u}) (a : X ⟶ Spec (.of k))
variable (R : Coefficients.{u}) [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)]
variable [ForgetData k ks R] (e : FieldData k ks R) (d : OrdinaryData k ks X a R)
variable [(fieldFunctor k ks e).IsEquivalence]
variable [PreservesFiniteLimits (fieldFunctor k ks e)]
variable [PreservesFiniteColimits (fieldFunctor k ks e)]
variable [PointAdjunctionData R (geometricScheme.{u} k ks X a)]
variable [PreservesFiniteLimits
    (CondensedRing.upperStar.{u} R.X (geometricProjection.{u} k ks X a))]
variable [PreservesFiniteColimits
    (CondensedRing.upperStar.{u} R.X (geometricProjection.{u} k ks X a))]

/-- Derived geometric sections with their field and forgotten presentations, normalized
by the actual section maps and the two total-right-derived units.
Source: field-action node, derived geometric normalization paragraphs
(blueprint: def-sfb-field-action-geometric-transport-data). -/
structure GeometricTransport where
  /-- Base change of every geometric test, including the empty test. -/
  tests : ∀ P : Profinite.{u}, test k ks X a P ≅
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ a).obj
      (test k ks (Spec (.of k)) (𝟙 _) P)
  /-- The test comparison is the canonical map on every geometric fibre. -/
  test_fibres : ∀ (P : Profinite.{u}) (p : P),
    fibreMap k ks X a P p ≫ (tests P).hom.left ≫
      pullback.fst (test k ks (Spec (.of k)) (𝟙 _) P).hom a =
        geometricToField k ks X a ≫ fibreMap k ks (Spec (.of k)) (𝟙 _) P p
  /-- Ordinary structure direct image becomes the existing geometric section functor. -/
  ordinary : CondensedRing.lowerStar.{u} R.X a ⋙ fieldFunctor k ks e ≅ d.geometric.functor
  /-- On each test the comparison is exactly the displayed base-change restriction. -/
  sections : ∀ (M : Modules R.toMon X) (P : Profinite.{u}),
    ((e.geometric.sections.hom.app ((CondensedRing.lowerStar.{u} R.X a).obj M)).app (op P)) ≫
        M.X.obj.map (tests P).hom.op =
      ((ordinary.hom.app M).val).hom.hom.app (op P) ≫
        (d.geometric.sections.hom.app M).app (op P)
  /-- The derived-object isomorphism, for arbitrary unbounded inputs. -/
  derived : (CondensedRing.lowerStar.{u} R.X a).rightDerivedFunctor.{u + 2, u + 2, u + 1, u + 1,
    u + 2, u + 2} ⋙
    (fieldFunctor k ks e).mapDerivedCategory ≅ d.geometric.functor.rightDerivedFunctor
  /-- Its canonical total-derived-unit equation. -/
  derived_unit : IsNormalizedPostComparison.{u}
    (CondensedRing.lowerStar.{u} R.X a) (fieldFunctor k ks e) d.geometric.functor
    (addF := CondensedRing.lowerStar_additive R.X a) (addE := e.geometric.additive)
    (addH := d.geometric.additive) ordinary derived
  /-- Forgetting gives the derived point direct image of the exact geometric pullback. -/
  forgotten : d.geometric.functor.rightDerivedFunctor ⋙
    CategoryTheory.CondensedBar.forgetAction.mapDerivedCategory ≅
      (CondensedRing.upperStar.{u} R.X (geometricProjection.{u} k ks X a)).mapDerivedCategory ⋙
        (pointModules.{u} R.toMon (geometricScheme.{u} k ks X a)).rightDerivedFunctor
  /-- This is the slice/composition comparison, normalized by geometricRestriction. -/
  forgotten_unit : IsNormalizedComparison.{u} d.geometric.functor
    CategoryTheory.CondensedBar.forgetAction
    (CondensedRing.upperStar.{u} R.X (geometricProjection.{u} k ks X a))
    (pointModules.{u} R.toMon (geometricScheme.{u} k ks X a))
    (addF := d.geometric.additive)
    (addL := CondensedRing.upperStar_additive R.X (geometricProjection.{u} k ks X a))
    (addP := (inferInstance : PointAdjunctionData R (geometricScheme.{u} k ks X a)).additive)
    d.geometric.underlying forgotten
  /-- Both natural derived-object identifications preserve canonical shifts. -/
  derived_shift : NatTrans.CommShift derived.hom ℤ
  /-- Shift compatibility of the forgotten identification. -/
  forgotten_shift : NatTrans.CommShift forgotten.hom ℤ

end Geometry



/-- The coefficient projection, defined by exactly the scalar-adjunction transpose in
our node. This is a construction from specified adjunctions and their restriction square.
Source: field-action node, explicit definition of beta
(blueprint: def-sfb-field-action-geometric-transport-data). -/
def scalarProjection
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    {S : C ⥤ C'} {V : C' ⥤ C} {T : D ⥤ D'} {W : D' ⥤ D}
    (adjX : S ⊣ V) (adjS : T ⊣ W) (F : C ⥤ D) (F' : C' ⥤ D')
    (ρ : V ⋙ F ≅ F' ⋙ W) (M : C) : T.obj (F.obj M) ⟶ F'.obj (S.obj M) :=
  (adjS.homEquiv (F.obj M) (F'.obj (S.obj M))).symm
    (F.map (adjX.unit.app M) ≫ ρ.hom.app (S.obj M))

/-- The exact pullback on the chosen common-universe derived category.
Source: field-action node, geometric pullback
(blueprint: def-sfb-field-action-geometric-transport-data). -/
abbrev pull (R : Coefficients.{u}) {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    DerivedCategory.{u + 2} (Modules R.toMon Z) ⥤
      DerivedCategory.{u + 2} (Modules R.toMon Y) :=
  (CondensedRing.upperStar.{u} R.X f).mapDerivedCategory

/-- The ordinary unbounded right derived structure direct image.
Source: field-action node, Ra_*
(blueprint: def-sfb-field-action-geometric-transport-data). -/
abbrev push (R : Coefficients.{u}) {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    DerivedCategory.{u + 2} (Modules R.toMon Y) ⥤
      DerivedCategory.{u + 2} (Modules R.toMon Z) :=
  (CondensedRing.lowerStar.{u} R.X f).rightDerivedFunctor.{u + 2, u + 2, u + 1, u + 1,
    u + 2, u + 2}

/-- The canonical derived geometric adjunction, using exactness of coefficient pullback.
Source: field-action node, counit-adjoint projection
(blueprint: def-sfb-field-action-geometric-transport-data). -/
def geometricAdjunction (R : Coefficients.{u}) {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    pull R f ⊣ push R f :=
  (CondensedRing.upperStarLowerStarAdjunction R.X f).mapDerivedCategoryRightDerivedAdjunction

/-- The normalized scalar exchanges for an actual scheme morphism. The right comparison
is the canonical derived composition comparison of the identical underlying direct
images; adjunction transposes then fix both pullback comparisons.
Source: field-action node, scalar-restriction and pullback comparisons
(blueprint: def-sfb-field-action-geometric-transport-data). -/
structure MorphismScalar {R R' : Coefficients.{u}} (φ : R ⟶ R')
    {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [addPush : Functor.Additive.{u + 1, u + 2, u + 1, u + 2}
      (CondensedRing.lowerStar.{u} R.X f)]
    [addPush' : Functor.Additive.{u + 1, u + 2, u + 1, u + 2}
      (CondensedRing.lowerStar.{u} R'.X f)] where
  /-- Direct-image restriction, with its total-derived-unit equation. -/
  direct : @CoefficientComparison.{u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (restrictX φ Y) _ _ _ (restrictX φ Z) _ _ _
    (CondensedRing.lowerStar.{u} R.X f) addPush
    (CondensedRing.lowerStar.{u} R'.X f) addPush'
  /-- Underived restriction leaves the underlying abelian-sheaf map unchanged. -/
  identity : ∀ M : Modules R'.toMon Y, (direct.ordinary.hom.app M).hom = 𝟙 _
  /-- Conjugacy under the two canonical geometric adjunctions. -/
  pullRestriction : AdjunctionSquare (geometricAdjunction R' f) (geometricAdjunction R f)
    (restrictX φ Z).mapDerivedCategory (restrictX φ Y).mapDerivedCategory
  /-- The geometric square uses exactly the same direct-image comparison. -/
  direct_normalization : pullRestriction.restriction = direct.derived.symm
  /-- Scalar extension and geometric pullback commute as normalized scalar adjunctions. -/
  pullExtension : AdjunctionSquare (scalarDerivedAdjunction φ Z)
    (scalarDerivedAdjunction φ Y) (pull R f) (pull R' f)
  /-- The two scalar/geometric squares use the identical restriction comparison. -/
  restriction_normalization : pullExtension.restriction = pullRestriction.extension.symm

/-- Derive a square of exact additive functors using the canonical composition maps.
Source: field-action node, coefficient restriction normalization
(blueprint: def-sfb-field-action-geometric-transport-data). -/
def derivedSquare
    {C D C' D' : Type (u + 2)}
    [Category.{u + 1} C] [Category.{u + 1} D]
    [Category.{u + 1} C'] [Category.{u + 1} D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory.{u + 2} C] [HasDerivedCategory.{u + 2} D]
    [HasDerivedCategory.{u + 2} C'] [HasDerivedCategory.{u + 2} D']
    (V : C' ⥤ C) (E : C ⥤ D) (F : C' ⥤ D') (W : D' ⥤ D)
    [V.Additive] [E.Additive] [F.Additive] [W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (o : V ⋙ E ≅ F ⋙ W) :
    V.mapDerivedCategory ⋙ E.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ W.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso V E).symm ≪≫
    Functor.mapDerivedCategoryNatIso o ≪≫ Functor.mapDerivedCategoryCompIso F W

/-- The point pullback's derived scalar exchange is normalized by the termwise scalar
restriction square of its actual monoidal inverse image.
Source: field-action node, forgotten coefficient projection
(blueprint: def-sfb-field-action-geometric-transport-data). -/
structure PointScalar {R R' : Coefficients.{u}} (φ : R ⟶ R') (Y : Scheme.{u})
    [PointAdjunctionData R Y] [PointAdjunctionData R' Y] where
  /-- The extension/restriction mate square. -/
  square : AdjunctionSquare (condensedScalarAdjunction φ) (scalarDerivedAdjunction φ Y)
    (pointPull R Y).mapDerivedCategory (pointPull R' Y).mapDerivedCategory
  /-- The right comparison is induced by the ordinary mapMod/comap comparison. -/
  normalization : square.restriction =
    derivedSquare.{u} (restrictCondensed φ) (pointPull R Y) (pointPull R' Y) (restrictX φ Y)
      ((upperStarFromPoint Y).mapModComapIso φ.hom.hom)

/-- The point coefficient projection, defined as the counit-adjoint map displayed in the
node: pull back the source, use the scalar exchange, then apply extension to the counit.
Source: field-action node, displayed forgotten projection
(blueprint: def-sfb-field-action-geometric-transport-data). -/
def pointProjection {R R' : Coefficients.{u}} (φ : R ⟶ R') (Y : Scheme.{u})
    [d : PointAdjunctionData R Y] [d' : PointAdjunctionData R' Y]
    (c : PointScalar φ Y) (M : DerivedCategory (Modules R.toMon Y)) :
    (condensedDerivedExtend φ).obj ((pointModules.{u} R.toMon Y).rightDerivedFunctor.obj M) ⟶
      (pointModules.{u} R'.toMon Y).rightDerivedFunctor.obj ((derivedExtend φ Y).obj M) :=
  ((pointDerivedAdjunction (R := R') (Y := Y)).homEquiv _ _)
    (c.square.extension.hom.app ((pointModules.{u} R.toMon Y).rightDerivedFunctor.obj M) ≫
      (derivedExtend φ Y).map ((pointDerivedAdjunction (R := R) (Y := Y)).counit.app M))



/-- Bundle the existing all-continuous norm-topology coefficient ring.
Source: field-action node, R(P)=C(P,E)
(blueprint: def-sfb-field-action-geometric-transport-data). -/
def normCoefficients (E : Type u) [NormedField E] : Coefficients.{u} where
  X := (normContinuousRing E).X
  mon := (normContinuousRing E).mon
  comm := normContinuousRing_comm E

/-- Continuous functions into the finite-dimensional representation with its module
(norm) topology. This introduces no new representation category.
Source: field-action node, continuous-function realization
(blueprint: def-sfb-field-action-geometric-transport-data). -/
abbrev representationFunctions (E : Type u) [NormedField E]
    (V : NormContinuousRepresentations E (ks ≃ₐ[k] ks)) (P : Profinite.{u}) :=
  @ContinuousMap P V.obj.V inferInstance (moduleTopology E V.obj.V)

/-- The finite-rank lisse restriction of the same field functor. The existing norm
representation category allows an empty finite basis and uses every equivariant linear
map. The section bijections preserve addition, all continuous scalar functions, every
variable Galois element, test restrictions and representation morphisms.
Source: Bhatt--Scholze Definition 6.8.3 and Proposition 6.8.4
(blueprint: def-sfb-field-action-geometric-transport-data). -/
structure LisseTransport (E : Type u) [NormedField E]
    [CategoryTheory.CondensedBar.ActionAbelian (normCoefficients E) (ks ≃ₐ[k] ks)]
    (e : FieldData k ks (normCoefficients E)) where
  /-- The lisse/continuous finite-dimensional equivalence. -/
  equivalence : NormContinuousLisse E (Spec (.of k)) ≌
    NormContinuousRepresentations E (ks ≃ₐ[k] ks)
  /-- The realization is exactly P maps to C(P,W). -/
  sections : ∀ (V : NormContinuousRepresentations E (ks ≃ₐ[k] ks)) (P : Profinite.{u}),
    Profinite.CondensedAction.sectionModule (normCoefficients E).toMon
      ((fieldFunctor k ks e).obj (equivalence.inverse.obj V).obj).module P ≃
        representationFunctions k ks E V P
  /-- Addition is pointwise addition. -/
  add : ∀ (V : NormContinuousRepresentations E (ks ≃ₐ[k] ks)) (P : Profinite.{u})
    (m n : Profinite.CondensedAction.sectionModule (normCoefficients E).toMon
      ((fieldFunctor k ks e).obj (equivalence.inverse.obj V).obj).module P) (p : P),
    sections V P (m + n) p = sections V P m p + sections V P n p
  /-- All continuous coefficient functions, not only constants, act pointwise. -/
  scalar : ∀ (V : NormContinuousRepresentations E (ks ≃ₐ[k] ks)) (P : Profinite.{u})
    (r : (InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) (normCoefficients E).X).obj (op P))
    (m : Profinite.CondensedAction.sectionModule (normCoefficients E).toMon
      ((fieldFunctor k ks e).obj (equivalence.inverse.obj V).obj).module P) (p : P),
    sections V P (r • m) p = r.down p • sections V P m p
  /-- Every generalized Galois element acts by the given continuous representation. -/
  action : ∀ (V : NormContinuousRepresentations E (ks ≃ₐ[k] ks)) (P : Profinite.{u})
    (g : C(P, ks ≃ₐ[k] ks))
    (m : Profinite.CondensedAction.sectionModule (normCoefficients E).toMon
      ((fieldFunctor k ks e).obj (equivalence.inverse.obj V).obj).module P) (p : P),
    sections V P (((fieldFunctor k ks e).obj (equivalence.inverse.obj V).obj).act P g m) p =
      V.obj.ρ (g p) (sections V P m p)
  /-- Restriction is precomposition on continuous functions. -/
  restriction : ∀ (V : NormContinuousRepresentations E (ks ≃ₐ[k] ks))
    (P Q : Profinite.{u}) (f : Q ⟶ P)
    (m : Profinite.CondensedAction.sectionModule (normCoefficients E).toMon
      ((fieldFunctor k ks e).obj (equivalence.inverse.obj V).obj).module P) (q : Q),
    sections V Q
      ((((fieldFunctor k ks e).obj (equivalence.inverse.obj V).obj).module.X.obj.map f.op).hom
        m) q = sections V P m (f q)
  /-- Equivariant linear arrows are realized by pointwise postcomposition. -/
  maps : ∀ (V W : NormContinuousRepresentations E (ks ≃ₐ[k] ks)) (f : V ⟶ W)
    (P : Profinite.{u})
    (m : Profinite.CondensedAction.sectionModule (normCoefficients E).toMon
      ((fieldFunctor k ks e).obj (equivalence.inverse.obj V).obj).module P) (p : P),
    sections W P
      (((((fieldFunctor k ks e).map (equivalence.inverse.map f).hom).val).hom.hom.app
        (op P)).hom m) p = f.hom.hom (sections V P m p)


end AlgebraicGeometry.ProEtale.FieldActionTransport
