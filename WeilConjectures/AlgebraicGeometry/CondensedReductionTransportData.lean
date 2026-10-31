/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedWeilReality
public import WeilConjectures.AlgebraicGeometry.CondensedFibresExact
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
/-! # Reduction on the actual condensed constructible Weil heart

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md, paragraph 6 and final paragraph
(blueprint: def-zl-condensed-reduction-transport-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedReduction

/-- Reduction with its inherited morphism to the fixed finite field.
Source: Stacks 01J4; blueprint reduction paragraph
(blueprint: def-zl-condensed-reduction-transport-data). -/
def model {S : Scheme.{u}} (X₀ : Over S) : Over S :=
  Over.mk (X₀.left.nilradical.subschemeι ≫ X₀.hom)

/-- The actual reduction immersion over the finite base.
Source: Stacks 01J4 (blueprint: def-zl-condensed-reduction-transport-data). -/
def immersion {S : Scheme.{u}} (X₀ : Over S) : model X₀ ⟶ X₀ :=
  Over.homMk X₀.left.nilradical.subschemeι

/-- Finite type is inherited by the reduction closed subscheme.
Source: Stacks 01J4 (blueprint: def-zl-condensed-reduction-transport-data). -/
instance model_ft {S : Scheme.{u}} (X₀ : Over S) [LocallyOfFiniteType X₀.hom] :
    LocallyOfFiniteType (model X₀).hom :=
  inferInstanceAs (LocallyOfFiniteType (X₀.left.nilradical.subschemeι ≫ X₀.hom))

/-- Quasi-compactness is inherited by the reduction closed subscheme.
Source: Stacks 01J4 (blueprint: def-zl-condensed-reduction-transport-data). -/
instance model_qc {S : Scheme.{u}} (X₀ : Over S) [QuasiCompact X₀.hom] :
    QuasiCompact (model X₀).hom :=
  inferInstanceAs (QuasiCompact (X₀.left.nilradical.subschemeι ≫ X₀.hom))

/-- Separatedness is inherited by the reduction closed subscheme.
Source: Stacks 01J4 (blueprint: def-zl-condensed-reduction-transport-data). -/
instance model_sep {S : Scheme.{u}} (X₀ : Over S) [IsSeparated X₀.hom] :
    IsSeparated (model X₀).hom :=
  inferInstanceAs (IsSeparated (X₀.left.nilradical.subschemeι ≫ X₀.hom))

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- Base change of the specified reduction immersion to the algebraic closure.
Source: blueprint reduction paragraph
(blueprint: def-zl-condensed-reduction-transport-data). -/
def geometricImmersion : (D.geometricFiber (model X₀)).left ⟶ (D.geometricFiber X₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
    (immersion X₀)).left

/-- The constructible fixed-pair heart uses precisely the existing constant-model
constructibility predicate and the existing actual Weil-module category.
Source: blueprint reduction paragraph (blueprint: def-zl-condensed-reduction-transport-data). -/
abbrev heart := ObjectProperty.FullSubcategory
  (fun M : CondensedWeil.WeilModule D l X₀ ↦
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)

/-- The faithful inclusion in the actual module category.
Source: blueprint reduction paragraph (blueprint: def-zl-condensed-reduction-transport-data). -/
def forget : heart D l X₀ ⥤ CondensedModule.Modules l (D.geometricFiber X₀).left :=
  ObjectProperty.ι _ ⋙ IsoAlgebra.forget _


/-- The module inverse image of the actual geometric reduction immersion.
Source: blueprint reduction paragraph (blueprint: def-zl-condensed-reduction-transport-data). -/
abbrev pull :
    CondensedModule.Modules l (D.geometricFiber X₀).left ⥤
      CondensedModule.Modules l (D.geometricFiber (model X₀)).left :=
  CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (geometricImmersion D X₀)

/-- The module direct image of the actual geometric reduction immersion.
Source: blueprint reduction paragraph (blueprint: def-zl-condensed-reduction-transport-data). -/
abbrev push :
    CondensedModule.Modules l (D.geometricFiber (model X₀)).left ⥤
      CondensedModule.Modules l (D.geometricFiber X₀).left :=
  CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
    (geometricImmersion D X₀)

/-- The specified module adjunction, rather than a newly chosen adjunction.
Source: blueprint reduction paragraph (blueprint: def-zl-condensed-reduction-transport-data). -/
@[irreducible] def moduleAdjunction : pull D l X₀ ⊣ push D l X₀ :=
  CondensedRing.upperStarLowerStarAdjunction
    (Profinite.padicAlgClRingObj l) (geometricImmersion D X₀)

/-- Geometric Frobenius inverse image in the actual module category.
Source: blueprint geometric Frobenius convention
(blueprint: def-zl-condensed-reduction-transport-data). -/
abbrev frobenius :
    CondensedModule.Modules l (D.geometricFiber X₀).left ⥤
      CondensedModule.Modules l (D.geometricFiber X₀).left :=
  CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (D.geometricFrobenius X₀).hom

/-- The commuting square of the geometric reduction and geometric Frobenius.
Source: blueprint reduction paragraph (blueprint: def-zl-condensed-reduction-transport-data). -/
def Commutes : Prop :=
  geometricImmersion D X₀ ≫ (D.geometricFrobenius X₀).hom =
    (D.geometricFrobenius (model X₀)).hom ≫ geometricImmersion D X₀

/-- The pullback comparison is exactly the two canonical compositors and the
commuting-square identification, in the order FP -> QF.
Source: blueprint reduction paragraph, DAG proof step 5
(blueprint: def-zl-condensed-reduction-transport-data). -/
@[irreducible] def comparison (h : Commutes D X₀) :
    frobenius D l X₀ ⋙ pull D l X₀ ≅ pull D l X₀ ⋙ frobenius D l (model X₀) :=
  (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l)
    (geometricImmersion D X₀) (D.geometricFrobenius X₀).hom).symm ≪≫
  CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) h ≪≫
  CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l)
    (D.geometricFrobenius (model X₀)).hom (geometricImmersion D X₀)

/-- The ordinary constructible-heart equivalence, normalized on both functors and
on the actual module adjunction. Equalities after the inclusions specify the actions
on objects and arrows; HEq only accounts for these equal carrier types.
Source: blueprint reduction paragraph, DAG proof steps 2--4
(blueprint: def-zl-condensed-reduction-transport-data). -/
structure ModuleEquivalence where
  source_abelian : Abelian (ConstantModelConstructible (Profinite.padicAlgClRingObj l)
    (D.geometricFiber X₀).left)
  target_abelian : Abelian (ConstantModelConstructible (Profinite.padicAlgClRingObj l)
    (D.geometricFiber (model X₀)).left)
  inverseImage : ConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left ⥤
    ConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber (model X₀)).left
  directImage : ConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber (model X₀)).left ⥤
    ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber X₀).left
  inverseImage_eq : inverseImage ⋙ ObjectProperty.ι _ =
    ObjectProperty.ι _ ⋙ pull D l X₀
  directImage_eq : directImage ⋙ ObjectProperty.ι _ =
    ObjectProperty.ι _ ⋙ push D l X₀
  adjunction : inverseImage ⊣ directImage
  unit_eq : ∀ M, HEq ((ObjectProperty.ι _).map (adjunction.unit.app M))
    ((moduleAdjunction D l X₀).unit.app M.obj)
  counit_eq : ∀ N, HEq ((ObjectProperty.ι _).map (adjunction.counit.app N))
    ((moduleAdjunction D l X₀).counit.app N.obj)
  unit_iso : ∀ M, IsIso (adjunction.unit.app M)
  counit_iso : ∀ N, IsIso (adjunction.counit.app N)
  inverseImage_limits : PreservesFiniteLimits inverseImage
  inverseImage_colimits : PreservesFiniteColimits inverseImage
  directImage_limits : PreservesFiniteLimits directImage
  directImage_colimits : PreservesFiniteColimits directImage
  inverseImage_additive : inverseImage.Additive
  directImage_additive : directImage.Additive

/-- The component formula for the adjoint Frobenius mate, written in abstract
categories so the module implementations do not expand in the equivalence structure.
Source: blueprint reduction paragraph, DAG proof step 6
(blueprint: def-zl-condensed-reduction-transport-data). -/
@[irreducible] def mateComponent {C : Type u₁} [Category.{v₁} C]
    {B : Type u₂} [Category.{v₂} B]
    {F : C ⥤ B} {G : B ⥤ C} (a : F ⊣ G) (P : C ⥤ C) (Q : B ⥤ B)
    (b : P ⋙ F ≅ F ⋙ Q) (N : B) : P.obj (G.obj N) ⟶ G.obj (Q.obj N) :=
  a.unit.app (P.obj (G.obj N)) ≫ G.map (b.hom.app (G.obj N)) ≫
    G.map (Q.map (a.counit.app N))

set_option maxHeartbeats 2000000 in
-- The concrete fixed-pair categories require extra kernel reduction for this structure.
/-- The lifted equivalence uses the actual inverse image, the actual direct image
and its adjoint Frobenius mate. The mate's component equation determines it uniquely.
The lifted unit and counit have precisely the underlying module unit and counit.
Source: blueprint reduction paragraph, DAG proof steps 5--7
(blueprint: def-zl-condensed-reduction-transport-data). -/
structure WeilEquivalence (h : Commutes D X₀) where
  source_abelian : Abelian (heart D l X₀)
  target_abelian : Abelian (heart D l (model X₀))
  pushComparison : push D l X₀ ⋙ frobenius D l X₀ ≅
    frobenius D l (model X₀) ⋙ push D l X₀
  pushComparison_eq : ∀ N, pushComparison.hom.app N =
    mateComponent (moduleAdjunction D l X₀) (frobenius D l X₀)
      (frobenius D l (model X₀)) (comparison D l X₀ h) N
  inverseImage : heart D l X₀ ⥤ heart D l (model X₀)
  directImage : heart D l (model X₀) ⥤ heart D l X₀
  inverseImage_eq : inverseImage ⋙ ObjectProperty.ι _ =
    ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso (comparison D l X₀ h).symm
  directImage_eq : directImage ⋙ ObjectProperty.ι _ =
    ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso pushComparison
  adjunction : inverseImage ⊣ directImage
  unit_eq : ∀ M, HEq ((forget D l X₀).map (adjunction.unit.app M))
    ((moduleAdjunction D l X₀).unit.app M.obj.carrier)
  counit_eq : ∀ N, HEq ((forget D l (model X₀)).map (adjunction.counit.app N))
    ((moduleAdjunction D l X₀).counit.app N.obj.carrier)
  unit_iso : ∀ M, IsIso (adjunction.unit.app M)
  counit_iso : ∀ N, IsIso (adjunction.counit.app N)
  inverseImage_limits : PreservesFiniteLimits inverseImage
  inverseImage_colimits : PreservesFiniteColimits inverseImage
  directImage_limits : PreservesFiniteLimits directImage
  directImage_colimits : PreservesFiniteColimits directImage
  inverseImage_additive : inverseImage.Additive
  directImage_additive : directImage.Additive

/-- The actual scalar fibre as a functor on the constructible Weil heart.
Source: blueprint local-fibre clause (blueprint: def-zl-condensed-reduction-transport-data). -/
def closedFibreFunctor (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    heart D l X₀ ⥤ ModuleCat.{u + 1} (PadicAlgCl l) :=
  forget D l X₀ ⋙ CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (localClosedPoint D X₀ x i hi) ⋙ CondensedQbarGeometricEvaluation.fieldFiber D.k l

/-- Canonical inverse-image composition gives the natural fibre identification.
Source: blueprint reduction paragraph, DAG proof step 8
(blueprint: def-zl-condensed-reduction-transport-data). -/
@[irreducible] def fibreComparison {Y Z : Scheme.{u}} (r : Z ⟶ Y)
    (z : Spec (.of D.k) ⟶ Z) (y : Spec (.of D.k) ⟶ Y) (h : z ≫ r = y) :
    CondensedRing.upperStar (Profinite.padicAlgClRingObj l) r ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        CondensedQbarGeometricEvaluation.fieldFiber D.k l ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj l) y ⋙
        CondensedQbarGeometricEvaluation.fieldFiber D.k l :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) z r).symm ≪≫
        CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) h) _

set_option maxHeartbeats 2000000 in
-- Checking the concrete scalar-fibre comparison types requires extra definitional reduction.
/-- Closed points and residue fields are unchanged. Both fibre identifications are
natural and intertwine the local geometric Frobenius itself. The forward comparison
is normalized by composition; the inverse is that comparison followed by the counit.
Source: blueprint reduction paragraph, DAG proof step 8
(blueprint: def-zl-condensed-reduction-transport-data). -/
def LocalCompatibility {h : Commutes D X₀} (E : WeilEquivalence D l X₀ h) : Prop :=
  (∃ e : {y : (model X₀).left // y ∈ closedPoints (model X₀).left} ≃
      {x : X₀.left // x ∈ closedPoints X₀.left},
    ∀ y, (e y).val = (immersion X₀).left y.val) ∧
  (∀ y : {y : (model X₀).left // y ∈ closedPoints (model X₀).left},
    IsIso ((immersion X₀).left.residueFieldMap y.val) ∧
    Nat.card (X₀.left.residueField ((immersion X₀).left y.val)) =
      Nat.card ((model X₀).left.residueField y.val)) ∧
  ∀ (y : {y : (model X₀).left // y ∈ closedPoints (model X₀).left})
    (hx : (immersion X₀).left y.val ∈ closedPoints X₀.left)
    (i : X₀.left.residueField ((immersion X₀).left y.val) →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap ((immersion X₀).left y.val)) =
      algebraMap D.k₀ D.k)
    (j : (model X₀).left.residueField y.val →+* D.k)
    (hj : j.comp ((model X₀).hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k),
    i = j.comp ((immersion X₀).left.residueFieldMap y.val).hom →
    ∃ hp : localClosedPoint D (model X₀) y j hj ≫ geometricImmersion D X₀ =
        localClosedPoint D X₀ ⟨(immersion X₀).left y.val, hx⟩ i hi,
    ∃ e : E.inverseImage ⋙ closedFibreFunctor D l (model X₀) y j hj ≅
        closedFibreFunctor D l X₀ ⟨(immersion X₀).left y.val, hx⟩ i hi,
      (∀ M, HEq (e.hom.app M)
        ((fibreComparison D l (geometricImmersion D X₀)
          (localClosedPoint D (model X₀) y j hj)
          (localClosedPoint D X₀ ⟨(immersion X₀).left y.val, hx⟩ i hi) hp).hom.app
          M.obj.carrier)) ∧
      (∀ M, e.hom.app M ≫
          CondensedWeil.closedOperator D l X₀ M.obj ⟨(immersion X₀).left y.val, hx⟩ i hi =
        CondensedWeil.closedOperator D l (model X₀) (E.inverseImage.obj M).obj y j hj ≫
          e.hom.app M) ∧
      ∃ d : E.directImage ⋙
          closedFibreFunctor D l X₀ ⟨(immersion X₀).left y.val, hx⟩ i hi ≅
            closedFibreFunctor D l (model X₀) y j hj,
        (∀ N, d.hom.app N = e.inv.app (E.directImage.obj N) ≫
          (closedFibreFunctor D l (model X₀) y j hj).map (E.adjunction.counit.app N)) ∧
        ∀ N, d.hom.app N ≫ CondensedWeil.closedOperator D l (model X₀) N.obj y j hj =
          CondensedWeil.closedOperator D l X₀ (E.directImage.obj N).obj
            ⟨(immersion X₀).left y.val, hx⟩ i hi ≫ d.hom.app N

/-- Reality, purity at every real weight, and mixedness at every specified upper bound
are preserved and reflected in both directions, using the actual condensed predicates.
Source: blueprint reduction paragraph and final filtration paragraph, DAG proof step 9
(blueprint: def-zl-condensed-reduction-transport-data). -/
def NumericalCompatibility {h : Commutes D X₀} (E : WeilEquivalence D l X₀ h)
    (iota : PadicAlgCl l ≃+* ℂ) : Prop :=
  (∀ (M : heart D l X₀) (w : ℝ),
    (CondensedWeil.Real D l (model X₀) (E.inverseImage.obj M).obj iota.toRingHom ↔
      CondensedWeil.Real D l X₀ M.obj iota.toRingHom) ∧
    (CondensedWeil.Pure D l (model X₀) (E.inverseImage.obj M).obj iota.toRingHom w ↔
      CondensedWeil.Pure D l X₀ M.obj iota.toRingHom w) ∧
    (CondensedWeil.Mixed D l (model X₀) (E.inverseImage.obj M).obj iota.toRingHom w ↔
      CondensedWeil.Mixed D l X₀ M.obj iota.toRingHom w)) ∧
  ∀ (N : heart D l (model X₀)) (w : ℝ),
    (CondensedWeil.Real D l X₀ (E.directImage.obj N).obj iota.toRingHom ↔
      CondensedWeil.Real D l (model X₀) N.obj iota.toRingHom) ∧
    (CondensedWeil.Pure D l X₀ (E.directImage.obj N).obj iota.toRingHom w ↔
      CondensedWeil.Pure D l (model X₀) N.obj iota.toRingHom w) ∧
    (CondensedWeil.Mixed D l X₀ (E.directImage.obj N).obj iota.toRingHom w ↔
      CondensedWeil.Mixed D l (model X₀) N.obj iota.toRingHom w)

/-- A pure quotient is a constructible Weil module with the cokernel universal
property in actual ordinary Weil modules. This avoids selecting a particular cokernel;
all such coforks are uniquely isomorphic, so the pure weight is unchanged.
Source: blueprint final paragraph (blueprint: def-zl-condensed-reduction-transport-data). -/
def PureQuotient {A B : heart D l X₀} (f : A ⟶ B)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) : Prop :=
  ∃ (Q : heart D l X₀) (π : B.obj ⟶ Q.obj)
    (h : (ObjectProperty.ι _).map f ≫ π = 0),
    Nonempty (IsColimit (CokernelCofork.ofπ π h)) ∧
      CondensedWeil.Pure D l X₀ Q.obj iota w

/-- Applying either exact equivalence to an individual finite mixed filtration
retains its monomorphisms and each assigned quotient weight, including a common bound.
Source: blueprint final paragraph, DAG proof step 10
(blueprint: def-zl-condensed-reduction-transport-data). -/
def ImageFiltrations (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (T : heart D l X₀ ⥤ heart D l Y₀) (iota : PadicAlgCl l →+* ℂ) : Prop :=
  ∀ (n : ℕ) (G : Fin (n + 1) ⥤ heart D l X₀) (weights : Fin n → ℝ) (w : ℝ),
    IsZero (G.obj 0) →
    (∀ (a b : Fin (n + 1)) (hab : a ≤ b), Mono (G.map (homOfLE hab))) →
    (∀ s : Fin n, weights s ≤ w ∧ PureQuotient D l X₀
      (G.map (homOfLE s.castSucc_le_succ)) iota (weights s)) →
    IsZero (T.obj (G.obj 0)) ∧
    (∀ (a b : Fin (n + 1)) (hab : a ≤ b), Mono (T.map (G.map (homOfLE hab)))) ∧
    (∀ s : Fin n, PureQuotient D l Y₀
      (T.map (G.map (homOfLE s.castSucc_le_succ))) iota (weights s)) ∧
    CondensedWeil.Mixed D l Y₀ (T.obj (G.obj (Fin.last n))).obj iota w

/-- Every prescribed filtration of the inverse image is carried back through the
actual direct image and the actual unit. The endpoint square specifies precisely its
identification with the original module; each quotient retains its assigned weight.
Source: blueprint final paragraph, DAG proof step 10
(blueprint: def-zl-condensed-reduction-transport-data). -/
def UnitFiltrations {h : Commutes D X₀} (E : WeilEquivalence D l X₀ h)
    (iota : PadicAlgCl l →+* ℂ) : Prop :=
  ∀ (M : heart D l X₀) (n : ℕ) (G : Fin (n + 1) ⥤ heart D l (model X₀))
    (last : G.obj (Fin.last n) ≅ E.inverseImage.obj M) (weights : Fin n → ℝ) (w : ℝ),
    IsZero (G.obj 0) →
    (∀ (a b : Fin (n + 1)) (hab : a ≤ b), Mono (G.map (homOfLE hab))) →
    (∀ s : Fin n, weights s ≤ w ∧ PureQuotient D l (model X₀)
      (G.map (homOfLE s.castSucc_le_succ)) iota (weights s)) →
    ∃ (P : Fin (n + 1) ⥤ heart D l X₀) (c : P ≅ G ⋙ E.directImage)
      (finish : P.obj (Fin.last n) ≅ M),
      finish.hom ≫ E.adjunction.unit.app M =
        c.hom.app (Fin.last n) ≫ E.directImage.map last.hom ∧
      IsZero (P.obj 0) ∧
      (∀ (a b : Fin (n + 1)) (hab : a ≤ b), Mono (P.map (homOfLE hab))) ∧
      (∀ s : Fin n, PureQuotient D l X₀
        (P.map (homOfLE s.castSucc_le_succ)) iota (weights s)) ∧
      CondensedWeil.Mixed D l X₀ M.obj iota w

end WeilConjectures.CondensedReduction
