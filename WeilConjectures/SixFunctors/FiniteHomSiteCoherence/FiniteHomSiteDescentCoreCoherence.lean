/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Finite coefficient Hom coherence on the two actual sites

Small presentations are related to the actual small sites by explicit equivalences.
All functors below are normalized ringed derived pullbacks. In particular no scalar
functor, tensorator, associator, or Hom comparison is an unconstrained parameter.
Source: thm-coef-finite-hom, final evaluation and site-transport paragraph
(blueprint: lem-coef-finite-hom-site-descent-core-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxErrors 8
universe u w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules
open CategoryTheory.RingedDerivedComparisons

namespace WeilConjectures
namespace FiniteHomSiteCoherence

/-- Identity of the underlying topos with the specified structural coefficient map.
The module direct image is scalar restriction, with its unchanged underlying sections.
Source: Stacks 03DA, 07A6
(blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
def scalar {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) where
  inverse := 𝟭 _
  direct := 𝟭 _
  adj := Adjunction.id
  leftExact := inferInstance
  ringMap := (sheafCompose J (CategoryTheory.forget CommRingCat)).map a
  ring_zero := by
    intro T z hz U t
    change (a.hom.app U).hom (z.hom.app U t) = 0
    have h := hz U t
    change z.hom.app U t = (0 : R.obj.obj U) at h
    exact (congrArg (a.hom.app U).hom h).trans (map_zero _)
  ring_one := by
    intro T z hz U t
    change (a.hom.app U).hom (z.hom.app U t) = 1
    have h := hz U t
    change z.hom.app U t = (1 : R.obj.obj U) at h
    exact (congrArg (a.hom.app U).hom h).trans (map_one _)
  ring_add := by
    intro T x y z hz U t
    change (a.hom.app U).hom (z.hom.app U t) =
      @Add.add (S.obj.obj U) inferInstance
        ((a.hom.app U).hom (x.hom.app U t)) ((a.hom.app U).hom (y.hom.app U t))
    have h := hz U t
    change z.hom.app U t =
      @Add.add (R.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t) at h
    exact (congrArg (a.hom.app U).hom h).trans (map_add _ _ _)
  ring_mul := by
    intro T x y z hz U t
    change (a.hom.app U).hom (z.hom.app U t) =
      @Mul.mul (S.obj.obj U) inferInstance
        ((a.hom.app U).hom (x.hom.app U t)) ((a.hom.app U).hom (y.hom.app U t))
    have h := hz U t
    change z.hom.app U t =
      @Mul.mul (R.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t) at h
    exact (congrArg (a.hom.app U).hom h).trans (map_mul _ _ _)
  modules := restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
  additive := inferInstance
  underlying := Iso.refl _
  module_linear := by
    intro M T s x y z hz U t
    have h := hz U t
    change z.hom.app U t = @Add.add (M.val.obj U) inferInstance
      (@SMul.smul (S.obj.obj U) (M.val.obj U) inferInstance
        ((a.hom.app U).hom (s.hom.app U t)) (x.hom.app U t)) (y.hom.app U t) at h
    simp only [Adjunction.homEquiv, Adjunction.id]
    change z.hom.app U t = @Add.add (M.val.obj U) inferInstance
      (@SMul.smul (S.obj.obj U) (M.val.obj U) inferInstance
        ((a.hom.app U).hom (s.hom.app U t)) (x.hom.app U t)) (y.hom.app U t)
    exact h

/-- The canonical tensor comparison of a normalized ringed derived pullback.
Source: Stacks 07A4 (blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
abbrev tensor (s : System.{u, w}) {X Y : Site.{u, w}} (f : Morphism X Y) :=
  (s.lift f).edge.tensorComparison (s.lift f).tensorModelY (s.lift f).tensorModelX

/-- The specified Hom comparison: transpose of pullback of evaluation.
Source: Stacks 08J9 (blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
abbrev comparison (s : System.{u, w}) {X Y : Site.{u, w}}
    (f : Morphism X Y) (K M : Y.D) :=
  coefficientBaseChangeHom Y.closed X.closed (s.lift f).edge.left (tensor s f) K M

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory.{w} (RingedTensorModules.{u, u, u} J R)]

/-- The equations for one specified finite scalar map, including the evaluation formula.
These are equations in the ordinary module derived categories of this very site.
Source: thm-coef-finite-hom, final paragraph
(blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
def Laws (s : System.{u, w}) {R S T : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ T) : Prop :=
  let A := site J R
  let B := site J S
  let D := site J T
  let f := s.lift (X := B) (Y := A) (scalar a)
  let g := s.lift (X := D) (Y := B) (scalar b)
  let α := (scalarComposition J s a b).pullback.symm
  let ι := (scalarIdentity J s R).pullback
  CoefficientEvaluationCompatible A.closed B.closed f.edge.left
      (tensor s (X := B) (Y := A) (scalar a)) ∧
    (∀ K M : A.D,
      B.closed.tensor.map
          (Prod.mkHom (comparison s (X := B) (Y := A) (scalar a) K M) (𝟙 (f.edge.left.obj K))) ≫
          B.closed.evaluation (f.edge.left.obj K) (f.edge.left.obj M) =
        (tensor s (X := B) (Y := A) (scalar a)).inv.app
            ((derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op K, M), K) ≫
          f.edge.left.map (A.closed.evaluation K M)) ∧
    (∀ K M : A.D,
      g.edge.left.map (comparison s (X := B) (Y := A) (scalar a) K M) ≫
          comparison s (X := D) (Y := B) (scalar b) (f.edge.left.obj K) (f.edge.left.obj M) ≫
          (derivedInternalHomOfUniverses.{u, u, u, w} J T).map
            (Prod.mkHom (α.inv.app K).op (α.hom.app M)) =
        α.hom.app ((derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op K, M)) ≫
          comparison s (X := D) (Y := A) (scalar (a ≫ b)) K M) ∧
    (∀ K M : A.D,
      comparison s (X := A) (Y := A) (scalar (𝟙 R)) K M ≫
          (derivedInternalHomOfUniverses.{u, u, u, w} J R).map
            (Prod.mkHom (ι.inv.app K).op (ι.hom.app M)) =
        ι.hom.app ((derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op K, M)))

/-- The induced topology on the chosen small presentation of the actual etale site.
Source: size convention (blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
abbrev etaleTopology {X : AlgebraicGeometry.Scheme.{u}}
    {E : Type (u + 1)} [SmallCategory E] (e : E ≌ X.Etale) :=
  e.functor.inducedTopology X.smallEtaleTopology

/-- The induced topology on the chosen small presentation of the actual pro-etale site.
Source: size convention (blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
abbrev proTopology {X : AlgebraicGeometry.Scheme.{u}}
    {P : Type (u + 1)} [SmallCategory P] (p : P ≌ X.ProEt) :=
  p.functor.inducedTopology (AlgebraicGeometry.Scheme.ProEt.topology X)

/-- The actual geometric inverse image, transported through the two site equivalences.
The middle functor is the left adjoint in `Scheme.proEtaleSiteComparison`.
Source: Stacks 099R, 00WX
(blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
def actualInverse {X : AlgebraicGeometry.Scheme.{u}}
    {E P : Type (u + 1)} [SmallCategory E] [SmallCategory P]
    (e : E ≌ X.Etale) (p : P ≌ X.ProEt) :
    Sheaf (etaleTopology e) (Type (u + 1)) ⥤
      Sheaf (proTopology p) (Type (u + 1)) := by
  letI : e.inverse.IsDenseSubsite X.smallEtaleTopology (etaleTopology e) := by
    change e.symm.functor.IsDenseSubsite X.smallEtaleTopology
      (e.symm.inverse.inducedTopology X.smallEtaleTopology)
    infer_instance
  letI : p.inverse.IsDenseSubsite (AlgebraicGeometry.Scheme.ProEt.topology X) (proTopology p) := by
    change p.symm.functor.IsDenseSubsite (AlgebraicGeometry.Scheme.ProEt.topology X)
      (p.symm.inverse.inducedTopology (AlgebraicGeometry.Scheme.ProEt.topology X))
    infer_instance
  exact (e.sheafCongr (etaleTopology e) X.smallEtaleTopology (Type (u + 1))).functor ⋙
    Functor.sheafPullbackConstruction.sheafPullback (AlgebraicGeometry.Scheme.toProEt X)
      (Type (u + 1)) X.smallEtaleTopology (AlgebraicGeometry.Scheme.ProEt.topology X) ⋙
    (p.sheafCongr (proTopology p) (AlgebraicGeometry.Scheme.ProEt.topology X)
      (Type (u + 1))).inverse

/-- The normalized ordinary derived category with the actual constant coefficient sheaf.
Source: Stacks 03DA (blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
abbrev constantSite {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : CommRingCat.{u})
    [HasDerivedCategory.{w}
      (RingedTensorModules.{u, u, u} J ((constantSheaf J CommRingCat.{u}).obj R))] :=
  site J ((constantSheaf J CommRingCat.{u}).obj R)

end FiniteHomSiteCoherence

open FiniteHomSiteCoherence AlgebraicGeometry

end WeilConjectures
