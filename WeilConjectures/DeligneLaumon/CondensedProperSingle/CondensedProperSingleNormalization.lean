/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedProperOrdinaryZero.CondensedProperOrdinaryZeroComparison
import WeilConjectures.DeligneLaumon.CondensedModule.CondensedProperGermTransportComposition

/-! # Degree-zero normalization of proper condensed Frobenius

Source: the proper comparison and augmentation calculation in steps 2--6 of
lem-a1-condensed-proper-frobenius-germs in the latest blueprint refinement.
(blueprint: lem-a1-condensed-proper-single-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedProperSingle

namespace NativeGerm

/-- Compose a component and a mapped isomorphism with functor variables retained.
Source: component composition in the native one-step Weil transport.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
def composeAt {C B : Type*} [Category C] [Category B]
    (F G : C ⥤ B) (H : C ⥤ C) (α : F ⋙ 𝟭 B ≅ H ⋙ G)
    (M : C) (θ : H.obj M ≅ M) : F.obj M ≅ G.obj M :=
  α.app M ≪≫ G.mapIso θ

/-- The forward map of the generic native transport is the specified composite.
Source: the defining forward maps of trans, app and mapIso, before specialization.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
theorem composeAt_hom {C B : Type*} [Category C] [Category B]
    (F G : C ⥤ B) (H : C ⥤ C) (α : F ⋙ 𝟭 B ≅ H ⋙ G)
    (M : C) (θ : H.obj M ≅ M) :
    (composeAt F G H α M θ).hom = α.hom.app M ≫ G.map θ.hom := rfl


private theorem mapped_naturality {C B E : Type*}
    [Category C] [Category B] [Category E] {F G H : C ⥤ B}
    (α : F ≅ G) (β : G ⟶ H) (P : B ⥤ E) {M N : C} (f : M ⟶ N) :
    P.map (F.map f) ≫ (P.map (α.hom.app N) ≫ P.map (β.app N)) =
      (P.map (α.hom.app M) ≫ P.map (β.app M)) ≫ P.map (H.map f) := by
  rw [← Category.assoc, ← P.map_comp, α.hom.naturality, P.map_comp, Category.assoc,
    ← P.map_comp, β.naturality, P.map_comp, ← Category.assoc]
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {P Y : Scheme.{u}}
  (a : Y ⟶ P)
  (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) ⥤
    Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1}) (condensedRingObj Λ P))
  (α : F ≅ CondensedRing.lowerStar Λ a ⋙ CondensedRing.upperStar Λ (𝟙 P))
  {E : Type v} [Category.{w} E]
  (J : Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1}) (condensedRingObj Λ P) ⥤ E)
/-- The comparison followed by native restriction, with all functors still variables.
Source: the specified proper comparison and stalk projection.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
def arrow
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (z : P ⟶ Y) (hz : z ≫ a = 𝟙 P) :
    J.obj (F.obj M) ⟶ J.obj ((CondensedRing.upperStar Λ z).obj M) :=
  J.map (α.hom.app M) ≫ J.map (CondensedRing.stalkLowerStarProj Λ hz M)
/-- Its native stalk transformation. -/
private def stalk (z : P ⟶ Y) (hz : z ≫ a = 𝟙 P) :
    CondensedRing.lowerStar Λ a ⋙ CondensedRing.upperStar Λ (𝟙 P) ⟶
      CondensedRing.upperStar Λ z where
  app M := CondensedRing.stalkLowerStarProj Λ hz M
  naturality {_M _N} f := CondensedRing.stalkLowerStarProj_naturality Λ hz f
/-- Naturality by pasting comparison naturality and native stalk naturality,
then applying the scalar functor.
Source: the parent naturality argument.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
theorem arrow_naturality
    {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (f : M ⟶ N) (z : P ⟶ Y) (hz : z ≫ a = 𝟙 P) :
    J.map (F.map f) ≫ arrow Λ a F α J N z hz =
      arrow Λ a F α J M z hz ≫ J.map ((CondensedRing.upperStar Λ z).map f) := by
  exact mapped_naturality α (stalk Λ a z hz) J f

private theorem map_germ_square {B E : Type*} [Category B] [Category E]
    (P : B ⥤ E) {A : E} {X Y Z : B} (f : A ⟶ A) (c : A ⟶ P.obj X)
    (o : X ⟶ X) (p : X ⟶ Y) (q : X ⟶ Z) (t : Z ⟶ Y)
    (hc : f ≫ c = c ≫ P.map o) (hp : o ≫ p = q ≫ t) :
    f ≫ (c ≫ P.map p) = (c ≫ P.map q) ≫ P.map t := by
  rw [← Category.assoc, hc, Category.assoc, ← P.map_comp, hp, P.map_comp, ← Category.assoc]

/-- A scalar comparison square and native stalk square give the germ equation.
Source: associativity, functoriality and the two specified commuting squares.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
theorem arrow_intertwines
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (z z' : P ⟶ Y) (hz : z ≫ a = 𝟙 P) (hz' : z' ≫ a = 𝟙 P)
    (f : J.obj (F.obj M) ⟶ J.obj (F.obj M))
    (o : (CondensedRing.upperStar Λ (𝟙 P)).obj ((CondensedRing.lowerStar Λ a).obj M) ⟶
      (CondensedRing.upperStar Λ (𝟙 P)).obj ((CondensedRing.lowerStar Λ a).obj M))
    (t : (CondensedRing.upperStar Λ z').obj M ⟶ (CondensedRing.upperStar Λ z).obj M)
    (T : J.obj ((CondensedRing.upperStar Λ z').obj M) ⟶
      J.obj ((CondensedRing.upperStar Λ z).obj M))
    (hc : f ≫ (J.mapIso (α.app M)).hom =
      (J.mapIso (α.app M)).hom ≫ J.map o)
    (hp : o ≫ CondensedRing.stalkLowerStarProj Λ hz M =
      CondensedRing.stalkLowerStarProj Λ hz' M ≫ t) (hT : T = J.map t) :
    f ≫ arrow Λ a F α J M z hz = arrow Λ a F α J M z' hz' ≫ T := by
  dsimp only [arrow]
  rw [hT]
  exact map_germ_square J f (J.map (α.hom.app M)) o _ _ t hc hp

end NativeGerm

/-- Point sections with their explicit native module category fixed once.
Source: exactly CondensedRing.pointSections; this changes only its category presentation.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
def scalarSections (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] :
    Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of k))) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l)) :=
  CondensedRing.pointSections l k


variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] [IsAlgClosed k]
  {Y : Scheme.{u}} (a : Y ⟶ Spec (.of k)) [IsProper a]

/-- The proper degree-zero module cohomology functor, fixed before scalar evaluation.
Source: proper compact cohomology of the single sheaf in the parent node.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
abbrev cohomology :=
    DerivedCategory.singleFunctor (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) Y)) 0 ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.padicAlgClRingObj l) (Compactification.ofIsProper a) ⋙
        DerivedCategory.homologyFunctor
          (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
            (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of k)))) 0

omit [IsAlgClosed k] in
omit [IsAlgClosed k] in
/-- Naturality of the specified comparison, with the section functor written explicitly.
Source: naturality of proper comparison and degree-zero augmentation.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
theorem comparison_naturality {M N : CondensedModule.Modules l Y} (f : M ⟶ N) :
    (cohomology l k a).map f ≫
        (comparison l k a).hom.app N =
      (comparison l k a).hom.app M ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (𝟙 (Spec (.of k)))).map
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) a).map f) := by
  simpa only [Functor.comp_map] using (comparison l k a).hom.naturality f


/-- Compact sections with all functor categories fixed once.
Source: proper degree-zero compact cohomology in the parent node.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
def sections :=
  cohomology l k a ⋙ scalarSections l k

/-- The proper germ with its native scalar target, before finite-field specialization.
Source: comparison followed by the actual native stalk projection.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
def nativeEvaluation (M : CondensedModule.Modules l Y) (z : Spec (.of k) ⟶ Y)
    (hz : z ≫ a = 𝟙 _) :
    (sections l k a).obj M ⟶
      (scalarSections l k).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M) :=
  NativeGerm.arrow (Profinite.padicAlgClRingObj l) a (cohomology l k a)
    (comparison l k a) (scalarSections l k) M z hz

omit [IsAlgClosed k] in
/-- Native germ naturality before finite-field specialization.
Source: apply the generic native comparison-and-restriction naturality square.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
theorem nativeEvaluation_naturality {M N : CondensedModule.Modules l Y} (f : M ⟶ N)
    (z : Spec (.of k) ⟶ Y) (hz : z ≫ a = 𝟙 _) :
    (sections l k a).map f ≫ nativeEvaluation l k a N z hz =
      nativeEvaluation l k a M z hz ≫ (scalarSections l k).map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f) := by
  exact NativeGerm.arrow_naturality (Profinite.padicAlgClRingObj l) a
    (cohomology l k a) (comparison l k a) (scalarSections l k) f z hz

/-- The native germ with the finite-field fibre constant retained in its target.
Source: specialization before taking the geometric fibre of a scheme.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
def finiteEvaluation (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ Spec (.of D.k)) [IsProper a]
    (M : CondensedModule.Modules l T) (z : Spec (.of D.k) ⟶ T) (hz : z ≫ a = 𝟙 _) :
    (sections l D.k a).obj M ⟶ CondensedModule.fibre l D M z :=
  nativeEvaluation l D.k a M z hz

/-- Naturality with the finite-field fibre presentation fixed before specialization.
Source: native germ naturality.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
theorem finiteEvaluation_naturality
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ Spec (.of D.k)) [IsProper a]
    {M N : CondensedModule.Modules l T} (f : M ⟶ N)
    (z : Spec (.of D.k) ⟶ T) (hz : z ≫ a = 𝟙 _) :
    (sections l D.k a).map f ≫ finiteEvaluation l D a N z hz =
      finiteEvaluation l D a M z hz ≫ (scalarSections l D.k).map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f) := by
  exact nativeEvaluation_naturality l D.k a f z hz

/-- The native germ square with the finite-field fibre presentation retained.
Source: paste the scalar comparison and native stalk square before geometric specialization.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
theorem finiteEvaluation_intertwines
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ Spec (.of D.k)) [IsProper a]
    (M : CondensedModule.Modules l T) (z z' : Spec (.of D.k) ⟶ T)
    (hz : z ≫ a = 𝟙 _) (hz' : z' ≫ a = 𝟙 _)
    (f : End ((sections l D.k a).obj M))
    (o : End ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (𝟙 (Spec (.of D.k)))).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) a).obj M)))
    (t : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z').obj M ⟶
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M)
    (b : CondensedModule.fibre l D M z' ⟶ CondensedModule.fibre l D M z)
    (hc : f ≫ ((scalarSections l D.k).mapIso ((comparison l D.k a).app M)).hom =
      ((scalarSections l D.k).mapIso ((comparison l D.k a).app M)).hom ≫
        (scalarSections l D.k).map o)
    (hp : o ≫ CondensedRing.stalkLowerStarProj (Profinite.padicAlgClRingObj l) hz M =
      CondensedRing.stalkLowerStarProj (Profinite.padicAlgClRingObj l) hz' M ≫ t)
    (hb : b = (CondensedRing.pointSections l D.k).map t) :
    f ≫ finiteEvaluation l D a M z hz = finiteEvaluation l D a M z' hz' ≫ b := by
  exact NativeGerm.arrow_intertwines (Profinite.padicAlgClRingObj l) a
    (cohomology l D.k a) (comparison l D.k a) (scalarSections l D.k)
    M z z' hz hz' f o t b hc hp hb

/-- The native transport isomorphism with its point-source object fixed before sections.
Source: the point comparison followed by pullback of the Weil isomorphism.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
def finiteTransportIso
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (g : T ⟶ T) (M : CondensedModule.Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).obj M ≅ M)
    (z z' : Spec (.of D.k) ⟶ T) (h : z ≫ g = (frobeniusPointIso D).hom ≫ z') :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z').obj M ≅
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M :=
  NativeGerm.composeAt (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z')
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g)
    (CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
      (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
        (frobeniusPointIso D).hom) g h) M θ

/-- Project the generic native transport before specializing its functors. -/
private theorem finiteTransportIso_native_hom
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (g : T ⟶ T) (M : CondensedModule.Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).obj M ≅ M)
    (z z' : Spec (.of D.k) ⟶ T) (h : z ≫ g = (frobeniusPointIso D).hom ≫ z') :
    (finiteTransportIso l D g M θ z z' h).hom =
      (CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
        (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
          (frobeniusPointIso D).hom) g h).hom.app M ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map θ.hom := by
  unfold finiteTransportIso
  exact NativeGerm.composeAt_hom
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z')
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g)
    (CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
      (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
        (frobeniusPointIso D).hom) g h) M θ

/-- The actual initial transport is the scalar image of the native isomorphism.
Source: the proved initial transport formula, before taking its forward map.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
theorem finiteTransportIso_eq
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (g : T ⟶ T) (M : CondensedModule.Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).obj M ≅ M)
    (z z' : Spec (.of D.k) ⟶ T) (h : z ≫ g = (frobeniusPointIso D).hom ≫ z') :
    CondensedModule.transport l D g M θ z z' 0 h =
      (CondensedRing.pointSections l D.k).mapIso (finiteTransportIso l D g M θ z z' h) := by
  exact CondensedModule.properGerm_transport_zero l D g M θ z z' h

/-- Scalar transport as the map of the forward arrow of the native isomorphism.
Source: project the whole initial transport equality to its forward map.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
theorem finiteTransportIso_hom
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (g : T ⟶ T) (M : CondensedModule.Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).obj M ≅ M)
    (z z' : Spec (.of D.k) ⟶ T) (h : z ≫ g = (frobeniusPointIso D).hom ≫ z') :
    (CondensedModule.transport l D g M θ z z' 0 h).hom =
      (CondensedRing.pointSections l D.k).map (finiteTransportIso l D g M θ z z' h).hom := by
  exact congrArg Iso.hom (finiteTransportIso_eq l D g M θ z z' h)

private theorem finiteWeil_stalk_square
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    [IsIso (frobeniusPointIso D).hom]
    {T : Scheme.{u}} (a : T ⟶ Spec (.of D.k))
    (g : T ⟶ T) [IsIso g] (w : g ≫ a = a ≫ (frobeniusPointIso D).hom)
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l) g)
    (z z' : Spec (.of D.k) ⟶ T) (hz : z ≫ a = 𝟙 _) (hz' : z' ≫ a = 𝟙 _)
    (h : z ≫ g = (frobeniusPointIso D).hom ≫ z') :
    CondensedProperOrdinaryZero.ordinary l D.k a g (frobeniusPointIso D).hom w M ≫
        CondensedRing.stalkLowerStarProj (Profinite.padicAlgClRingObj l) hz M.carrier =
      CondensedRing.stalkLowerStarProj (Profinite.padicAlgClRingObj l) hz' M.carrier ≫
        (finiteTransportIso l D g M.carrier M.str z z' h).hom := by
  rw [finiteTransportIso_native_hom, CategoryTheory.Endofunctor.IsoAlgebra.str_hom]
  exact CondensedProperOrdinaryZero.ordinary_stalk_compatibility l D.k a g
    (frobeniusPointIso D).hom w M z z' hz hz' h

private theorem finiteWeil_transport_square
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (g : T ⟶ T)
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l) g)
    (z z' : Spec (.of D.k) ⟶ T)
    (h : z ≫ g = (frobeniusPointIso D).hom ≫ z') :
    (CondensedModule.transport l D g M.carrier M.str z z' 0 h).hom =
      (CondensedRing.pointSections l D.k).map
        (finiteTransportIso l D g M.carrier M.str z z' h).hom := by
  exact finiteTransportIso_hom l D g M.carrier M.str z z' h

/-- Finite-field one-step germ square before choosing a geometric fibre.
Source: paste the canonical comparison, native ordinary stalk square and actual transport.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
theorem finiteEvaluation_weil_square
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    [IsIso (frobeniusPointIso D).hom]
    {T : Scheme.{u}} (a : T ⟶ Spec (.of D.k)) [IsProper a]
    (g : T ⟶ T) [IsIso g] (w : g ≫ a = a ≫ (frobeniusPointIso D).hom)
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l) g)
    (z z' : Spec (.of D.k) ⟶ T) (hz : z ≫ a = 𝟙 _) (hz' : z' ≫ a = 𝟙 _)
    (h : z ≫ g = (frobeniusPointIso D).hom ≫ z')
    (f : End ((sections l D.k a).obj M.carrier))
    (hc : f ≫ ((scalarSections l D.k).mapIso ((comparison l D.k a).app M.carrier)).hom =
      ((scalarSections l D.k).mapIso ((comparison l D.k a).app M.carrier)).hom ≫
        (scalarSections l D.k).map
          (CondensedProperOrdinaryZero.ordinary l D.k a g (frobeniusPointIso D).hom w M)) :
    f ≫ finiteEvaluation l D a M.carrier z hz =
      finiteEvaluation l D a M.carrier z' hz' ≫
        (CondensedModule.transport l D g M.carrier M.str z z' 0 h).hom := by
  exact finiteEvaluation_intertwines l D a M.carrier z z' hz hz' f
    (CondensedProperOrdinaryZero.ordinary l D.k a g (frobeniusPointIso D).hom w M)
    (finiteTransportIso l D g M.carrier M.str z z' h).hom
    (CondensedModule.transport l D g M.carrier M.str z z' 0 h).hom hc
    (finiteWeil_stalk_square l D a g w M z z' hz hz' h)
    (finiteWeil_transport_square l D g M z z' h)

/-- Proper augmentation after cancelling the inserted identity pullback.
Source: proper comparison and degree-zero augmentation.
(blueprint: lem-a1-condensed-proper-single-normalization). -/
def sectionsComparison (M : CondensedModule.Modules l Y) :
    (sections l k a).obj M ≅ (scalarSections l k).obj
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) a).obj M) :=
  (scalarSections l k).mapIso
    ((comparison l k a).app M ≪≫
      (CondensedRing.upperStarId (Profinite.padicAlgClRingObj l)
        (Spec (.of k))).app
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) a).obj M))

omit [IsAlgClosed k] in
variable (g : Y ⟶ Y) [IsIso g]
  (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h] (w : g ≫ a = a ≫ h)

private theorem map_square_composite {C B : Type*} [Category C] [Category B]
    (F : C ⥤ B) {X Y : C} {Z : B} (f : X ⟶ X) (o : Y ⟶ Y) (c : X ⟶ Y)
    (d : F.obj Y ⟶ Z) (p : Z ⟶ Z) (hc : f ≫ c = c ≫ o)
    (hd : F.map o ≫ d = d ≫ p) :
    F.map f ≫ (F.map c ≫ d) = (F.map c ≫ d) ≫ p := by
  rw [← Category.assoc, ← F.map_comp, hc, F.map_comp, Category.assoc, hd,
    ← Category.assoc]

private theorem map_intertwines {B E : Type*} [Category B] [Category E]
    (P : B ⥤ E) {X Y : B} (f : X ⟶ X) (g : Y ⟶ Y) (c : X ⟶ Y)
    (e : f ≫ c = c ≫ g) : P.map f ≫ P.map c = P.map c ≫ P.map g := by
  rw [← P.map_comp, e, P.map_comp]

end WeilConjectures.CondensedProperSingle
