/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingClosure
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.Paper.LocalizingAdmissibleCoefficients
import Sheaf.Paper.OpenImmersionLocalizing
import Mathlib.Algebra.Ring.Shrink
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Paper.CondensedAmbientExchangeTriangulated
import all Sheaf.Paper.FiniteProperExchange
import all Sheaf.Paper.FiniteProperBaseChange
import Sheaf.SixFunctors.FiniteCtfInternalEtaleRealization
import all Sheaf.Paper.FiniteDiscreteEncodingCompactification
import Sheaf.Paper.LocalizingClosureExistence
import all Sheaf.Paper.UnboundedLocalizingPullback
import Sheaf.CategoryTheory.Triangulated.LocalizingSubcategoryUniverse
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarCoproducts

/-!
# Finite-coefficient proper direct image on the localizing categories

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.md
(blueprint: det-ctf-finite-proper-localizing).

The finite ring is represented canonically by its finite discrete condensed ring.
All subcategories in the statements are the recorded constant-model constructible
finite-Tor predicate and `localizingClosureProEtale`; the functors are the published
module-object six functors, and the base-change map is the recorded ambient exchange
`CondensedRing.condensedAmbientExchange`. Thus the statements retain the specified
coefficient identification while using the recorded condensed objects.

## Main definitions

* `finiteDiscreteCondensedCoefficient`: the condensed ring of a finite discrete ring.
* `finiteCoefficientLocalizingProperties`: the Dctf, localizing-restriction, exactness
  and sum clauses for a module-object derived functor.

## Main statements

* `finiteProperLocalizing`: clause (1).
* `finiteProperLocalizing_baseChange`: clause (2).
* `finiteOpenLocalizing`: the extension-by-zero part of clause (3).
* `finiteCompactificationLocalizing`: the compactification part of clause (3).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor CategoryTheory.Obj CategoryTheory.MonoidalClosed

namespace AlgebraicGeometry.ProEtale

-- Keep the recorded generating predicate abstract across the tensor-instance caches.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteProper_recordedClosure_localizing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    IsLocalizingSubcategory (localizingClosureProEtale Λ X) := by
  exact (localizingClosure_exists Λ X _).2.2.2.1

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteProper_generator_in_closure
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : ConstantModelConstructibleFiniteTor Λ X) :
    localizingClosureProEtale Λ X M.obj := by
  intro P hP hS
  exact hS M.obj M.property

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteProper_recordedClosure_elim
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hP : IsLocalizingSubcategory P)
    (hgen : ∀ M : ConstantModelConstructibleFiniteTor Λ X, P M.obj)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : localizingClosureProEtale Λ X K) : P K := by
  exact hK P hP (fun M hM ↦ hgen ⟨M, hM⟩)

end AlgebraicGeometry.ProEtale

section PrivateComparisonProofs

attribute [local instance] finiteProperCache1 finiteProperCache2 finiteProperCache3
  finiteProperCache4 finiteProperCache5 finiteProperCache6 finiteProperCache7
  finiteProperCache8 finiteProperCache9 finiteProperCache10 finiteProperCache11 finiteProperCache12
  cachedModuleMonoidal cachedModuleBraided cachedModuleSymmetric cachedDerivedMonoidal
  cachedModuleClosed cachedModuleFlatResolution cachedDerivedTensorStructure

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [-instance] CategoryTheory.sfbSheafTensor_monoidalPreadditive
attribute [-instance] CategoryTheory.sfbSheafTensor_hasWeakSheafify

section TensorInstanceCache

variable (T : AlgebraicGeometry.Scheme.{u})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]

private theorem cachedTensorFour :
    ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod
      (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R)),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by infer_instance

private theorem cachedTensorLeft :
    ∀ (X₁ X₂ X₃ : GradedObject ℤ (Mod
      (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R)),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance

private theorem cachedTensorRight :
    ∀ (X₁ X₂ X₃ : GradedObject ℤ (Mod
      (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R)),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance

private theorem cachedTensorColimLeft :
    ∀ M : Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R,
      PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor _).obj M) := by
  intro M
  infer_instance

private theorem cachedTensorColimRight :
    ∀ M : Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R,
      PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor _).flip.obj M) := by
  intro M
  infer_instance

omit [IsCommMonObj R] in
private theorem cachedExactIntegerColimits :
    HasExactColimitsOfShape ℤ
      (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R) := by
  infer_instance

end TensorInstanceCache

attribute [local instance] cachedTensorFour cachedTensorLeft cachedTensorRight
  cachedTensorColimLeft cachedTensorColimRight cachedExactIntegerColimits

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem iso_intersection_localizing
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (L : ObjectProperty C) (hloc : IsLocalizingSubcategory L)
    {F G : C ⥤ D} (η : F ⟶ G) [η.isoLocus.IsTriangulated]
    (hsums : ∀ (I : Type u) (J : Discrete I ⥤ L.FullSubcategory),
      PreservesColimit (J ⋙ L.ι) F ∧
        PreservesColimit (J ⋙ L.ι) G) : IsLocalizingSubcategory (L ⊓ η.isoLocus) := by
  let P : ObjectProperty C := L ⊓ η.isoLocus
  let : L.IsTriangulated := hloc.1
  let : L.IsClosedUnderIsomorphisms := hloc.2.1
  change IsLocalizingSubcategory P
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I J hJ hK
  let := hJ
  refine ⟨hloc.2.2 J hJ (fun i ↦ (hK i).1), ?_⟩
  let J' : Discrete I ⥤ L.FullSubcategory := L.lift J (fun i ↦ (hK i.as).1)
  have hF := (hsums I J').1
  have hG := (hsums I J').2
  have : PreservesColimit J F := hF
  have : PreservesColimit J G := hG
  have : ∀ j, IsIso ((Functor.whiskerLeft J η).app j) := fun j ↦ (hK j.as).2
  have : IsIso (Functor.whiskerLeft J η) := NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit J η _ (colimit.isColimit J)

private theorem preserves_composite
    {C D E J : Type*} [Category* C] [Category* D] [Category* E] [Category* J]
    (K : J ⥤ C) {F : C ⥤ D} {G : D ⥤ E}
    (hF : PreservesColimit K F) (hG : PreservesColimit (K ⋙ F) G) :
    PreservesColimit K (F ⋙ G) := by
  letI := hF
  letI := hG
  exact comp_preservesColimit F G

private theorem maps_localizingClosure
    {C D : Type u} [Category.{v} C] [Category.{v'} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (S : ObjectProperty C) (T : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    (P : ObjectProperty C) (hP : IsLocalizingSubcategory P)
    (hT : IsLocalizingSubcategory (localizingClosure T))
    (hgen : ∀ K, S K → P K)
    (hpres : ∀ K, S K → T (F.obj K))
    (hsums : ∀ (I : Type u) (J : Discrete I ⥤ C),
      (∀ i : I, P (J.obj ⟨i⟩)) → PreservesColimit J F) :
    ∀ K, localizingClosure S K → localizingClosure T (F.obj K) := by
  let Q := localizingClosure T
  letI : P.IsTriangulated := hP.1
  letI : P.IsClosedUnderIsomorphisms := hP.2.1
  letI : Q.IsTriangulated := hT.1
  letI : Q.IsClosedUnderIsomorphisms := hT.2.1
  let R := P ⊓ Q.inverseImage F
  have hR : IsLocalizingSubcategory R := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I J hJ hJR
    letI := hJ
    letI := hsums I J (fun i ↦ (hJR i).1)
    exact ⟨hP.2.2 J hJ (fun i ↦ (hJR i).1),
      Q.prop_of_iso (preservesColimitIso F J).symm
        (hT.2.2 (J ⋙ F) inferInstance (fun i ↦ (hJR i).2))⟩
  intro K hK
  exact (hK R hR (fun L hL ↦ ⟨hgen L hL,
    fun V _ hV ↦ hV _ (hpres L hL)⟩)).2

private theorem preserves_on_subcategory
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {I : Type*} (P : ObjectProperty C) [HasColimitsOfShape (Discrete I) C]
    [P.IsClosedUnderColimitsOfShape (Discrete I)]
    (e : C ≌ C') (t : D ≌ D') (F : C ⥤ D) (G : C' ⥤ D')
    (i : F ⋙ t.functor ≅ e.functor ⋙ G)
    (hs : ∀ (M : I → C), (∀ j, P (M j)) →
      PreservesColimit (Discrete.functor (fun j ↦ e.functor.obj (M j))) G) :
    PreservesColimitsOfShape (Discrete I) (P.ι ⋙ F) := by
  constructor
  intro J
  let M := fun j : I ↦ J.obj ⟨j⟩
  have hJ : Discrete.functor M ≅ J := Discrete.natIso (fun _ ↦ Iso.refl _)
  suffices h : PreservesColimit (Discrete.functor M) (P.ι ⋙ F) by
    letI := h
    exact preservesColimit_of_iso_diagram (P.ι ⋙ F) hJ
  letI := hs (fun j ↦ (M j).obj) (fun j ↦ (M j).property)
  letI : PreservesColimit (Discrete.functor M ⋙ P.ι ⋙ e.functor) G :=
    preservesColimit_of_iso_diagram
      (K₁ := Discrete.functor (fun j ↦ e.functor.obj (M j).obj))
      G (Discrete.natIso (fun _ ↦ Iso.refl _))
  letI : PreservesColimit (Discrete.functor M) (P.ι ⋙ e.functor) :=
    comp_preservesColimit P.ι e.functor
  letI : PreservesColimit (Discrete.functor M) ((P.ι ⋙ e.functor) ⋙ G) :=
    comp_preservesColimit _ _
  letI : PreservesColimit (Discrete.functor M) ((P.ι ⋙ F) ⋙ t.functor) :=
    preservesColimit_of_natIso _
      ((Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft P.ι i.symm ≪≫
        (Functor.associator _ _ _).symm)
  exact preservesColimit_of_reflects_of_preserves (P.ι ⋙ F) t.functor

private theorem transported_generator
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (S : ObjectProperty C) (T : ObjectProperty D) (Q : ObjectProperty E)
    [Q.IsClosedUnderIsomorphisms] (e : S.FullSubcategory ≌ T.FullSubcategory)
    (V : C ⥤ E) (F : D ≌ E)
    (i : e.functor ⋙ T.ι ≅ S.ι ⋙ V ⋙ F.inverse)
    (hV : ∀ L, S L → Q (V.obj L)) (K : T.FullSubcategory) :
    Q (F.functor.obj K.obj) := by
  let L := e.inverse.obj K
  let j : F.inverse.obj (V.obj L.obj) ≅ K.obj :=
    (i.app L).symm ≪≫ T.ι.mapIso (e.counitIso.app K)
  exact Q.prop_of_iso
    ((F.counitIso.app (V.obj L.obj)).symm ≪≫ F.functor.mapIso j)
    (hV L.obj L.property)

namespace AlgebraicGeometry.ProEtale

open CondensedRing

attribute [local instance] unboundedLocalizingPullbackCommShift

attribute [local irreducible] CondensedRing.lowerStar CondensedRing.upperStar
  upperStarFromPoint DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.monoidalCategoryStruct
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local irreducible] CondensedRing.condensedAmbientExchange
  CondensedRing.condensedAmbientPullbackComparison CondensedRing.leftDerivedUpperStarComp
  CondensedRing.derivedUpperStarLowerStarAdjunction

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem ordinary_preserves_coproduct
    (B : Type (u + 1)) [CommRing B] [Finite B] {k : Type u} [Field k]
    {Z T : Scheme.{u}} (f : Z ⟶ T) [IsProper f]
    (aZ : Z ⟶ Spec (.of k)) (aT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [LocallyOfFiniteType aT] [QuasiCompact aT] (hf : f ≫ aT = aZ)
    {I : Type (u + 1)}
    (M : I → _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} B)))
    (hM : ∀ i, DerivedCategory.etaleOriginHomology B Z (M i)) :
    PreservesColimit (Discrete.functor M)
      (lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor := by
  letI := isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology
    B f aZ aT hf M hM
  exact PreservesCoproduct.of_iso_comparison _ M

private theorem encoding_triangulated
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (T : Scheme.{u}) (e : FiniteDiscreteOrdinary.Encoding A T) :
    e.fixedDerived.functor.IsTriangulated := by
  change (e.ordinary.functor ⋙ e.fixed.functor).mapDerivedCategory.IsTriangulated
  infer_instance

set_option maxHeartbeats 30000 in
-- Transport the specified fixed-interval equivalence.
private theorem encoding_generator_etaleOrigin
    (ℓ p : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [CharP k p] (hp : 0 < p) (hne : p ≠ ℓ)
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T)
    (T : Over (Spec (.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (K : ConstantModelConstructibleFiniteTor (FiniteDiscreteOrdinary.coefficient A) T.left) :
    DerivedCategory.etaleOriginHomology (ULift.{u + 1} A) T.left
      ((E T.left).fixedDerived.functor.obj K.obj) := by
  obtain ⟨a, b, htor⟩ := K.property.2
  obtain ⟨hreal, _⟩ := FiniteDiscreteOrdinary.finiteCtfInternalEtaleRealization
    ℓ p k hp hne A E
  obtain ⟨eT, ⟨heT⟩⟩ := hreal T (min a b) b (min_le_right _ _)
  exact transported_generator _ _
    (DerivedCategory.etaleOriginHomology (ULift.{u + 1} A) T.left) eT
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T.left).mapDerivedCategory
    (E T.left).fixedDerived heT
    (fun C _ ↦ DerivedCategory.etaleOriginHomology_mapDerivedCategory_obj C)
    ⟨K.obj, K.property.1, htor.mono (min_le_left _ _) le_rfl⟩

attribute [local irreducible] FiniteDiscreteOrdinary.Encoding.fixedDerived

end AlgebraicGeometry.ProEtale
end PrivateComparisonProofs

attribute [local instance] cachedTensorFour cachedTensorLeft cachedTensorRight
  cachedTensorColimLeft cachedTensorColimRight cachedExactIntegerColimits

namespace AlgebraicGeometry.ProEtale

open CondensedRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The condensed ring of a finite discrete commutative ring: the continuous-map
condensed ring `S ↦ C(S, A)` for the discrete topology on `A`.
Source: blueprint det-ctf-finite-proper-localizing, statement, coefficient
identification of lem-weil-pbc-finite-discrete-condensed-ring-constant
(blueprint: det-ctf-finite-proper-localizing). -/
noncomputable def finiteDiscreteCondensedCoefficient (A : Type u) [CommRing A] [Finite A] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := by infer_instance
  exact Profinite.continuousMapRingObjOfUniverse.{u, u} A

/-- The canonical monoid structure on the finite discrete condensed coefficient, the
published pointwise ring-object structure of the continuous-map condensed ring.
Source: blueprint det-ctf-finite-proper-localizing, statement, coefficient
identification (blueprint: det-ctf-finite-proper-localizing). -/
noncomputable instance finiteDiscreteCondensedCoefficient_monObj
    (A : Type u) [CommRing A] [Finite A] :
    MonObj (finiteDiscreteCondensedCoefficient A) := by
  unfold finiteDiscreteCondensedCoefficient
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := by infer_instance
  exact Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A

/-- Commutativity of the canonical finite discrete condensed coefficient.
Source: blueprint det-ctf-finite-proper-localizing, statement, coefficient
identification (blueprint: det-ctf-finite-proper-localizing). -/
noncomputable instance finiteDiscreteCondensedCoefficient_isCommMonObj
    (A : Type u) [CommRing A] [Finite A] :
    IsCommMonObj (finiteDiscreteCondensedCoefficient A) := by
  unfold finiteDiscreteCondensedCoefficient
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := by infer_instance
  letI : MonObj (Profinite.continuousMapRingObjOfUniverse.{u, u} A) :=
    Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A
  exact Profinite.isCommMonObj_continuousMapRingObjOfUniverse.{u, u} A

/-- The Dctf and localizing-restriction clauses for a module-object derived functor `F`:
`F` maps `Dctf(X)` into `Dctf(Y)` (the recorded `constantModelBoundedConstructible` and
finite Tor amplitude), maps `Loc(Dctf(X))` into `Loc(Dctf(Y))` (the recorded
`localizingClosureProEtale`), sends distinguished triangles of the source closure to
distinguished triangles (exactness of the restriction), and preserves every small
coproduct of objects of the source closure (the empty one included).
Source: blueprint det-ctf-finite-proper-localizing, statement, clauses (1) and (3)
(blueprint: det-ctf-finite-proper-localizing). -/
def finiteCoefficientLocalizingProperties
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}}
    (F : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ⥤
      DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)))
    [F.CommShift ℤ] : Prop :=
  (∀ K, (constantModelBoundedConstructible Λ X K ∧
      DerivedCategory.finiteTorAmplitude _ K) →
    (constantModelBoundedConstructible Λ Y (F.obj K) ∧
      DerivedCategory.finiteTorAmplitude _ (F.obj K))) ∧
  (∀ K, localizingClosureProEtale Λ X K →
    localizingClosureProEtale Λ Y (F.obj K)) ∧
  (∀ T : Triangle
      (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))),
    T ∈ distTriang _ →
    localizingClosureProEtale Λ X T.obj₁ →
    localizingClosureProEtale Λ X T.obj₂ →
    localizingClosureProEtale Λ X T.obj₃ →
      F.mapTriangle.obj T ∈ distTriang _) ∧
  (∀ (I : Type (u + 2))
    (D : Discrete I ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))),
    (∀ i : I, localizingClosureProEtale Λ X (D.obj ⟨i⟩)) →
      PreservesColimit D F)

open scoped CategoryTheory.MonoidalClosed in
/-- Finite rings in any universe have a small discrete model. Postcomposition with the
ring equivalence induces an isomorphism of continuous-map ring sheaves, hence of their
ring objects. The annihilating power of `ℓ` transports along this same equivalence.
Source: blueprint det-ctf-finite-proper-localizing, proof steps 1 and 16, and
sk-def-localizing-closure, finite-coefficient convention
(blueprint: det-ctf-finite-proper-localizing). -/
private theorem finiteDiscreteCoefficient_admissible
    (ℓ : ℕ) [Fact ℓ.Prime] (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 1 ≤ n ∧ (ℓ ^ n : ℕ) • (1 : A) = 0) :
    IsLocalizingAdmissibleCoefficient ℓ (finiteDiscreteCondensedCoefficient A) := by
  classical
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := by infer_instance
  let B := Shrink.{0} A
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  letI : IsTopologicalRing B := by infer_instance
  let e : A ≃+* B := (Shrink.ringEquiv.{0} A).symm
  let h : Profinite.continuousMapRingSheafOfUniverse.{u, u} A ⟶
      Profinite.continuousMapRingSheaf.{u} B :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.toRingHom.compLeftContinuous S.unop (continuous_of_discreteTopology)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let v : Profinite.continuousMapRingSheaf.{u} B ⟶
      Profinite.continuousMapRingSheafOfUniverse.{u, u} A :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.symm.toRingHom.compLeftContinuous S.unop (continuous_of_discreteTopology)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let E : Profinite.continuousMapRingSheafOfUniverse.{u, u} A ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    { hom := h
      inv := v
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let E' := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso E
  letI : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
  let eh := presheaf_enrichedHoms_exist
    (C := Profinite.{u}) (A := Ab.{u + 1})
  letI : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}),
    Enriched.FunctorCategory.HasEnrichedHom Ab.{u + 1} F G := eh.1
  letI : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}),
    Enriched.FunctorCategory.HasFunctorEnrichedHom Ab.{u + 1} F G := eh.2
  letI : ((coherentTopology Profinite.{u}).W (A := Ab.{u + 1})).IsMonoidal :=
    GrothendieckTopology.W.monoidal
  letI hmon : IsMonHom E'.hom := Sheaf.isMonHom_sheafCompose_map _ E.hom
  refine Or.inl ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ⟨Mon.mkIso' E'⟩⟩
  obtain ⟨n, _, hn⟩ := hA
  refine ⟨n, fun b ↦ ?_⟩
  have hn' : (ℓ ^ n : ℕ) • (1 : B) = 0 := by
    simpa only [map_nsmul, map_one, map_zero] using congrArg e hn
  simpa only [nsmul_eq_mul, mul_one, zero_mul] using congrArg (fun x : B ↦ x * b) hn'

attribute [local instance] unboundedLocalizingPullbackCommShift

attribute [local instance] finiteProperCache1 finiteProperCache2 finiteProperCache3
  finiteProperCache4 finiteProperCache5 finiteProperCache6 finiteProperCache7
  finiteProperCache8 finiteProperCache9 finiteProperCache10 finiteProperCache11 finiteProperCache12
  cachedModuleMonoidal cachedModuleBraided cachedModuleSymmetric cachedDerivedMonoidal
  cachedModuleClosed cachedModuleFlatResolution cachedDerivedTensorStructure

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [-instance] CategoryTheory.sfbSheafTensor_monoidalPreadditive
attribute [-instance] CategoryTheory.sfbSheafTensor_hasWeakSheafify

attribute [local irreducible] CondensedRing.lowerStar CondensedRing.upperStar
  upperStarFromPoint DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.monoidalCategoryStruct
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local irreducible] CondensedRing.condensedAmbientExchange
  CondensedRing.condensedAmbientPullbackComparison CondensedRing.leftDerivedUpperStarComp
  CondensedRing.derivedUpperStarLowerStarAdjunction

attribute [local irreducible] FiniteDiscreteOrdinary.Encoding.fixedDerived

namespace CondensedRing

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteProper_exchange_eq_ambient
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :
    condensedAmbientExchange Λ sq = finiteProperExchange Λ sq.toCommSq := by
  unfold condensedAmbientExchange finiteProperExchange
  unfold condensedAmbientPullbackComparison finitePullbackSquare
  rw [finitePullbackCongr_eqToIso]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The explicit identity identification of the two finite-discrete coefficient models.
Its data are the identity monoid isomorphism, with no choice of an existence witness. -/
@[irreducible] private noncomputable def finiteProperCoefficientIso
    (A : Type u) [CommRing A] [Finite A] :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    letI : IsTopologicalRing A := by infer_instance
    Mon.mk (finiteDiscreteCondensedCoefficient A) ≅
      Mon.mk (FiniteDiscreteOrdinary.coefficient A) := by
  exact Iso.refl _

-- Keep the ordinary and internal encoding constructions abstract, as in their comparison API.
attribute [local irreducible] FiniteDiscreteOrdinary.coefficientEncoding
  ProEtale.derivedBaseChangeMap ProEtale.upperStar ProEtale.lowerStar
  ProEtale.derivedUpperStarLowerStarAdjunction ProEtale.leftDerivedUpperStarComp

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteProper_generator_exchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (e : Mon.mk Λ ≅ Mon.mk (FiniteDiscreteOrdinary.coefficient A))
    (E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    {X' Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsProper f]
    (sq : ChosenCartesianSquare g' f' f g)
    (M : ConstantModelConstructibleFiniteTor Λ X) :
    IsIso ((condensedAmbientExchange Λ sq).app M.obj) := by
  let SX : Over (Spec (.of k)) := Over.mk (X ↘ Spec (.of k))
  letI : LocallyOfFiniteType SX.hom := ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
  letI : QuasiCompact SX.hom := ‹QuasiCompact (X ↘ Spec (.of k))›
  letI : IsSeparated SX.hom := ‹IsSeparated (X ↘ Spec (.of k))›
  let origin := (coefficientEncoding_etaleOrigin (R := Λ) A ℓ k e E SX M).some
  let α := ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} A))
    sq.toCommSq
  have hα : IsIso (α.app
      ((FiniteDiscreteOrdinary.coefficientEncoding A e X (E X)).obj M.obj)) :=
    (NatTrans.isIso_app_iff_of_iso α origin.2.2.2.val).1
      (ordinary_exchange_of_etale (ULift.{u + 1} A) sq origin.1 origin.2.2.2.property.1)
  rw [finiteProper_exchange_eq_ambient Λ sq]
  exact (FiniteDiscreteOrdinary.finiteCoefficientExchangeEncoding_isIso
    A e E sq M.obj).2 hα

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteProper_generator_specialization
    (A : Type u) [CommRing A] [Finite A]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    {X' Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsProper f]
    (sq : ChosenCartesianSquare g' f' f g)
    (M : ConstantModelConstructibleFiniteTor (finiteDiscreteCondensedCoefficient A) X) :
    IsIso ((condensedAmbientExchange (finiteDiscreteCondensedCoefficient A) sq).app M.obj) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := by infer_instance
  exact finiteProper_generator_exchange (finiteDiscreteCondensedCoefficient A) A ℓ k
    (finiteProperCoefficientIso A)
    (fun T ↦ (FiniteDiscreteOrdinary.encoding_exists A T).some) X sq M

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteProper_pullback_localizing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X' X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace X'] [QuasiSeparatedSpace X']
    (g' : X' ⟶ X) :
    ∀ M, localizingClosureProEtale Λ X M →
      localizingClosureProEtale Λ X'
        ((CondensedRing.upperStar Λ g').leftDerivedFunctor.obj M) := by
  obtain ⟨hg'⟩ := pullback_of_constructible Λ g' (pullback_constructible Λ g')
  exact fun M hM ↦ hg'.localizing ⟨M, hM⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteProper_localizing_exchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (hf : finiteCoefficientLocalizingProperties Λ
      (CondensedRing.lowerStar Λ f).rightDerivedFunctor)
    (hf' : finiteCoefficientLocalizingProperties Λ
      (CondensedRing.lowerStar Λ f').rightDerivedFunctor)
    (hmap : ∀ M, localizingClosureProEtale Λ X M →
      localizingClosureProEtale Λ X'
        ((CondensedRing.upperStar Λ g').leftDerivedFunctor.obj M))
    (hgen : ∀ M : ConstantModelConstructibleFiniteTor Λ X,
      IsIso ((condensedAmbientExchange Λ sq).app M.obj))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : localizingClosureProEtale Λ X K) :
    IsIso ((condensedAmbientExchange Λ sq).app K) := by
  let L := localizingClosureProEtale Λ X
  let β := condensedAmbientExchange Λ sq
  have hloc : IsLocalizingSubcategory L :=
    finiteProper_recordedClosure_localizing Λ X
  letI : β.isoLocus.IsTriangulated := condensedAmbientExchange_isoLocus_triangulated Λ sq
  have hsums : ∀ (I : Type (u + 2)) (J : Discrete I ⥤ L.FullSubcategory),
      PreservesColimit (J ⋙ L.ι)
          ((CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
            (CondensedRing.upperStar Λ g).leftDerivedFunctor) ∧
      PreservesColimit (J ⋙ L.ι)
          ((CondensedRing.upperStar Λ g').leftDerivedFunctor ⋙
            (CondensedRing.lowerStar Λ f').rightDerivedFunctor) := by
    intro I J
    let D := J ⋙ L.ι
    have hD : ∀ i : I, L (D.obj ⟨i⟩) := fun i ↦ (J.obj ⟨i⟩).property
    have hpull : PreservesColimitsOfSize.{u + 2, u + 2}
        (CondensedRing.upperStar Λ g).leftDerivedFunctor :=
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ g).leftAdjoint_preservesColimits
    refine ⟨preserves_composite D (hf.2.2.2 I D hD)
      hpull.preservesColimitsOfShape.preservesColimit, ?_⟩
    have h₁ : PreservesColimit D (CondensedRing.upperStar Λ g').leftDerivedFunctor :=
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ g').leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape.preservesColimit
    have h₂ := hf'.2.2.2 I (D ⋙ (CondensedRing.upperStar Λ g').leftDerivedFunctor)
      (fun i ↦ hmap (D.obj ⟨i⟩) (hD i))
    exact preserves_composite D h₁ h₂
  let P := L ⊓ β.isoLocus
  have hP : IsLocalizingSubcategory P := iso_intersection_localizing L hloc β hsums
  have hPgen : ∀ M : ConstantModelConstructibleFiniteTor Λ X, P M.obj :=
    fun M ↦ ⟨finiteProper_generator_in_closure Λ X M, hgen M⟩
  exact (finiteProper_recordedClosure_elim Λ X P hP hPgen K hK).2

end CondensedRing

section Setting

variable (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : 0 < p) (hpℓ : p ≠ ℓ)
  (k : Type u) [Field k] [CharP k p]
  (A : Type u) [CommRing A] [Finite A]
  (hA : ∃ n : ℕ, 1 ≤ n ∧ (ℓ ^ n : ℕ) • (1 : A) = 0)
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]

include hℓ hp hpℓ hA k

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 60000 in
-- Keep the canonical derived functors abstract during elaboration.
/-- Clause (1): proper pushforward preserves the recorded finite-coefficient Dctf and
restricts to an exact sum-preserving functor of the localizing closures.
Source: blueprint sk-prop-ctf-finite-proper-localizing, clause (1)
(blueprint: det-ctf-finite-proper-localizing).

Proof:
1. Use the normalized section-action equivalence for the finite discrete ring. Its
   derived equivalence identifies each internal Dctf generator with an etale realization,
   by `finiteCtfInternalEtaleRealization` for a fixed ordered Tor interval.
2. Pull back the replete triangulated property of having etale-origin cohomology along
   that equivalence. Exact coproducts make it localizing at the Hom universe; an existing
   larger coproduct has small nonzero support, so it is localizing in the object universe.
3. The source theorem
   `isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology` gives coproduct
   preservation on that subcategory. Transport through `encodingDerivedPushforwardIso`,
   reflect the colimit through the target equivalence, and extend to larger index sets
   by the same small-support argument.
4. `continuous_finiteProper_preserves` supplies Dctf preservation. Intersect the classical
   subcategory with the inverse image of the target localizing closure. This intersection
   is replete, triangulated, and closed under all existing ambient coproducts by step 3.
   It contains the generators, hence contains their localizing closure. The ordinary
   right derived functor is triangulated, giving the asserted exactness. -/
theorem finiteProperLocalizing (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] :
    finiteCoefficientLocalizingProperties (finiteDiscreteCondensedCoefficient A)
      (f)_*⟦finiteDiscreteCondensedCoefficient A⟧.rightDerivedFunctor := by
  classical
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  letI : Fact (ringChar k).Prime :=
    ⟨by simpa only [ringChar.eq k p] using
      ((CharP.char_is_prime_or_zero k p).resolve_right (Nat.ne_of_gt hp))⟩
  letI : Fact (ringChar k ≠ ℓ) := ⟨by simpa only [ringChar.eq k p] using hpℓ⟩
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := by infer_instance
  change finiteCoefficientLocalizingProperties (FiniteDiscreteOrdinary.coefficient A)
    (CondensedRing.lowerStar (FiniteDiscreteOrdinary.coefficient A) f).rightDerivedFunctor
  let SX : Over (Spec (.of k)) := Over.mk (X ↘ Spec (.of k))
  let SY : Over (Spec (.of k)) := Over.mk (Y ↘ Spec (.of k))
  letI : LocallyOfFiniteType SX.hom := ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
  letI : QuasiCompact SX.hom := ‹QuasiCompact (X ↘ Spec (.of k))›
  letI : IsSeparated SX.hom := ‹IsSeparated (X ↘ Spec (.of k))›
  letI : LocallyOfFiniteType SY.hom := ‹LocallyOfFiniteType (Y ↘ Spec (.of k))›
  letI : QuasiCompact SY.hom := ‹QuasiCompact (Y ↘ Spec (.of k))›
  letI : IsSeparated SY.hom := ‹IsSeparated (Y ↘ Spec (.of k))›
  let E (T : Scheme.{u}) := (FiniteDiscreteOrdinary.encoding_exists A T).some
  let P : ObjectProperty (DerivedCategory (FiniteDiscreteOrdinary.Internal A X)) :=
    (DerivedCategory.etaleOriginHomology (ULift.{u + 1} A) X).inverseImage
      (E X).fixedDerived.functor
  have hPsmall : P.IsTriangulated := by
    let : (E X).fixedDerived.functor.IsTriangulated := encoding_triangulated A X (E X)
    dsimp only [P]
    infer_instance
  have hPiso : P.IsClosedUnderIsomorphisms := by dsimp only [P]; infer_instance
  have hP : IsLocalizingSubcategory P := by
    let := hPsmall
    let := hPiso
    apply isLocalizingSubcategory_of_locallySmall.{u + 1}
    refine ⟨hPsmall, hPiso, ?_⟩
    intro I D hD hobj
    letI := hD
    exact (DerivedCategory.etaleOriginHomology (ULift.{u + 1} A) X).prop_of_isColimit
      (isColimitOfPreserves (E X).fixedDerived.functor (colimit.isColimit D))
      (fun i ↦ hobj i.as)
  have hgen : ∀ K, (constantModelBoundedConstructible
      (FiniteDiscreteOrdinary.coefficient A) X K ∧
      _root_.DerivedCategory.finiteTorAmplitude (FiniteDiscreteOrdinary.Internal A X) K) →
      P K := by
    intro K hK
    exact encoding_generator_etaleOrigin ℓ p k hp hpℓ A E SX ⟨K, hK⟩
  let F := (CondensedRing.lowerStar (FiniteDiscreteOrdinary.coefficient A) f).rightDerivedFunctor
  let G := (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctor
  let i : F ⋙ (E Y).fixedDerived.functor ≅ (E X).fixedDerived.functor ⋙ G :=
    FiniteDiscreteOrdinary.encodingDerivedPushforwardIso A f (E Y) (E X)
  have hs : ∀ (I : Type (u + 1)), PreservesColimitsOfShape (Discrete I) (P.ι ⋙ F) := by
    intro I
    letI : HasColimitsOfShape (Discrete I)
        (DerivedCategory (FiniteDiscreteOrdinary.Internal A X)) :=
      Adjunction.hasColimitsOfShape_of_equivalence (E X).fixedDerived.functor
    let : P.IsClosedUnderColimitsOfShape (Discrete (ULift.{u + 2} I)) :=
      ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
        rintro _ ⟨D, hD⟩
        exact hP.2.2 D inferInstance (fun j ↦ hD ⟨j⟩))
    let : P.IsClosedUnderColimitsOfShape (Discrete I) :=
      ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
        (Discrete.equivalence Equiv.ulift)
    apply preserves_on_subcategory P (E X).fixedDerived (E Y).fixedDerived F G i
    intro M hM
    exact ordinary_preserves_coproduct (ULift.{u + 1} A) f
      (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) (by simp) _ hM
  have hslarge (I : Type (u + 2)) :
      PreservesColimitsOfShape (Discrete I) (P.ι ⋙ F) :=
    preservesCoproducts_of_small (P.ι ⋙ F) hs I
  have hsums (I : Type (u + 2))
      (D : Discrete I ⥤ DerivedCategory (FiniteDiscreteOrdinary.Internal A X))
      (hD : ∀ i : I, P (D.obj ⟨i⟩)) : PreservesColimit D F := by
    apply PreservesColimit.mk'
    intro hcol
    let := hcol
    let := hP.2.1
    let : P.IsClosedUnderColimitsOfShape (Discrete I) :=
      ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
        rintro _ ⟨D, hD⟩
        exact hP.2.2 D inferInstance (fun j ↦ hD ⟨j⟩))
    let L := P.lift D (fun j ↦ hD j.as)
    let := hslarge I
    letI : HasColimit (L ⋙ P.ι) := hcol
    letI : CreatesColimit L P.ι :=
      createsColimitFullSubcategoryInclusionOfClosed (Discrete I) P L
    letI : HasColimit L := hasColimit_of_created L P.ι
    letI : PreservesColimit L (P.ι ⋙ F) :=
      (hslarge I).preservesColimit
    have hh := isColimitOfPreserves (P.ι ⋙ F) (colimit.isColimit L)
    exact preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves P.ι (colimit.isColimit L)) hh
  let ff : SX ⟶ SY := Over.homMk f (by
    change f ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k)
    exact comp_over f _)
  letI : IsProper ff.left := ‹IsProper f›
  have hpres := CondensedRing.continuous_finiteProper_preserves A ℓ
    (by obtain ⟨n, _, hn⟩ := hA; exact ⟨n, hn⟩) k
    SX SY ff
  have hQ := (localizingClosure_exists (FiniteDiscreteOrdinary.coefficient A) Y
    (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) Y ⊓
      fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K)).2.2.2.1
  letI : F.IsTriangulated := inferInstance
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    exact hpres ⟨K, hK⟩
  · exact maps_localizingClosure
      (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X ⊓
        fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M)
      (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) Y ⊓
        fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M) F P hP hQ hgen
      (fun K hK ↦ hpres ⟨K, hK⟩) hsums
  · intro T hT _ _ _
    exact Functor.map_distinguished _ T hT
  · intro I D hD
    exact hsums I D (fun i ↦ hD i P hP hgen)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 150000 in
-- Cache the full proof before exposing the public theorem.
private theorem finiteProperLocalizing_baseChange_proof
    {X' Y' : Scheme.{u}} [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [IsSeparated (X' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))] [IsProper f]
    (sq : ChosenCartesianSquare g' f' f g)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (finiteDiscreteCondensedCoefficient A) X)))
    (hK : localizingClosureProEtale (finiteDiscreteCondensedCoefficient A) X K) :
    IsIso ((condensedAmbientExchange (finiteDiscreteCondensedCoefficient A) sq).app K) := by
  classical
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  letI : Fact (ringChar k).Prime :=
    ⟨by simpa only [ringChar.eq k p] using
      ((CharP.char_is_prime_or_zero k p).resolve_right (Nat.ne_of_gt hp))⟩
  letI : Fact (ringChar k ≠ ℓ) := ⟨by simpa only [ringChar.eq k p] using hpℓ⟩
  have hcart : IsPullback g' f' f g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  letI : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) hcart inferInstance
  have hf : finiteCoefficientLocalizingProperties (finiteDiscreteCondensedCoefficient A)
      (CondensedRing.lowerStar (finiteDiscreteCondensedCoefficient A) f).rightDerivedFunctor := by
    as_aux_lemma =>
      exact finiteProperLocalizing ℓ p hℓ hp hpℓ k A hA f
  have hf' : finiteCoefficientLocalizingProperties (finiteDiscreteCondensedCoefficient A)
      (CondensedRing.lowerStar (finiteDiscreteCondensedCoefficient A) f').rightDerivedFunctor := by
    as_aux_lemma =>
      exact finiteProperLocalizing ℓ p hℓ hp hpℓ k A hA f'
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  letI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace
    (X' ↘ Spec (.of k))
  letI : QuasiSeparatedSpace X :=
    (quasiSeparated_iff_quasiSeparatedSpace (X ↘ Spec (.of k))).mp inferInstance
  letI : QuasiSeparatedSpace X' :=
    (quasiSeparated_iff_quasiSeparatedSpace (X' ↘ Spec (.of k))).mp inferInstance
  have hmap := by
    as_aux_lemma =>
      exact finiteProper_pullback_localizing (finiteDiscreteCondensedCoefficient A) g'
  have hgen : ∀ M : ConstantModelConstructibleFiniteTor (finiteDiscreteCondensedCoefficient A) X,
    IsIso ((condensedAmbientExchange (finiteDiscreteCondensedCoefficient A) sq).app M.obj) := by
    as_aux_lemma =>
      intro M
      exact finiteProper_generator_specialization A ℓ k X sq M
  as_aux_lemma =>
    exact finiteProper_localizing_exchange (finiteDiscreteCondensedCoefficient A) sq
      hf hf' hmap hgen K hK

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 150000 in
-- Keep the canonical derived functors abstract during elaboration.
/-- Clause (2): the canonical base-change map, the recorded ambient exchange
`condensedAmbientExchange` (the adjunction mate of the square comparison under the
derived adjunctions), is invertible on the localizing closure, for arbitrary `g`.
Source: blueprint sk-prop-ctf-finite-proper-localizing, clause (2)
(blueprint: det-ctf-finite-proper-localizing).

Proof:
1. The existing finite proper base-change theorem, specialized through the identity
   coefficient isomorphism, proves invertibility of the recorded mate on every Dctf
   generator. The two mates agree after identifying their equality transports using
   `finitePullbackCongr_eqToIso`.
2. The pullback compositor commutes with the canonical coherent shifts transported from
   the exact termwise pullback. The two adjunctions give compatible shifts on the right
   adjoints; their units and counits commute with shifts. Thus the mate is shift-compatible
   between triangulated functors, and its isomorphism locus is replete and triangulated.
3. Properness is preserved by the chosen Cartesian square. Clause (1) for both proper
   maps and `UnboundedLocalizingPullback` for the other leg show that the two composite
   functors preserve every existing coproduct of objects in the source closure.
4. Intersect that closure with the mate's isomorphism locus. Naturality and the universal
   property of coproducts make the intersection localizing. It contains the Dctf
   generators by step 1, so minimality makes the mate invertible on the whole closure. -/
theorem finiteProperLocalizing_baseChange
    {X' Y' : Scheme.{u}} [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [IsSeparated (X' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))] [IsProper f]
    (sq : ChosenCartesianSquare g' f' f g)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (finiteDiscreteCondensedCoefficient A) X)))
    (hK : localizingClosureProEtale (finiteDiscreteCondensedCoefficient A) X K) :
    IsIso ((condensedAmbientExchange (finiteDiscreteCondensedCoefficient A) sq).app K) := by
  exact finiteProperLocalizing_baseChange_proof ℓ p hℓ hp hpℓ k A hA sq K hK

/-- Clause (3), open part: extension by zero preserves the recorded Dctf and all small
sums, and restricts to an exact sum-preserving functor of the localizing closures.
Source: blueprint sk-prop-ctf-finite-proper-localizing, clause (3)
(blueprint: det-ctf-finite-proper-localizing).

Proof (steps 1 and 16 of the node): by step 1 the constant-`A` categories are the
module-object categories over the finite discrete condensed ring, which is an admissible
coefficient. Apply det-proper-image-localizing-open with `Λ = A` discrete: its scheme
hypotheses are the standing ones, and it gives preservation of Dctf, of all small ambient
sums, and the exact sum-preserving restriction to the two localizing closures. -/
theorem finiteOpenLocalizing (j : X ⟶ Y) [j.IsOver (Spec (.of k))]
    [IsOpenImmersion j] :
    finiteCoefficientLocalizingProperties (finiteDiscreteCondensedCoefficient A)
      (j)_!open⟦finiteDiscreteCondensedCoefficient A⟧.mapDerivedCategory ∧
    (∀ I : Type (u + 2), PreservesColimitsOfShape (Discrete I)
      (j)_!open⟦finiteDiscreteCondensedCoefficient A⟧.mapDerivedCategory) := by
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨hctf, _, _, _, hmap, _, _⟩ :=
    openImmersionLowerShriek_localizing ℓ k p hp hpℓ
      (finiteDiscreteCondensedCoefficient A) (finiteDiscreteCoefficient_admissible ℓ A hA) j
  let J := (j)_!open⟦finiteDiscreteCondensedCoefficient A⟧.mapDerivedCategory
  have hsums : PreservesColimitsOfSize.{u + 2, u + 2} J :=
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (finiteDiscreteCondensedCoefficient A) j).leftAdjoint_preservesColimits
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro K hK
    exact hctf ⟨K, hK⟩
  · intro K hK
    exact hmap ⟨K, hK⟩
  · intro T hT _ _ _
    exact Functor.map_distinguished _ T hT
  · intro I D _
    exact hsums.preservesColimitsOfShape.preservesColimit
  · intro I
    exact hsums.preservesColimitsOfShape

/-- Clause (3), compactification part: for `j` open and `f` proper, `Rf_* ∘ j_!` maps
Dctf into Dctf and restricts to an exact sum-preserving functor of the closures.
Source: blueprint sk-prop-ctf-finite-proper-localizing, clause (3)
(blueprint: det-ctf-finite-proper-localizing).

Proof (step 17 of the node): apply `finiteOpenLocalizing` (step 16) to `j` and
`finiteProperLocalizing` (step 13) to `f`. Each maps Dctf into Dctf and restricts to an
exact functor of the closures, so the composite does. For a family in the source closure
the two canonical coproduct comparisons compose to
`Rf_* j_! (⨁ K_s) ≅ Rf_* (⨁ j_! K_s) ≅ ⨁ Rf_* j_! K_s`, compatibly with coprojections,
including the empty family. -/
theorem finiteCompactificationLocalizing
    {U : Scheme.{u}} [U.Over (Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] :
    finiteCoefficientLocalizingProperties (finiteDiscreteCondensedCoefficient A)
      ((j)_!open⟦finiteDiscreteCondensedCoefficient A⟧.mapDerivedCategory ⋙
        (f)_*⟦finiteDiscreteCondensedCoefficient A⟧.rightDerivedFunctor) := by
  obtain ⟨hj, _⟩ := finiteOpenLocalizing ℓ p hℓ hp hpℓ k A hA j
  have hf := finiteProperLocalizing ℓ p hℓ hp hpℓ k A hA f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    exact hf.1 _ (hj.1 K hK)
  · intro K hK
    exact hf.2.1 _ (hj.2.1 K hK)
  · intro T hT h₁ h₂ h₃
    have hT' := hj.2.2.1 T hT h₁ h₂ h₃
    have hT'' := hf.2.2.1 _ hT' (hj.2.1 _ h₁) (hj.2.1 _ h₂) (hj.2.1 _ h₃)
    exact isomorphic_distinguished _ hT'' _
      ((Functor.mapTriangleCompIso _ _).app T)
  · intro I D hD
    have h₁ := hj.2.2.2 I D hD
    have h₂ := hf.2.2.2 I
      (D ⋙ (j)_!open⟦finiteDiscreteCondensedCoefficient A⟧.mapDerivedCategory)
      (fun i ↦ hj.2.1 _ (hD i))
    exact preserves_composite D h₁ h₂

end Setting

end AlgebraicGeometry.ProEtale
