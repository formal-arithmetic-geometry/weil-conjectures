/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import Sheaf.Paper.LocalizingClosureExistence
import Mathlib.Topology.Instances.ZMod
import Sheaf.Paper.UnboundedLocalizingPullback
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Sheaf.SixFunctors.ProperImageLocalizingProper

/-!
# Extending proper base change to the localizing closure

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-proper-base-change-unbounded/sk-prop-proper-base-change-unbounded-extension.md
(blueprint: det-proper-base-change-unbounded-extension).

The exchange is the existing canonical ambient mate, transported to the exact termwise
inverse images. The ambient category is ordinary and unbounded; the generators are bounded
constructible objects of finite Tor amplitude. All six coefficient cases are retained,
including the finite-subextension-valued algebraic-closure coefficient.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v u' v'

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

private theorem extend_iso
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : ObjectProperty C) (hloc : IsLocalizingSubcategory (localizingClosure S))
    (F G : C ⥤ D) (η : F ⟶ G) [η.isoLocus.IsTriangulated]
    (hsums : ∀ (I : Type u) (J : Discrete I ⥤ (localizingClosure S).FullSubcategory),
      PreservesColimit (J ⋙ (localizingClosure S).ι) F ∧
        PreservesColimit (J ⋙ (localizingClosure S).ι) G)
    (hS : ∀ K, S K → IsIso (η.app K)) :
    ∀ K, localizingClosure S K → IsIso (η.app K) := by
  let L := localizingClosure S
  let P : ObjectProperty C := L ⊓ η.isoLocus
  let : L.IsTriangulated := hloc.1
  let : L.IsClosedUnderIsomorphisms := hloc.2.1
  have hP : IsLocalizingSubcategory P := by
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
  intro K hK
  exact (hK P hP (fun M hM ↦ ⟨fun Q hQ hSQ ↦ hSQ M hM, hS M hM⟩)).2

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {X' X Y' Y : Scheme.{u}}
  {g' : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}

/-- The canonical ambient exchange expressed using exact termwise inverse images.
The comparison `Lu^* ≅ D(u^*)` is the canonical exact-functor comparison, and both
adjunctions are transported along it. Consequently the transported mate inserts the unit
for `p'`, applies the termwise square comparison built from `upperStarComp` and `sq.w`,
and contracts the counit for `p`, exactly as in the displayed formula of the source.
This is a change of presentation of `condensedAmbientExchange`, with no new choice of map.
Source: blueprint main-20261015, unbounded base-change extension, displayed beta
(blueprint: det-proper-base-change-unbounded-extension). -/
def termwiseCondensedAmbientExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : ChosenCartesianSquare g' p' p g) :
    (lowerStar Λ p).rightDerivedFunctor ⋙ (upperStar Λ g).mapDerivedCategory ⟶
      (upperStar Λ g').mapDerivedCategory ⋙ (lowerStar Λ p').rightDerivedFunctor :=
  (Functor.isoWhiskerLeft (lowerStar Λ p).rightDerivedFunctor
    (leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm).hom ≫
    condensedAmbientExchange Λ sq ≫
    (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ g')
      (lowerStar Λ p').rightDerivedFunctor).hom

/-- The extension implication for one coefficient ring: the specified base-change map
being invertible on every bounded constructible finite-Tor object implies its invertibility
on every object of their localizing closure. Both quantifiers range over the same ordinary
unbounded derived category of internal modules over the pulled-back condensed ring.
Source: blueprint main-20261015, unbounded base-change extension, final sentence
(blueprint: det-proper-base-change-unbounded-extension). -/
def UnboundedBaseChangeExtension
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : ChosenCartesianSquare g' p' p g) : Prop :=
  (∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    (constantModelBoundedConstructible Λ X K ∧ DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((termwiseCondensedAmbientExchange Λ sq).app K)) →
  ∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    localizingClosureProEtale Λ X K →
      IsIso ((termwiseCondensedAmbientExchange Λ sq).app K)

attribute [local instance] unboundedLocalizingPullbackCommShift

private theorem normalization_commShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    NatTrans.CommShift (upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory.hom ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility
      (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ
  exact NatTrans.CommShift.of_iso_inv
    (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ

private theorem comparison_comp_commShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.CommShift (leftDerivedUpperStarComp Λ f g).hom ℤ := by
  let := normalization_commShift Λ f
  let := normalization_commShift Λ g
  let := normalization_commShift Λ (f ≫ g)
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_assoc, Iso.symm_self_id_assoc,
    Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

/-- The isomorphism locus of the specified ambient exchange is triangulated.
No properness or finiteness hypothesis is required for this exactness assertion.
Source: blueprint main-20261015, det-proper-base-change-unbounded-extension,
steps 2--4 (blueprint: det-proper-base-change-unbounded-extension).

Proof: transport the termwise coherent shifts to each total inverse image through
`leftDerivedUpperStarIsoMapDerivedCategory`. Transport its exactness through the same
isomorphism. For the two derived adjunctions, equip the right adjoints with the unique
compatible shifts; the triangulated right-adjoint theorem supplies their exactness.
The pullback comparison commutes with shifts: after the exact-functor comparisons it
is the localization of the termwise comparison induced by `upperStarComp` and the square
equality. In each degree its component on a shifted complex is its component at the
shifted degree, and additivity respects the signed differential. The derived comparison
is built by precisely these exact-functor identifications. The units and counits commute
with these chosen shifts. Expand `mateEquiv`: its whiskered units, comparison and counit,
and its associators and unitors, all commute with shifts, so their composite does too.
The two composite functors are triangulated. The standard isomorphism-locus theorem
then gives closure under zero, all integer shifts and distinguished triangles. -/
private theorem condensedAmbientExchange_isoLocus_triangulated
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' p' p g) :
    (condensedAmbientExchange Λ sq).isoLocus.IsTriangulated := by
  have hcomp : NatTrans.CommShift (condensedAmbientPullbackComparison Λ sq).hom ℤ := by
    have := comparison_comp_commShift Λ p' g
    have := comparison_comp_commShift Λ g' p
    have heq' (f₁ f₂ : X' ⟶ Y) (h : f₁ = f₂) : NatTrans.CommShift
        (eqToIso (congrArg (fun h : X' ⟶ Y ↦ (upperStar Λ h).leftDerivedFunctor)
          h)).hom ℤ := by
      subst f₂
      change NatTrans.CommShift (𝟙 _) ℤ
      infer_instance
    have := heq' _ _ sq.toCommSq.w.symm
    unfold condensedAmbientPullbackComparison
    dsimp only [Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have exact_pull {T S : Scheme.{u}} (f : T ⟶ S) :
      (upperStar Λ f).leftDerivedFunctor.IsTriangulated := by
    have := Functor.CommShift.ofIso_compatibility
      (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ
    exact Functor.isTriangulated_of_iso (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm
  let := exact_pull p
  let := exact_pull g
  let := exact_pull p'
  let := exact_pull g'
  let a := derivedUpperStarLowerStarAdjunction Λ p
  let a' := derivedUpperStarLowerStarAdjunction Λ p'
  let : (lowerStar Λ p).rightDerivedFunctor.CommShift ℤ := a.rightAdjointCommShift ℤ
  let : (lowerStar Λ p').rightDerivedFunctor.CommShift ℤ := a'.rightAdjointCommShift ℤ
  let := a.commShift_of_leftAdjoint ℤ
  let := a'.commShift_of_leftAdjoint ℤ
  let := a.isTriangulated_rightAdjoint
  let := a'.isTriangulated_rightAdjoint
  have : NatTrans.CommShift (condensedAmbientExchange Λ sq) ℤ := by
    dsimp only [condensedAmbientExchange, mateEquiv, Equiv.coe_fn_mk]
    infer_instance
  infer_instance

private theorem composite_sums
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hp : ProperLocalizingHypotheses Λ p)
    (hp' : ProperLocalizingHypotheses Λ p')
    (hg : UnboundedLocalizingPullback Λ g)
    (hg' : UnboundedLocalizingPullback Λ g')
    (I : Type (u + 2)) (J : Discrete I ⥤ (localizingClosureProEtale Λ X).FullSubcategory) :
    PreservesColimit (J ⋙ (localizingClosureProEtale Λ X).ι)
      ((lowerStar Λ p).rightDerivedFunctor ⋙ (upperStar Λ g).leftDerivedFunctor) ∧
    PreservesColimit (J ⋙ (localizingClosureProEtale Λ X).ι)
      ((upperStar Λ g').leftDerivedFunctor ⋙ (lowerStar Λ p').rightDerivedFunctor) := by
  let := hg.sums I
  let := hg'.sums I
  let := hp.2 I J
  let J' := (localizingClosureProEtale Λ X').lift
    (J ⋙ (localizingClosureProEtale Λ X).ι ⋙ (upperStar Λ g').leftDerivedFunctor)
    (fun i ↦ hg'.localizing (J.obj i))
  have : PreservesColimit
      ((J ⋙ (localizingClosureProEtale Λ X).ι) ⋙ (upperStar Λ g').leftDerivedFunctor)
      (lowerStar Λ p').rightDerivedFunctor := by
    exact hp'.2 I J'
  constructor <;> infer_instance

private theorem extension_of_preservation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : ChosenCartesianSquare g' p' p g)
    (hp : ProperLocalizingHypotheses Λ p)
    (hp' : ProperLocalizingHypotheses Λ p')
    (hg : UnboundedLocalizingPullback Λ g)
    (hg' : UnboundedLocalizingPullback Λ g') : UnboundedBaseChangeExtension Λ sq := by
  have he (K) : IsIso ((termwiseCondensedAmbientExchange Λ sq).app K) ↔
      IsIso ((condensedAmbientExchange Λ sq).app K) := by
    simp only [termwiseCondensedAmbientExchange, NatTrans.comp_app,
      isIso_comp_left_iff, isIso_comp_right_iff]
  intro h K hK
  apply (he K).2
  let := condensedAmbientExchange_isoLocus_triangulated Λ sq
  apply extend_iso _ _ _ _ (condensedAmbientExchange Λ sq)
    (composite_sums Λ hp hp' hg hg') (fun M hM ↦ (he M).1 (h M hM)) K hK
  exact (localizingClosure_exists Λ X
    (constantModelBoundedConstructible Λ X ⊓ fun M ↦
      DerivedCategory.finiteTorAmplitude _ M)).2.2.2.1

/-- Proper base change extends from Dctf to its localizing closure, for every admissible
coefficient in the source's list. The last coefficient is specifically the ring of
continuous functions valued in some finite subextension, rather than all continuous
functions into the algebraic closure. Finite rings are represented in `Type 0`, which
includes a representative of every finite coefficient ring.
Source: blueprint main-20261015, unbounded base-change extension
(blueprint: det-proper-base-change-unbounded-extension).

Proof plan, following the five steps of the DAG node:
1. Properness of `p'` follows from properness under base change
   (lem-weil-pbc-proper-base-change). By det-proper-image-localizing-proper both proper
   pushforwards carry localizing closures to localizing closures and preserve ambient
   small sums. By det-proper-base-change-unbounded-pullback the two inverse images do so
   too. Hence both composites restrict to sum-preserving functors. Fullness identifies
   coproducts in these subcategories with the ambient coproducts (sk-def-localizing-closure).
2. Cartesian coefficients make inverse images exact (sk-prop-sfb-cartesian-coefficients).
   The exact-functor comparison of sk-def-sfb-derived-categories transports the adjunctions
   of sk-def-sfb-module-derived-pushpull to the termwise inverse images. Equip their right
   adjoints with the unique compatible coherent shifts
   (lem-weil-pbc-adjunction-shift-compatibility-unique); they are exact by
   lem-sf-triangulated-right-adjoint. Restrict and compose these exact functors using
   lem-weil-pbc-triangulated-functor-restriction and -composite. These auxiliary structures
   change neither the underlying functors nor the exchange map.
3. The comparison from def-sfb-module-upper-star-comp commutes with integer shifts
   degreewise: its degree-r component on a shifted complex is its component in degree
   r+n on the original complex. Additivity respects the shifted differential. Localization
   preserves this equality (def-weil-abstract-derived-category).
4. The unit and counit commute with the shifts of step 2. Whiskering and composition
   preserve compatibility (lem-weil-pbc-commshift-nattrans-comp-whisker), so the specified
   exchange restricts to a shift-compatible natural transformation of the two exact
   sum-preserving functors on the full localizing subcategories.
5. Apply sk-lem-sf-determination. Its generator hypothesis is exactly the antecedent of
   UnboundedBaseChangeExtension, and its conclusion is the desired assertion on the closure.
-/
theorem unboundedBaseChangeExtension
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
    [IsSeparated (X' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    [p.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [p'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]
    [IsProper p] (sq : ChosenCartesianSquare g' p' p g) :
    (∀ (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A],
      (∃ n : ℕ, (ℓ ^ n : A) = 0) →
        UnboundedBaseChangeExtension (Profinite.continuousMapRingObj A) sq) ∧
    UnboundedBaseChangeExtension (Profinite.continuousMapRingObj ℤ_[ℓ]) sq ∧
    UnboundedBaseChangeExtension (Profinite.continuousMapRingObj ℚ_[ℓ]) sq ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      UnboundedBaseChangeExtension (Profinite.padicIntegersRingObj ℓ E) sq ∧
      UnboundedBaseChangeExtension (Profinite.continuousMapRingObj E) sq) ∧
    UnboundedBaseChangeExtension (Profinite.padicAlgClRingObj ℓ) sq := by
  let E₀ : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  have hp'proper : IsProper p' := by
    rw [← sq.hom_snd]
    infer_instance
  let := hp'proper
  have hg := unboundedLocalizingPullback (ringChar k) ℓ
    (show ringChar k ≠ ℓ from Fact.out) k g
  have hg' := unboundedLocalizingPullback (ringChar k) ℓ
    (show ringChar k ≠ ℓ from Fact.out) k g'
  have hp (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
      (hA : ∃ n : ℕ, (ℓ ^ n : A) = 0)
      (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) [IsCommMonObj Λ.X]
      (hΛ : Λ ∈ [Mon.mk (Profinite.continuousMapRingObj A),
        Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ]),
        Mon.mk (Profinite.padicIntegersRingObj ℓ E.val),
        Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ]),
        Mon.mk (Profinite.continuousMapRingObj E), Mon.mk (Profinite.padicAlgClRingObj ℓ)]) :
      ProperLocalizingHypotheses Λ.X p ∧ ProperLocalizingHypotheses Λ.X p' := by
    exact ⟨proper_image_localizing_proper_coefficients ℓ E A hA Λ hΛ k p,
      proper_image_localizing_proper_coefficients ℓ E A hA Λ hΛ k p'⟩
  have hZ : ∃ n : ℕ, (ℓ ^ n : ZMod ℓ) = 0 := ⟨1, by simp⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A _ _ _ _ hA
    obtain ⟨hp, hp'⟩ := hp E₀ A hA (Mon.mk (Profinite.continuousMapRingObj A)) (by simp)
    exact extension_of_preservation _ sq hp hp' (hg.1 A hA).some (hg'.1 A hA).some
  · obtain ⟨hp, hp'⟩ := hp E₀ (ZMod ℓ) hZ
      (Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) (by simp)
    exact extension_of_preservation _ sq hp hp' hg.2.1.some hg'.2.1.some
  · obtain ⟨hp, hp'⟩ := hp E₀ (ZMod ℓ) hZ
      (Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) (by simp)
    exact extension_of_preservation _ sq hp hp' hg.2.2.1.some hg'.2.2.1.some
  · intro E
    obtain ⟨hpi, hpi'⟩ := hp E (ZMod ℓ) hZ
      (Mon.mk (Profinite.padicIntegersRingObj ℓ E)) (by simp)
    obtain ⟨hpe, hpe'⟩ := hp E (ZMod ℓ) hZ
      (Mon.mk (Profinite.continuousMapRingObj E)) (by simp)
    exact ⟨extension_of_preservation _ sq hpi hpi'
        (hg.2.2.2.1 E).1.some (hg'.2.2.2.1 E).1.some,
      extension_of_preservation _ sq hpe hpe'
        (hg.2.2.2.1 E).2.some (hg'.2.2.2.1 E).2.some⟩
  · obtain ⟨hp, hp'⟩ := hp E₀ (ZMod ℓ) hZ
      (Mon.mk (Profinite.padicAlgClRingObj ℓ)) (by simp)
    exact extension_of_preservation _ sq hp hp' hg.2.2.2.2.some hg'.2.2.2.2.some

end AlgebraicGeometry.ProEtale.CondensedRing
