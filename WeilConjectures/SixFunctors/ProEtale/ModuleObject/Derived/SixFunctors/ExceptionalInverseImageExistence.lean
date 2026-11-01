/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import all WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.Brown.BrownHypotheses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralBrownAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralExceptionalRestriction
import all WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.NumberTheory.Padics.Complex
import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalRestrictionGlue
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousAlgClConstructibleTor
public import WeilConjectures.AlgebraicGeometry.Rational.RationalExceptionalRestriction

/-!
# Existence of the exceptional inverse image

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-existence/_section.md,
and det-existence-localizing.proof.md and det-existence-restriction.proof.md
(blueprint: sk-thm-existence).

The lower shriek is the existing restriction of the actual compactification composite.
All categories are full subcategories of the ordinary unbounded module-object derived
category, with the recorded finite constant-model constructibility convention.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Compactness transports by precomposition with an isomorphism. -/
private theorem compact_of_iso
    {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{u} C]
    {K L : C} (e : K ≅ L) (hL : IsCompactObject L) : IsCompactObject K := by
  classical
  intro I A
  let d := DirectSum.map (fun i ↦ Preadditive.leftComp (A i) e.hom)
  have hd : Function.Bijective d :=
    ⟨(DirectSum.map_injective _).2 (fun i ↦ e.symm.homFromEquiv.injective),
      (DirectSum.map_surjective _).2 (fun i ↦ e.symm.homFromEquiv.surjective)⟩
  let post := Preadditive.leftComp (∐ A) e.hom
  have hp : Function.Bijective post := e.symm.homFromEquiv.bijective
  let a := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp K (Sigma.ι A i))
  let b := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp L (Sigma.ι A i))
  have square : a.comp d = post.comp b := by
    apply DirectSum.addHom_ext
    intro i f
    simp only [AddMonoidHom.comp_apply]
    dsimp [a, b, d]
    rw [DirectSum.map_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    exact Category.assoc _ _ _
  have hb : Function.Bijective b := hL I A
  have hcomp : Function.Bijective (a ∘ d) := by
    change Function.Bijective (a.comp d)
    rw [square]
    exact hp.comp hb
  exact (Function.Bijective.of_comp_iff a hd).mp hcomp

/-- Bounded constructibility transports termwise along a coefficient isomorphism. -/
private theorem bounded_coefficientIso
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (e : Mon.mk Λ ≅ Mon.mk Λ')
    (T : Scheme.{u}) (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T)
      Ab.{u + 1}) (condensedRingObj Λ T)))
    (hK : constantModelBoundedConstructible Λ T K) :
    constantModelBoundedConstructible Λ' T ((shriekCoefficientTransport e T).obj K) := by
  let φ := (upperStarFromPoint T).map e.inv.hom
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  have : IsIso φ := inferInstanceAs (IsIso ((upperStarFromPoint T).map e.inv.hom))
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) φ
  refine ⟨F.bounded_mapDerivedCategory_obj hK.1, ?_⟩
  intro n
  exact constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K)
    (constructible_comap (Λ := Λ) (Λ' := Λ') e.inv.hom T _ (hK.2 n))

/-- Exact coefficient equivalences preserve the ambient-intersection closure. -/
private theorem map_localizing_coefficientIso
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    ∀ K, L(T) K → localizingClosureProEtale Λ' T
      ((shriekCoefficientTransport e T).obj K) := by
  let F := shriekCoefficientTransport e T
  have : F.IsEquivalence := (shriekCoefficientIso_transport e T).1
  have : F.IsTriangulated := (shriekCoefficientIso_transport e T).2.1
  intro K hK P hP hSP
  let := hP.1
  let := hP.2.1
  apply hK (P.inverseImage F) ?_ (fun A hA ↦
    hSP _ ((shriekCoefficientIso_transport e T).2.2.2.1 A |>.mpr hA))
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I D hD hDR
  let := hD
  let hpres : PreservesColimitsOfSize.{u + 2, u + 2} F :=
    F.asEquivalence.toAdjunction.leftAdjoint_preservesColimits
  let hshape : PreservesColimitsOfShape (Discrete I) F :=
    hpres.preservesColimitsOfShape
  let : PreservesColimit D F := hshape.preservesColimit
  let : HasColimit (D ⋙ F) := Adjunction.hasColimit_comp_equivalence D F
  exact P.prop_of_iso (preservesColimitIso F D).symm
    (hP.2.2 (D ⋙ F) inferInstance hDR)

/-- Coefficient transport identifies the two recorded localizing closures. -/
private theorem localizing_coefficientIso
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    ∀ K, localizingClosureProEtale Λ' T ((shriekCoefficientTransport e T).obj K) ↔ L(T) K := by
  intro K
  constructor
  · intro hK
    have hi : L(T).IsClosedUnderIsomorphisms :=
      (localizingClosure_exists Λ T S(T)).2.2.2.1.2.1
    let := hi
    exact ObjectProperty.prop_of_iso _ ((transportCompIso e T).app K)
      (map_localizing_coefficientIso _ e.symm T _ hK)
  · exact map_localizing_coefficientIso Λ e T K

/-- Conjugating an adjunction transports its constructible-preservation property. -/
private theorem preservation_coefficientIso
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (e : Mon.mk Λ ≅ Mon.mk Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, L(X) K → L(Y)
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : L(Y).FullSubcategory ⥤ L(X).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G)
    (pres : ∀ (h' : ∀ K, localizingClosureProEtale Λ' X K →
          localizingClosureProEtale Λ' Y
            ((rightDerivedLowerShriekOfCompactification Λ' c.obj.obj).obj K))
        (G' : (localizingClosureProEtale Λ' Y).FullSubcategory ⥤
          (localizingClosureProEtale Λ' X).FullSubcategory),
        (localizingLowerShriek Λ' c.obj.obj h' ⊣ G') →
        ∀ N, (constantModelBoundedConstructible Λ' Y ⊓
          DerivedCategory.finiteTorAmplitude _) N.obj →
          (constantModelBoundedConstructible Λ' X ⊓
            DerivedCategory.finiteTorAmplitude _) (G'.obj N).obj) :
    ∀ N, S(Y) N.obj → S(X) (G.obj N).obj := by
  have isos (T : Scheme.{u}) : (localizingClosureProEtale Λ' T).IsClosedUnderIsomorphisms :=
    (localizingClosure_exists Λ' T
      (constantModelBoundedConstructible Λ' T ⊓ DerivedCategory.finiteTorAmplitude _)
      ).2.2.2.1.2.1
  let := isos X
  let := isos Y
  have isoL (T : Scheme.{u}) :
      (localizingClosureProEtale Λ' T).inverseImage (shriekCoefficientTransport e T) = L(T) := by
    ext K
    exact localizing_coefficientIso Λ e T K
  have equiv (T : Scheme.{u}) : (shriekCoefficientTransport e T).IsEquivalence :=
    (shriekCoefficientIso_transport e T).1
  let U := (shriekCoefficientTransport e X).asEquivalence.congrFullSubcategory (isoL X)
  let V := (shriekCoefficientTransport e Y).asEquivalence.congrFullSubcategory (isoL Y)
  let H' := rightDerivedLowerShriekOfCompactification Λ' c.obj.obj
  have h' : ∀ K, localizingClosureProEtale Λ' X K →
      localizingClosureProEtale Λ' Y (H'.obj K) := by
    intro K hK
    let M := (shriekCoefficientTransport e X).asEquivalence.inverse.obj K
    have hM : L(X) M := (localizing_coefficientIso Λ e X M).mp
      (ObjectProperty.prop_of_iso _
        ((shriekCoefficientTransport e X).asEquivalence.counitIso.app K).symm hK)
    have hi := (localizingClosure_exists Λ' Y
      (constantModelBoundedConstructible Λ' Y ⊓ DerivedCategory.finiteTorAmplitude _)
      ).2.2.2.1.2.1
    let := hi
    exact ObjectProperty.prop_of_iso _
      ((shriekCoefficientCompactificationIso e c).app M ≪≫
        H'.mapIso ((shriekCoefficientTransport e X).asEquivalence.counitIso.app K))
      (map_localizing_coefficientIso Λ e Y _ (h M hM))
  let F' := localizingLowerShriek Λ' c.obj.obj h'
  let G' := V.inverse ⋙ G ⋙ U.functor
  let a : localizingLowerShriek Λ c.obj.obj h ⋙ V.functor ≅ U.functor ⋙ F' :=
    NatIso.ofComponents
      (fun K ↦ (localizingClosureProEtale Λ' Y).isoMk
        ((shriekCoefficientCompactificationIso e c).app K.obj))
      (fun g ↦ ObjectProperty.hom_ext _
        ((shriekCoefficientCompactificationIso e c).hom.naturality g.hom))
  let i : (U.inverse ⋙ localizingLowerShriek Λ c.obj.obj h) ⋙ V.functor ≅ F' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft U.inverse a ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight U.counitIso F' ≪≫ F'.leftUnitor
  let adj' : F' ⊣ G' := ((U.symm.toAdjunction.comp adj).comp V.toAdjunction).ofNatIsoLeft i
  let b : G ⋙ U.functor ≅ V.functor ⋙ G' :=
    (G ⋙ U.functor).leftUnitor.symm ≪≫
      Functor.isoWhiskerRight V.unitIso (G ⋙ U.functor) ≪≫ Functor.associator _ _ _
  intro N hN
  have hp := pres h' G' adj' (V.functor.obj N)
    ((shriekCoefficientIso_transport e Y).2.2.2.1 N.obj |>.mpr hN)
  apply (shriekCoefficientIso_transport e X).2.2.2.1 (G.obj N).obj |>.mp
  exact ObjectProperty.prop_of_iso _
    ((localizingClosureProEtale Λ' X).ι.mapIso (b.app N)).symm hp

/-- The universe lift of a finite coefficient gives the same condensed ring. -/
private noncomputable def finite_coefficientIso
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj (ULift.{u} A)) := by
  let i : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} A) :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          { toFun := fun a ↦
              ULift.up ⟨fun x ↦ ULift.up (a.down x),
                continuous_uliftUp.comp a.down.continuous⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := by intros; rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          { toFun := fun a ↦
              ULift.up ⟨fun x ↦ (a.down x).down,
                continuous_uliftDown.comp a.down.continuous⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := by intros; rfl }⟩
      hom_inv_id := by ext; rfl
      inv_hom_id := by ext; rfl }
  let F := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  have : IsMonHom (F.mapIso i).hom := inferInstanceAs (IsMonHom (F.map i.hom))
  exact Mon.mkIso' (F.mapIso i)

/-- The four existence assertions, including restriction of the same Brown right adjoint.
The witnesses for triangulation and coproducts install the inherited structures before
compactness or exactness is asserted. The small skeletal family has exactly one object
in each isomorphism class of Dctf and generates the localizing category. Preservation
of Dctf by both adjoints means that the displayed adjunction restricts along the fully
faithful inclusions, with the same Hom equivalences. For each of the five non-finite
coefficient objects, the final clause identifies Dctf and Dbc as ambient object properties.

Source: blueprint main-20261015, sk-thm-existence, clauses 1--4 and final paragraph
(blueprint: sk-thm-existence).

Proof:
1. Apply sk-lem-brown-hypotheses to X. It gives compactness of every Dctf object
   in its closure and a small skeleton of compact generators, together with the
   triangulated and coproduct structures required by Brown representability.
2. Both schemes are qcqs: their structure maps are quasi-compact and separated
   over the affine scheme Spec k. Separated cancellation and locally-finite-type
   cancellation show that f is separated and locally of finite type; quasi-compactness
   of X and quasi-separatedness of Y show that f is quasi-compact. Apply Nagata to f.
   For its chosen compactification, det-sf-comp-coherence-single gives preservation
   of both closures, exactness, direct sums and Dctf. The comparisons of
   det-sf-comp-coherence-cocycle identify the functors from other compactifications.
3. Apply sk-prop-sf-existence once to this exact sum-preserving functor. Brown
   representability produces its right adjoint. Transposing the shift comparison
   gives a coherent shift comparison for that adjoint, which is exact.
4. For finite A, sk-prop-sf-rf-shriek-preservation gives preservation of Dctf by
   this right adjoint. For O_E, det-prop-int-brown-adjoint identifies it with the
   integral Brown adjoint and sk-thm-int-restriction gives preservation. For E and
   the algebraic closure use sk-thm-restriction for the same general right adjoint.
   Z_l and Q_l are the cases E = Q_l. Restrict the Hom equivalences along the full
   Dctf inclusions; their naturality and triangle identities are unchanged.
5. Apply det-def-localizing-closure-ctf-equals-bc to the integral and finite-extension
   coefficients. For the all-continuous algebraic closure use its separate theorem
   det-sf-comp-continuous-algcl-constructible-tor, since the older equality theorem
   uses finite-subextension-valued coefficients. The schemes are noetherian by finite
   type over k. Exact coefficient transport preserves bounded constructibility and
   reflects Dctf, so the same equality holds for each isomorphic coefficient ring.
   No regularity or Gorenstein condition is imposed for finite A. The zero ring and
   the empty schemes are included.
-/
theorem exceptionalInverseImage_exists
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ℓ k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    ∃ (hX : L(X.left).IsTriangulated) (hY : L(Y.left).IsTriangulated)
      (hSX : S(X.left) ≤ L(X.left)) (hSY : S(Y.left) ≤ L(Y.left))
      (h : ∀ K, L(X.left) K → L(Y.left)
        ((rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f)).obj K))
      (sX : HasCoproducts.{u + 1} L(X.left).FullSubcategory)
      (sY : HasCoproducts.{u + 1} L(Y.left).FullSubcategory),
      (fun [triX : L(X.left).IsTriangulated] [triY : L(Y.left).IsTriangulated]
          [sumsX : HasCoproducts.{u + 1} L(X.left).FullSubcategory]
          [sumsY : HasCoproducts.{u + 1} L(Y.left).FullSubcategory] ↦
        (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
          IsCompactObject.{u + 1} ((ObjectProperty.ιOfLE hSX).obj K)) ∧
        (LocallySmall.{u + 1} (ConstantModelConstructibleFiniteTor Λ X.left) ∧
          ∃ (I : Type (u + 1)) (E : I → ConstantModelConstructibleFiniteTor Λ X.left),
          (∀ K, ∃ i, Nonempty (E i ≅ K)) ∧
          (∀ i j, Nonempty (E i ≅ E j) → i = j) ∧
          IsTriangulatedGeneratingFamily (fun i ↦ (ObjectProperty.ιOfLE hSX).obj (E i))) ∧
        (localizingLowerShriek Λ (compactificationOverField f) h).IsTriangulated ∧
        (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
          (localizingLowerShriek Λ (compactificationOverField f) h)) ∧
        (∀ K : L(X.left).FullSubcategory, S(X.left) K.obj →
          S(Y.left) ((localizingLowerShriek Λ (compactificationOverField f) h).obj K).obj) ∧
        (∀ c : Compactification f.left, Nonempty
          ((localizingLowerShriek Λ (compactificationOverField f) h) ⋙ L(Y.left).ι ≅
            L(X.left).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)) ∧
        (∃ G : L(Y.left).FullSubcategory ⥤ L(X.left).FullSubcategory,
          ∃ s : G.CommShift ℤ,
            (fun [comm : G.CommShift ℤ] ↦
              G.IsTriangulated ∧
              Nonempty (localizingLowerShriek Λ (compactificationOverField f) h ⊣ G) ∧
              (∀ N : L(Y.left).FullSubcategory, S(Y.left) N.obj → S(X.left) (G.obj N).obj))
              (comm := s)) ∧
        ((Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
          (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
            Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
          (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
            Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ)))) →
          S(X.left) = constantModelBoundedConstructible Λ X.left ∧
          S(Y.left) = constantModelBoundedConstructible Λ Y.left))
        (triX := hX) (triY := hY) (sumsX := sX) (sumsY := sY) := by
  classical
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let : f.left.IsOver (Spec (.of k)) := ⟨f.w⟩
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y.hom›
  let : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  let : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  let : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  let : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
  have : IsSeparated (f.left ≫ Y.hom) := f.w.symm ▸ ‹IsSeparated X.hom›
  let : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  have : LocallyOfFiniteType (f.left ≫ Y.hom) :=
    f.w.symm ▸ ‹LocallyOfFiniteType X.hom›
  let : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  let : QuasiCompact f.left := by infer_instance
  let c : Compactification.BoundaryCompactification f.left :=
    ⟨⟨compactificationOverField f, Compactification.quasiCompact_openImmersion _ inferInstance⟩⟩
  obtain ⟨h, hX, hY, hFtri, ⟨sX⟩, ⟨sY⟩, hsums, G, s, hGtri, _, adj, _⟩ :=
    exists_localizingExceptionalAdjoint (hcd := hcd) Λ ℓ k f.left c _hΛ
  let := hX
  let := hY
  let := sX
  let := sY
  let := s
  have hSX : S(X.left) ≤ L(X.left) := fun K hK _ _ hS ↦ hS K hK
  have hSY : S(Y.left) ≤ L(Y.left) := fun K hK _ _ hS ↦ hS K hK
  obtain ⟨hsmall, _, _, hS, hisoS, _, hess, _, _, hgen⟩ :=
    brownHypotheses ℓ (ringChar k) (Fact.out : (ringChar k).Prime).pos
      (Fact.out : ringChar k ≠ ℓ) hcd X.hom Λ _hΛ
  let := hsmall
  let := hS
  let := hisoS
  obtain ⟨J, hJ, ⟨e⟩⟩ := (ObjectProperty.exists_equivalence_iff S(X.left)).mpr hess
  let := hJ
  let E := (fromSkeleton J ⋙ e.inverse)
  let eS := (skeletonEquivalence J).trans e.symm
  have hL (i : Skeleton J) : L(X.left) (E.obj i).obj := hSX _ (E.obj i).property
  obtain ⟨hcompact, hgenerate⟩ := hgen (Skeleton J) eS hL
  have hcompactAll : ∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      IsCompactObject.{u + 1} ((ObjectProperty.ιOfLE hSX).obj K) := by
    intro K
    let i := eS.inverse.obj K
    let q : (ObjectProperty.ιOfLE hSX).obj K ≅
        (⟨(eS.functor.obj i).obj, hL i⟩ : L(X.left).FullSubcategory) :=
      L(X.left).isoMk ((S(X.left).ι.mapIso (eS.counitIso.app K)).symm)
    exact compact_of_iso q (hcompact i)
  have hskel : LocallySmall.{u + 1} (ConstantModelConstructibleFiniteTor Λ X.left) ∧
      ∃ (I : Type (u + 1)) (E : I → ConstantModelConstructibleFiniteTor Λ X.left),
        (∀ K, ∃ i, Nonempty (E i ≅ K)) ∧
        (∀ i j, Nonempty (E i ≅ E j) → i = j) ∧
        IsTriangulatedGeneratingFamily (fun i ↦ (ObjectProperty.ιOfLE hSX).obj (E i)) := by
    refine ⟨locallySmall_of_faithful (ObjectProperty.ιOfLE hSX), Skeleton J, E.obj, ?_, ?_,
      hgenerate⟩
    · intro K
      exact ⟨toSkeleton (e.functor.obj K),
        ⟨e.inverse.mapIso (fromSkeletonToSkeletonIso (e.functor.obj K)) ≪≫
          (e.unitIso.app K).symm⟩⟩
    · intro i j hij
      exact skeleton_skeletal J ⟨E.preimageIso hij.some⟩
  have hctf := (compactification_localizing Λ ℓ k f.left c _hΛ).2.2.2
  refine ⟨hX, hY, hSX, hSY, h, sX, sY, hcompactAll, hskel, hFtri, hsums,
    (fun K hK ↦ hctf K.obj hK), ?_, ?_, ?_⟩
  · intro d
    let d' : Compactification.BoundaryCompactification f.left :=
      ⟨⟨d, d.quasiCompact_openImmersion inferInstance⟩⟩
    obtain ⟨φ, _⟩ := compactification_coherence_cocycle Λ ℓ _hΛ k f.left
    exact ⟨(L(Y.left).liftCompιIso _ _) ≪≫ φ c d'⟩
  · refine ⟨G, s, hGtri, ⟨adj⟩, ?_⟩
    let E₀ : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
    obtain ⟨_, _, _, _, _, _, _, _, qIso, zIso, _⟩ :=
      Profinite.base_coefficient_condensed_identification.{u} ℓ
    rcases _hΛ with hfin | hz | hq | hfield | hintegral | hsubfield
    · obtain ⟨A, hA, tA, dA, topA, finA, hn, ⟨eA⟩⟩ := hfin
      let := hA
      let := tA
      let := dA
      let := topA
      let := finA
      apply preservation_coefficientIso Λ (eA ≪≫ finite_coefficientIso A) c h G adj
      intro h' G' adj'
      have hpow : ∃ r : ℕ, ((ℓ ^ r : ℕ) : ULift.{u + 1} (ULift.{u} A)) = 0 := by
        obtain ⟨r, hr⟩ := hn
        refine ⟨r, ?_⟩
        apply ULift.ext
        apply ULift.ext
        simpa using hr 1
      obtain ⟨_, hp, _⟩ := localizingExceptionalAdjoint_preserves_finiteConstructible
        ℓ k (ULift.{u} A) hpow f.left c h' G' adj'
      exact fun N hN ↦ hp ⟨N, hN⟩
    · obtain ⟨eZ⟩ := hz
      apply preservation_coefficientIso Λ (eZ ≪≫ zIso) c h G adj
      exact fun h' G' adj' ↦ integral_preservation (hcd := hcd) ℓ k f.left E₀ c h' G' adj'
    · obtain ⟨eQ⟩ := hq
      exact (rationalExceptional_preserves_constructibleFiniteTor (hcd := hcd) Λ ℓ k f.left E₀
        ⟨eQ ≪≫ qIso⟩ c h G adj).1
    · obtain ⟨E, hE⟩ := hfield
      exact (rationalExceptional_preserves_constructibleFiniteTor (hcd := hcd) Λ ℓ k f.left E
        hE c h G adj).1
    · obtain ⟨E, ⟨eO⟩⟩ := hintegral
      apply preservation_coefficientIso Λ eO c h G adj
      exact fun h' G' adj' ↦ integral_preservation (hcd := hcd) ℓ k f.left E c h' G' adj'
    · obtain ⟨_, _, _, hp, _⟩ := (rationalRestrictionGlue.{u, u} (hcd := hcd) Λ ℓ E₀.1
        (Or.inr hsubfield) k (ringChar k) (Fact.out : ringChar k ≠ ℓ) f.left c h G adj).2
      have heq := (localizingClosure_ctf_equals_bc ℓ X.left Λ
        (Or.inr (Or.inr (Or.inr hsubfield)))).1.2.2.1
      exact fun N hN ↦ (congrFun heq _).mpr (hp N hN.1)
  · intro hcoeff
    let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    let : IsNoetherian X.left := ⟨⟩
    let : IsNoetherian Y.left := ⟨⟩
    have equals (T : Scheme.{u}) [IsNoetherian T] :
        S(T) = constantModelBoundedConstructible Λ T := by
      rcases hcoeff with hz | hq | ⟨E, he⟩ | ⟨E, he⟩ | hc
      · exact (localizingClosure_ctf_equals_bc ℓ T Λ (Or.inl hz)).1.2.2.1
      · exact (localizingClosure_ctf_equals_bc ℓ T Λ (Or.inr (Or.inl hq))).1.2.2.1
      · exact (localizingClosure_ctf_equals_bc ℓ T Λ
          (Or.inr (Or.inr (Or.inl ⟨E, Or.inl he⟩)))).1.2.2.1
      · exact (localizingClosure_ctf_equals_bc ℓ T Λ
          (Or.inr (Or.inr (Or.inl ⟨E, Or.inr he⟩)))).1.2.2.1
      · obtain ⟨eC⟩ := hc
        ext K
        constructor
        · exact And.left
        · intro hK
          have htrans := bounded_coefficientIso Λ eC T K hK
          exact (shriekCoefficientIso_transport eC T).2.2.2.1 K |>.mp
            ⟨htrans, continuousAlgCl_bounded_finiteTor ℓ T _ htrans⟩
    exact ⟨equals X.left, equals Y.left⟩

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

local notation "S(" T ")" =>
  (constantModelBoundedConstructible Λ T ⊓ fun K ↦ DerivedCategory.finiteTorAmplitude _ K)
local notation "L(" T ")" => localizingClosureProEtale Λ T

set_option linter.unusedVariables false in
-- The statement names dependent structure witnesses which are used through typeclass inference.
set_option maxHeartbeats 800000 in
-- Assemble dependent Brown structures and coefficient transports without unfolding them.
end AlgebraicGeometry.ProEtale.CondensedRing
