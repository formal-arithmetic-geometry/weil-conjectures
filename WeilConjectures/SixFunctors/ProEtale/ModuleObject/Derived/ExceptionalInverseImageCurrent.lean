/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCriteria
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCoefficientIso
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import Mathlib.CategoryTheory.Skeletal
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesStructural
import WeilConjectures.AlgebraicGeometry.Integral.IntegralConstructibleCompactness
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.SixFunctors.Etale.ForgetModuleCohomology
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
import Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import WeilConjectures.CategoryTheory.CompactFactorThroughThick
import WeilConjectures.CategoryTheory.CompactHomHocolim
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.ObjectProperty.Small
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import Mathlib.CategoryTheory.ObjectProperty.Ind
import WeilConjectures.AlgebraicGeometry.Ambient.AmbientIndDerivedTriangulated
import WeilConjectures.AlgebraicGeometry.Ambient.AmbientIndDerivedSums
import WeilConjectures.CategoryTheory.SmoothPurity.TruncationsAndHomotopyColimits
import WeilConjectures.CategoryTheory.CompactObjectsThick
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartFullFaithfulness
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleFilteredColimits
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartKernelsCokernels
import Mathlib.AlgebraicGeometry.QuasiAffine
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartCanonicalPresentation
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleExtensions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import WeilConjectures.Compactification.Dense
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.AlgebraicGeometry.DetIndHeartIISums
public import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingCompactificationCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# Exceptional inverse image for the current admissible coefficients

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-coefficients-constructible/sec-n-brown/sk-thm-existence/_section.md,
clauses (1)--(4), with the standing field convention in part-six-operations/prose-P1-01.md
(blueprint: sk-thm-existence).

The categories are the recorded full subcategories of the unbounded derived category of
internal modules over the pulled-back condensed ring. The algebraic-closure coefficient
in `IsLocalizingAdmissibleCoefficient` is the finite-subextension-valued condensed ring.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

local notation "S(" T ")" =>
  (constantModelBoundedConstructible Λ T ⊓ fun K ↦ DerivedCategory.finiteTorAmplitude _ K)
local notation "L(" T ")" => localizingClosureProEtale Λ T

/-- The existing constructible finite-Tor predicate is replete. -/
private instance ctf_replete
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    (shriekCoefficientCtf (Λ := Λ) T).IsClosedUnderIsomorphisms := by
  let _ := (constantModelConstructibleFiniteTor_wellDefined Λ T).2.1
  let _ := (constantModelConstructibleFiniteTor_wellDefined Λ T).2.2.2.1
  exact inferInstanceAs ((constantModelBoundedConstructible Λ T ⊓
    _root_.DerivedCategory.finiteTorAmplitude _).IsClosedUnderIsomorphisms)

/-- An exact sum-preserving functor carries generators and their localizing closures. -/
private theorem map_closure
    {C D : Type v} [Category.{w} C] [Category.{w} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [PreservesColimitsOfSize.{v, v} F]
    (S : ObjectProperty C) (T : ObjectProperty D) (hST : S ≤ T.inverseImage F) :
    localizingClosure S ≤ (localizingClosure T).inverseImage F := by
  intro M hM P hP hTP
  let _ := hP.1
  let _ := hP.2.1
  have hPF : IsLocalizingSubcategory (P.inverseImage F) := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I H hH hHP
    let _ := hH
    have hFH : HasColimit (H ⋙ F) :=
      ⟨F.mapCocone (colimit.cocone H), isColimitOfPreserves F (colimit.isColimit H)⟩
    exact P.prop_of_iso (preservesColimitIso F H).symm (hP.2.2 (H ⋙ F) hFH hHP)
  exact hM _ hPF (fun N hN ↦ hTP _ (hST N hN))

/-- Transport preservation along the recorded coefficient comparison on the actual
intersection-defined localizing closures. This reuses the coefficient-transport proof
of det-existence-restriction-right: inverse scalar restriction preserves generators,
triangles and all sums, so it identifies the closures; conjugate the supplied adjunction
and use right-adjoint uniqueness. Source: det-existence-restriction.proof.md,
coefficient-preservation paragraph (blueprint: lem-sfb-shriek-coefficient-isomorphism). -/
private theorem preservation_of_coefficient_iso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (h' : ∀ K, localizingClosureProEtale Λ' X K → localizingClosureProEtale Λ' Y
      ((rightDerivedLowerShriekOfCompactification Λ' c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (G' : (localizingClosureProEtale Λ' Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ' X).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G)
    (adj' : localizingLowerShriek Λ' c.obj.obj h' ⊣ G')
    (hp : ∀ K : (localizingClosureProEtale Λ' Y).FullSubcategory,
      shriekCoefficientCtf (Λ := Λ') Y K.obj →
        shriekCoefficientCtf (Λ := Λ') X (G'.obj K).obj) :
    ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
      shriekCoefficientCtf (Λ := Λ) Y K.obj →
        shriekCoefficientCtf (Λ := Λ) X (G.obj K).obj := by
  classical
  let q (T : Scheme.{u}) : condensedRingObj Λ T ≅ condensedRingObj Λ' T :=
    (upperStarFromPoint T).mapIso ((Mon.forget _).mapIso e)
  have (T : Scheme.{u}) : IsMonHom (q T).hom :=
    inferInstanceAs (IsMonHom ((upperStarFromPoint T).map e.hom.hom))
  have (T : Scheme.{u}) : IsMonHom (q T).inv :=
    inferInstanceAs (IsMonHom ((upperStarFromPoint T).map e.inv.hom))
  let H (T : Scheme.{u}) := CategoryTheory.Equivalence.mk
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (q T).inv)
    (Mod.comap (q T).hom)
    ((Mod.comapId _).symm ≪≫ Mod.comapCongr (q T).hom_inv_id.symm ≪≫
      Mod.comapComp (q T).hom (q T).inv)
    ((Mod.comapComp (q T).inv (q T).hom).symm ≪≫
      Mod.comapCongr (q T).inv_hom_id ≪≫ Mod.comapId _)
  have (T : Scheme.{u}) : (H T).functor.Additive :=
    inferInstanceAs ((Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (q T).inv).Additive)
  have (T : Scheme.{u}) : (H T).inverse.Additive :=
    inferInstanceAs ((Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (q T).hom).Additive)
  let d (T : Scheme.{u}) := (H T).mapDerivedCategory
  have hlocal (T : Scheme.{u}) : (localizingClosureProEtale Λ' T).inverseImage
      (d T).functor = localizingClosureProEtale Λ T := by
    let S := shriekCoefficientCtf (Λ := Λ) T
    let S' := shriekCoefficientCtf (Λ := Λ') T
    obtain ⟨_, htri, hiso, _, _, _⟩ := brownHypotheses_structural Λ T
    obtain ⟨_, htri', hiso', _, _, _⟩ := brownHypotheses_structural Λ' T
    let _ := htri
    let _ := hiso
    let _ := htri'
    let _ := hiso'
    have hf : localizingClosureProEtale Λ T ≤
        (localizingClosureProEtale Λ' T).inverseImage (d T).functor :=
      map_closure (H T).functor.mapDerivedCategory S S'
        (fun K hK ↦ constantModelCtf_coefficientIso e T ⟨K, hK⟩)
    have hb : localizingClosureProEtale Λ' T ≤
        (localizingClosureProEtale Λ T).inverseImage (d T).inverse :=
      map_closure (H T).inverse.mapDerivedCategory S' S
        (fun K hK ↦ constantModelCtf_coefficientIso e.symm T ⟨K, hK⟩)
    funext K
    apply propext
    exact ⟨fun hK ↦ (localizingClosureProEtale Λ T).prop_of_iso
      ((d T).unitIso.app K).symm (hb _ hK), hf K⟩
  obtain ⟨_, htriX, hisoX, _, _, _⟩ := brownHypotheses_structural Λ' X
  obtain ⟨_, htriY, hisoY, _, _, _⟩ := brownHypotheses_structural Λ' Y
  let _ := htriX
  let _ := htriY
  let _ := hisoX
  let _ := hisoY
  let EX := (d X).congrFullSubcategory (hlocal X)
  let EY := (d Y).congrFullSubcategory (hlocal Y)
  let F := localizingLowerShriek Λ c.obj.obj h
  let F' := localizingLowerShriek Λ' c.obj.obj h'
  let comp : F ⋙ EY.functor ≅ EX.functor ⋙ F' :=
    ((localizingClosureProEtale Λ' Y).fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft (localizingClosureProEtale Λ X).ι
        (shriekCoefficientCompactificationIso e c))
  let left : (EX.inverse ⋙ F) ⋙ EY.functor ≅ F' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft EX.inverse comp ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight EX.counitIso F' ≪≫ F'.leftUnitor
  let conj := (EX.symm.toAdjunction.comp adj).comp EY.toAdjunction
  let r := (conj.ofNatIsoLeft left).rightAdjointUniq adj'
  intro K hK
  have hp' := hp (EY.functor.obj K) (constantModelCtf_coefficientIso e Y ⟨K.obj, hK⟩)
  have ht : shriekCoefficientCtf (Λ := Λ') X (EX.functor.obj (G.obj K)).obj := by
    let i := r.app (EY.functor.obj K)
    let j := EX.functor.mapIso (G.mapIso (EY.unitIso.app K).symm)
    exact (shriekCoefficientCtf (Λ := Λ') X).prop_of_iso
      ((localizingClosureProEtale Λ' X).ι.mapIso (i.symm ≪≫ j)) hp'
  have hback := constantModelCtf_coefficientIso e.symm X
    ⟨(EX.functor.obj (G.obj K)).obj, ht⟩
  exact (shriekCoefficientCtf (Λ := Λ) X).prop_of_iso
    ((d X).unitIso.app (G.obj K).obj).symm hback

/-- The four assertions of the current exceptional-inverse-image theorem. A small skeleton
is given by representatives exhausting the isomorphism classes without repetitions.
The lower shriek has exactly the object and morphism maps of the chosen Nagata composite,
compared with every other compactification. The restricted adjunction is obtained from
this same ambient adjunction: its Hom equivalence agrees after the full inclusions.

Source: latest blueprint, part-six-operations/sec-coefficients-constructible/sec-n-brown/
sk-thm-existence/_section.md, clauses (1)--(4), and prose-P1-01.md, standing field scope
(blueprint: sk-thm-existence).

Proof plan (the node's six steps):
1. The base-field cohomological-dimension theorem gives finite ell-cohomological dimension
   for a finite or algebraically closed field. Apply sk-lem-brown-hypotheses to obtain
   compactness and generation. Essential smallness gives a small skeletal model; take
   one representative in each isomorphism class and transport generation to this family.
2. Both schemes are qcqs over the affine base. Separated cancellation, locally finite-type
   cancellation and quasi-compactness permanence show that f is separated and finite type.
   Nagata gives its chosen compactification inside the same setting.
3. det-sf-comp-coherence-single restricts the compactification composite to an exact,
   coproduct-preserving functor of the closures preserving Dctf. The cocycle theorem
   identifies the functors from all compactifications independently of refinement.
4. Apply sk-prop-sf-existence to this same functor and the finite-cd bound. Brown
   representability gives its right adjoint; transposing shifts makes it exact.
5. For finite coefficients apply sk-prop-sf-rf-shriek-preservation to this adjoint.
   For O_E, E and the finite-subextension-valued algebraic closure apply sk-thm-restriction.
   The bottom-extension coefficient identifications and coefficient-isomorphism theorem
   give the Z_ell and Q_ell cases, preserving and reflecting Dctf.
6. Use lem-integral-ctf-equals-bc where the nonfinite restriction input is expressed with
   Dbc. Both functors preserve Dctf. Apply the fully faithful adjunction-restriction lemma
   to the full inclusions; its Hom formula is exactly the last equality below.
-/
theorem exceptionalInverseImage_exists_current
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (_hk : Finite k ∨ IsAlgClosed k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    ∃ (hX : L(X.left).IsTriangulated) (hY : L(Y.left).IsTriangulated)
      (hSX : S(X.left) ≤ L(X.left)) (hSY : S(Y.left) ≤ L(Y.left))
      (_h : ∀ K, L(X.left) K → L(Y.left)
        ((rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f)).obj K))
      (sX : HasCoproducts.{u + 1} L(X.left).FullSubcategory)
      (sY : HasCoproducts.{u + 1} L(Y.left).FullSubcategory),
      (fun [_triX : L(X.left).IsTriangulated] [_triY : L(Y.left).IsTriangulated]
          [_sumsX : HasCoproducts.{u + 1} L(X.left).FullSubcategory]
          [_sumsY : HasCoproducts.{u + 1} L(Y.left).FullSubcategory] ↦
        ∃ (F : L(X.left).FullSubcategory ⥤ L(Y.left).FullSubcategory)
          (sF : F.CommShift ℤ),
          (fun [_shiftF : F.CommShift ℤ] ↦
        (F ⋙ L(Y.left).ι = L(X.left).ι ⋙
          rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f)) ∧
        (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
          IsCompactObject.{u + 1} ((ObjectProperty.ιOfLE hSX).obj K)) ∧
        (LocallySmall.{u + 1} (ConstantModelConstructibleFiniteTor Λ X.left) ∧
          ∃ (I : Type (u + 1)) (E : I → ConstantModelConstructibleFiniteTor Λ X.left),
          (∀ K, ∃ i, Nonempty (E i ≅ K)) ∧
          (∀ i j, Nonempty (E i ≅ E j) → i = j) ∧
          IsTriangulatedGeneratingFamily (fun i ↦ (ObjectProperty.ιOfLE hSX).obj (E i))) ∧
        F.IsTriangulated ∧
        (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
          F) ∧
        (∀ c : Compactification f.left, Nonempty
          (F ⋙ L(Y.left).ι ≅
            L(X.left).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)) ∧
        ∃ (hF : ∀ K : L(X.left).FullSubcategory, S(X.left) K.obj →
            S(Y.left) (F.obj K).obj)
          (G : L(Y.left).FullSubcategory ⥤ L(X.left).FullSubcategory)
          (s : G.CommShift ℤ),
          (fun [_comm : G.CommShift ℤ] ↦
            G.IsTriangulated ∧
            ∃ (adj : F ⊣ G)
              (hG : ∀ N : L(Y.left).FullSubcategory,
                S(Y.left) N.obj → S(X.left) (G.obj N).obj),
              ∃ adjSmall :
                (S(Y.left).lift
                  ((ObjectProperty.ιOfLE hSX) ⋙ F ⋙ L(Y.left).ι)
                  (fun K ↦ hF _ K.property)) ⊣
                (S(X.left).lift
                  ((ObjectProperty.ιOfLE hSY) ⋙ G ⋙ L(X.left).ι)
                  (fun N ↦ hG _ N.property)),
                ∀ (M : ConstantModelConstructibleFiniteTor Λ X.left)
                  (N : ConstantModelConstructibleFiniteTor Λ Y.left)
                  (a : F.obj
                    ((ObjectProperty.ιOfLE hSX).obj M) ⟶
                    (ObjectProperty.ιOfLE hSY).obj N),
                  (adjSmall.homEquiv M N (ObjectProperty.homMk a.hom)).hom =
                    (adj.homEquiv ((ObjectProperty.ιOfLE hSX).obj M)
                      ((ObjectProperty.ιOfLE hSY).obj N) a).hom)
            (_comm := s))
          (_shiftF := sF))
        (_triX := hX) (_triY := hY) (_sumsX := sX) (_sumsY := sY) := by
  sorry

/-- The constructible restriction supplied by the current Brown theorem. The equality
fixes the compact-support object and morphism maps, and the adjunction determines the
right functor up to its unique counit-compatible isomorphism.
Source: sk-thm-existence (3)--(4) (blueprint: sk-thm-existence). -/
structure CurrentConstructibleExceptionalData
    {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) where
  lower : ConstantModelConstructibleFiniteTor Λ X.left ⥤
    ConstantModelConstructibleFiniteTor Λ Y.left
  lower_eq : lower ⋙ S(Y.left).ι = S(X.left).ι ⋙
    rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f)
  right : ConstantModelConstructibleFiniteTor Λ Y.left ⥤
    ConstantModelConstructibleFiniteTor Λ X.left
  adjunction : lower ⊣ right

/-- Extract only the actual constructible adjunction from the current existence theorem.
Its left functor is fixed by `lower_eq`; its right functor is selected through this
adjunction, rather than through an arbitrary object-existence assertion.
Source: sk-thm-existence (3)--(4) (blueprint: sk-thm-existence). -/
noncomputable def currentConstructibleExceptionalData
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : Finite k ∨ IsAlgClosed k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    CurrentConstructibleExceptionalData Λ f :=
  Classical.choice (by
    obtain ⟨hX, hY, hSX, hSY, h, sX, sY, H⟩ :=
      exceptionalInverseImage_exists_current Λ ℓ k hk f hΛ
    let := hX
    let := hY
    let := sX
    let := sY
    obtain ⟨F, sF, H⟩ := H
    let := sF
    obtain ⟨eF, _, _, _, _, _, hF, G, sG, H⟩ := H
    let := sG
    obtain ⟨_, adj, hG, adjSmall, _⟩ := H
    refine ⟨⟨_, ?_, _, adjSmall⟩⟩
    exact congrArg (fun H ↦ (ObjectProperty.ιOfLE hSX) ⋙ H) eF)

end AlgebraicGeometry.ProEtale.CondensedRing
