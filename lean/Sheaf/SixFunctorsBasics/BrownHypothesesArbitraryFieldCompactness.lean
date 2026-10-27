module

public import Sheaf.SixFunctorsBasics.BrownHypothesesStructural
public import WeilConjectures.CategoryTheory.CompactObject
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
import Mathlib.CategoryTheory.ObjectProperty.Small
import Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness
import all Sheaf.SixFunctors.BrownHypothesesSmall
import Sheaf.Paper.IntegralConstructibleCompactness
import Sheaf.Paper.LocalizingClosureCtfEqualsBc

/-!
# Supported objectwise compactness results for Brown hypotheses

The false unrestricted split is retired. The finite-field and Ext-bounded integral
results retain all their hypotheses; the parent Brown assertion remains disputed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- The objectwise compactness step holds over the geometric field of a finite-field
 datum. Essential smallness follows from the Noetherian smallness theorem.
 The coproduct structure may be any one, including the structure used by the caller.

 Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, compactness paragraph,
 and sk-lem-brown-hypotheses-generation.proof.md, compactness of representatives.
 (blueprint: p3-brown-finite-field-object-compactness).

 Proof: finite type over a field makes X compact and locally Noetherian. The bounded
 constant-model category is essentially small, hence so is its finite-Tor subcategory.
 Take a skeleton of a small category equivalent to this subcategory. Its representatives
 satisfy the surjectivity and skeletal hypotheses of
 brownHypothesesFiniteFieldCompactness. A given object is isomorphic to one of these
 representatives. Lift this isomorphism to the full localizing subcategory and transport
 compactness using the finite-support characterization. Proof irrelevance identifies
 the coproduct structure returned by the representative theorem with the caller's.
 This theorem retains all finite-field and coefficient hypotheses of that input; it
 does not assert unrestricted arbitrary-field compactness. -/
theorem brownHypotheses_finiteField_object_compactness
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (hSums : HasCoproducts.{u + 1}
      (localizingClosureProEtale Λ X).FullSubcategory)
    (K : (localizingClosureProEtale Λ X).FullSubcategory)
    (hK : constantModelBoundedConstructible Λ X K.obj ∧
      DerivedCategory.finiteTorAmplitude _ K.obj) :
    @IsCompactObject _ _ _ hSums K := by
  classical
  let S := constantModelBoundedConstructible Λ X ⊓
    fun K ↦ DerivedCategory.finiteTorAmplitude _ K
  let L := localizingClosureProEtale Λ X
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of D.k))
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of D.k))
  have := small_bounded_constant_models Λ X
  have hsmall : ObjectProperty.EssentiallySmall.{u + 1} S :=
    ObjectProperty.EssentiallySmall.of_le (fun _ h ↦ h.1)
  obtain ⟨J, hJ, ⟨e⟩⟩ := (ObjectProperty.exists_equivalence_iff S).mpr hsmall
  let _ := hJ
  let G := Skeleton J
  let H : G ⥤ S.FullSubcategory := fromSkeleton J ⋙ e.inverse
  let g : G → ConstantModelConstructibleFiniteTor Λ X := H.obj
  have hG (C : ConstantModelConstructibleFiniteTor Λ X) :
      ∃ i : G, Nonempty (C.obj ≅ (g i).obj) := by
    refine ⟨toSkeleton (e.functor.obj C), ⟨?_⟩⟩
    exact S.ι.mapIso (e.unitIso.app C ≪≫
      e.inverse.mapIso (fromSkeletonToSkeletonIso (e.functor.obj C)).symm)
  have hsk (i j : G) (h : Nonempty ((g i).obj ≅ (g j).obj)) : i = j := by
    obtain ⟨q⟩ := h
    exact skeleton_skeletal J ⟨H.preimageIso (S.isoMk q)⟩
  obtain ⟨hcop, hc⟩ := brownHypothesesFiniteFieldCompactness D ℓ hℓ X Λ (by
    rcases hΛ with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))) G g hG hsk
  have heq : hcop = hSums := Subsingleton.elim _ _
  subst hcop
  let _ := hSums
  have hL (i : G) : L (g i).obj := fun P _ hSP ↦ hSP _ (g i).property
  obtain ⟨i, ⟨q⟩⟩ := hG ⟨K.obj, hK⟩
  let q' : K ≅ (⟨(g i).obj, hL i⟩ : L.FullSubcategory) := L.isoMk q
  exact (isCompactObject_iff_isCompactObj K).mpr
    (((isCompactObject_iff_isCompactObj _).mp (hc hL i)).of_iso q')

/-- The arbitrary-field objectwise compactness step for integral coefficients, with
 the uniform constructible Ext bound retained as an explicit hypothesis.

 Source: blueprint latest, sk-prop-int-compactness-compact.md, compactness clause,
 and sk-lem-brown-hypotheses.proof.md, integral compactness paragraph.
 (blueprint: p3-brown-integral-object-compactness-with-ext-bound).

 Proof: apply integralConstructibleCompactness with the given bound. For integral
 coefficients the constructible finite-Tor property equals the bounded constructible
 property, so their localizing closures agree. Rewrite the compactness assertion
 along this equality. Proof irrelevance identifies its coproduct structure with the
 caller's structure, and the bounded-constructible part of hK supplies membership.
 No bound for the base field is inferred from its positive characteristic. -/
theorem brownHypotheses_integral_object_compactness_of_ext_bounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X → ℕ)
    (hd : ∀ (C N : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X)
      (q : ℤ), (d C : ℤ) < q →
        Subsingleton (((DerivedCategory.singleFunctor _ 0).obj C.obj) ⟶
          ((DerivedCategory.singleFunctor _ 0).obj N.obj)⟦q⟧))
    (hSums : HasCoproducts.{u + 1}
      (localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E) X).FullSubcategory)
    (K : (localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E) X).FullSubcategory)
    (hK : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X K.obj ∧
      DerivedCategory.finiteTorAmplitude _ K.obj) :
    @IsCompactObject _ _ _ hSums K := by
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  let Λ := Profinite.padicIntegersRingObj ℓ E
  let B := constantModelBoundedConstructible Λ X
  let L := localizingClosureProEtale Λ X
  have hctf := (localizingClosure_ctf_equals_bc ℓ X Λ
    (Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩)))).1
  have hL : L = localizingClosure B := hctf.2.2.2.1
  have hc := (integralConstructibleCompactness ℓ E k p hp hpℓ X d hd).2.2
  change ∃ hc : HasCoproducts.{u + 1} (localizingClosure B).FullSubcategory,
    ∀ K : (localizingClosure B).FullSubcategory, B K.obj →
      @IsCompactObject _ _ _ hc K at hc
  rw [← hL] at hc
  obtain ⟨hcop, hc⟩ := hc
  have heq : hcop = hSums := Subsingleton.elim _ _
  subst hcop
  exact hc K hK.1

end CategoryTheory
