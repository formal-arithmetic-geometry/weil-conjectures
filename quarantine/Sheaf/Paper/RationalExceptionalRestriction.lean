/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.RationalRestrictionGlue
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.Paper.CompactificationLocalizing
import Sheaf.Paper.ContinuousQbarExceptionalPreservation
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Rational exceptional inverse image preserves constructibility

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-restriction,
statement and four proof paragraphs (blueprint: sk-thm-restriction).

The right adjoint is specified by its adjunction to the recorded localizing
compactification functor. The two functor equalities identify the restrictions
on objects and maps with those same functors, using the full inclusions.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The full inclusion of Dctf into its localizing closure. On objects and maps
this is the ambient identity: membership follows directly from the intersection
that defines the closure, since every intersected property contains Dctf.
Source: blueprint sk-thm-restriction, last proof paragraph and
sk-def-localizing-closure, defining intersection (blueprint: sk-thm-restriction). -/
noncomputable def constantModelFiniteTorToLocalizing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ConstantModelConstructibleFiniteTor Λ X ⥤
      (localizingClosureProEtale Λ X).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K hK _P _hP hSP ↦ hSP K hK)

namespace CondensedRing

/-- For rational coefficients the exceptional inverse image on the localizing
closures preserves Dctf, and both functors restrict to an adjoint pair on Dctf.
The equalities after the full inclusions specify the actual restrictions of the
compactification lower shriek and its given right adjoint, including their maps.
Source: blueprint main-20261015, sk-thm-restriction, statement and proof
(blueprint: sk-thm-restriction).

Proof:
1. Finite type and separatedness over the field make X and Y qcqs. Each of the
   original coefficient alternatives is admissible in sk-def-localizing-closure.
   Apply det-sf-comp-coherence-single to the given boundary compactification:
   its actual lower shriek preserves bounded constructible finite-Tor objects.
2. Split the original coefficient alternatives. For a finite extension E,
   det-thm-restriction-glue proves bounded constructibility of the supplied G K.
   Its geometric argument uses affine factorizations, affine-space purity,
   closed support and finite-cover gluing. The predicate equality of
   det-def-localizing-closure-ctf-equals-bc on X supplies finite Tor amplitude.
   Both invocations use only their finite-extension alternatives.
3. For C(-, Qbar_ell), apply
   lem-sfb-continuous-qbar-exceptional-preservation with the same f, c, h, G and
   supplied adjunction. This isolates the geometric preservation component for
   this coefficient; no identification with the finite-subextension-valued ring
   is asserted. The lemma follows the unit's same affine-factorization,
   affine-space-purity, closed-support and finite-cover route.
4. Every property in the intersection defining sk-def-localizing-closure contains
   Dctf, giving its full inclusion constantModelFiniteTorToLocalizing. Use the
   preservation statements to lift the two original functors to Dctf. The
   equalities after these full inclusions hold by reflexivity, including maps.
   Apply Adjunction.restrictFullyFaithful to the supplied adjunction. Its Hom
   equivalences therefore give the restricted adjunction without choosing any
   new ambient functor or changing the original coefficient hypothesis.
-/
theorem rationalExceptional_preserves_constructibleFiniteTor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ))))
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (_adj : localizingLowerShriek Λ c.obj.obj h ⊣ G) :
    (∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
      (constantModelBoundedConstructible Λ Y K.obj ∧
        DerivedCategory.finiteTorAmplitude _ K.obj) →
      constantModelBoundedConstructible Λ X (G.obj K).obj ∧
        DerivedCategory.finiteTorAmplitude _ (G.obj K).obj) ∧
    ∃ (F₀ : ConstantModelConstructibleFiniteTor Λ X ⥤
        ConstantModelConstructibleFiniteTor Λ Y)
      (G₀ : ConstantModelConstructibleFiniteTor Λ Y ⥤
        ConstantModelConstructibleFiniteTor Λ X),
      F₀ ⋙ constantModelFiniteTorToLocalizing Λ Y =
        constantModelFiniteTorToLocalizing Λ X ⋙ localizingLowerShriek Λ c.obj.obj h ∧
      G₀ ⋙ constantModelFiniteTorToLocalizing Λ X =
        constantModelFiniteTorToLocalizing Λ Y ⋙ G ∧
      Nonempty (F₀ ⊣ G₀) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated
    (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated
    (Y ↘ Spec (.of k))
  have hadmissible : IsLocalizingAdmissibleCoefficient ℓ Λ := by
    rcases _hΛ with hE | hQ
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, hE⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hQ)))))
  have hF := (compactification_localizing Λ ℓ k f c hadmissible).2.2.2
  have hG : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
      (constantModelBoundedConstructible Λ Y K.obj ∧
        DerivedCategory.finiteTorAmplitude _ K.obj) →
      constantModelBoundedConstructible Λ X (G.obj K).obj ∧
        DerivedCategory.finiteTorAmplitude _ (G.obj K).obj := by
    rcases _hΛ with hE | hQ
    · have hcoeff :
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
          (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
            Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
            Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) :=
        Or.inr (Or.inr (Or.inl ⟨E, Or.inr hE⟩))
      have hEqX := (localizingClosure_ctf_equals_bc ℓ X Λ hcoeff).1.2.2.1
      have hcoeff' : Nonempty (Mon.mk Λ ≅ Mon.mk
          ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
              (Profinite.padicSubfieldCondensedRing ℓ E.1))) ∨
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := Or.inl hE
      obtain ⟨_, _, _, hGbc, _⟩ :=
        (rationalRestrictionGlue.{u, u} Λ ℓ E.1 hcoeff' k (ringChar k)
          (Fact.out : ringChar k ≠ ℓ) f c h G _adj).2
      intro K hK
      exact (congrFun hEqX _).mpr (hGbc K hK.1)
    · exact continuousQbarExceptional_preserves_constructibleFiniteTor
        Λ ℓ k f hQ c h G _adj
  refine ⟨hG, ?_⟩
  let F₀ : ConstantModelConstructibleFiniteTor Λ X ⥤
      ConstantModelConstructibleFiniteTor Λ Y :=
    (constantModelBoundedConstructible Λ Y ⊓
      DerivedCategory.finiteTorAmplitude _).lift
      ((constantModelBoundedConstructible Λ X ⊓
        DerivedCategory.finiteTorAmplitude _).ι ⋙
          rightDerivedLowerShriekOfCompactification Λ c.obj.obj)
      (fun K ↦ hF K.obj K.property)
  let G₀ : ConstantModelConstructibleFiniteTor Λ Y ⥤
      ConstantModelConstructibleFiniteTor Λ X :=
    (constantModelBoundedConstructible Λ X ⊓
      DerivedCategory.finiteTorAmplitude _).lift
      (constantModelFiniteTorToLocalizing Λ Y ⋙ G ⋙
        (localizingClosureProEtale Λ X).ι)
      (fun K ↦ hG ((constantModelFiniteTorToLocalizing Λ Y).obj K) K.property)
  have eF : F₀ ⋙ constantModelFiniteTorToLocalizing Λ Y =
      constantModelFiniteTorToLocalizing Λ X ⋙ localizingLowerShriek Λ c.obj.obj h := by
    rfl
  have eG : G₀ ⋙ constantModelFiniteTorToLocalizing Λ X =
      constantModelFiniteTorToLocalizing Λ Y ⋙ G := by
    rfl
  refine ⟨F₀, G₀, eF, eG, ⟨?_⟩⟩
  exact _adj.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE _) (ObjectProperty.fullyFaithfulιOfLE _)
    (eqToIso eF.symm) (eqToIso eG.symm)

end CondensedRing

end AlgebraicGeometry.ProEtale
