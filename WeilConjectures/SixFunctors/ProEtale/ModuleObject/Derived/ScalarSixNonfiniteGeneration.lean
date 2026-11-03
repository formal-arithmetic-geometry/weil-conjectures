/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFieldGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNativeIntegralGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixGenerationTransport
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison

/-! # Integral and field generation in the scalar-perfect presentation.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (1), generators.
(blueprint: lem-route-sfb-nonfinite-scalar-generation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

/-- Integral and field generation in the scalar-perfect presentation.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (1), generators.
(blueprint: lem-route-sfb-nonfinite-scalar-generation).

Proof in words: first use the displayed coefficient isomorphism to move to its native
presentation, with the exact monoidal equivalence on modules and derived categories.
For integers of a finite extension specialize the integral generation argument:
resolve each locally finitely presented stratum module by two locally free modules.
Their degree-zero scalar complexes give scalar-perfect generators. Exact extension,
the finite locally closed extension tower and bounded derived devissage then give
a finite witness. The integral constant-model comparison supplies the constructible
cohomology hypothesis, and the support reconstruction comparison identifies arbitrary
open-then-closed factorizations with the canonical image factorization.
For finite extensions of Q_ell and the algebraic
closure use the coefficient-heart lisse filtration. Each lisse module is finite free on its
specified cover, so the degree-zero complex of that free scalar module supplies a
scalar-perfect model. The ordinary exact extension and its derived extension agree
with the stated open-then-closed derived composite. Short exact sequence triangles
and the finite lisse filtration give finite extension witnesses for sheaves. Bounded
derived devissage gives the witnesses for complexes. Z_ell and Q_ell are the bottom
finite subextension cases. Transport
back across the given isomorphism. No completed derived category or infinite
coproduct enters the construction; zero and empty cases use rank zero. -/
theorem sfbNonfiniteScalarGeneration (ell : ℕ) [Fact ell.Prime]
    {Λ : ScalarSixRing.{u}}
    (hΛ : Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ell])) ∨
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ell])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
    (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicIntegersRingObj ell E))) ∨
    Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    ∃ n : ℕ, (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
      ).retractClosure K.obj := by
  classical
  have hfield (E : PadicAlgCl.FiniteIntermediateField ell)
      (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E)) :
      ∃ n : ℕ, (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
        ).retractClosure K.obj := by
    apply sfbGeneration_coefficientIso ell
      (Γ := ⟨coefficientHeartRingObj (Profinite.padicSubfieldCondensedRing ell E.1)⟩)
      e k X _ K
    intro L
    exact sfbNativeFieldGeneration ell (Profinite.padicSubfieldCondensedRing ell E.1)
      (Or.inl ⟨E.1, E.2, rfl⟩) k X L.obj L.property.1
  have hintegral (E : PadicAlgCl.FiniteIntermediateField ell)
      (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) :
      ∃ n : ℕ, (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
        ).retractClosure K.obj := by
    have : FiniteDimensional ℚ_[ell] E.1 := E.2
    let er := integerRingSheafIso.{u} ell ⟨E.1, E.2⟩
    let ea := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
    have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ er.hom
    let e' := Mon.mkIso' ea
    apply sfbGeneration_coefficientIso ell
      (Γ := ⟨DerivedNakayama.integerRing ell (ULift.{u} E.1)⟩)
      (e ≪≫ e') k X _ K
    intro L
    exact sfbNativeIntegralGeneration ell (ULift.{u} E.1) k X L
  rcases hΛ with hZ | hQ | hE | hO | hA
  · obtain ⟨e⟩ := hZ
    obtain ⟨_, _, _, _, _, _, _, _, _, zIso, _⟩ :=
      Profinite.base_coefficient_condensed_identification.{u} ell
    exact hintegral ⟨⊥, inferInstance⟩ (e ≪≫ zIso)
  · obtain ⟨e⟩ := hQ
    obtain ⟨_, _, _, _, _, _, _, _, qIso, _, _⟩ :=
      Profinite.base_coefficient_condensed_identification.{u} ell
    exact hfield ⟨⊥, inferInstance⟩ (e ≪≫ qIso)
  · obtain ⟨E, ⟨e⟩⟩ := hE
    exact hfield E e
  · obtain ⟨E, ⟨e⟩⟩ := hO
    exact hintegral E e
  · obtain ⟨e⟩ := hA
    apply sfbGeneration_coefficientIso ell
      (Γ := ⟨coefficientHeartRingObj (Profinite.padicAlgClCondensedRing ell)⟩) e k X _ K
    intro L
    exact sfbNativeFieldGeneration ell (Profinite.padicAlgClCondensedRing ell)
      (Or.inr rfl) k X L.obj L.property.1

end AlgebraicGeometry.ProEtale.CondensedRing
