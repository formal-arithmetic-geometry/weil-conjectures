/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperConstructibleClosedExchangeHeart
import all WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleFilteredColimits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AmbientQcqsExchangeCanonicalShifts
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators

/-! # Closed proper base change on bounded constructible finite-Tor inputs

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), proper base change along the closed
complement (blueprint: lem-sfb-qcqs-proper-constructible-closed-base-change).

The exchange is the actual unit--square--counit mate on ordinary unbounded internal module
objects. The coefficient predicate retains exactly the node's norm-topological convention.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The five coefficient families A, Z_l, Q_l, E and O_E with the discrete or induced norm-topological
convention. The ring of all continuous maps to the algebraic closure is not admissible (2026-10-25).

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-localizing-closure,
coefficient convention, restricted to the exact list in the present theorem
(blueprint: lem-sfb-qcqs-proper-constructible-closed-base-change). -/
def IsNormTopologicalLocalizingAdmissibleCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] : Prop :=
  (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
    Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E)))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- Finite Postnikov induction for a shift-compatible morphism of triangulated functors.
Keeping this argument abstract prevents expansion of concrete coefficient pullbacks. -/
private theorem isIso_of_bounded_cohomology
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (F G : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [G.CommShift ℤ]
    (hF : F.IsTriangulated) (hG : G.IsTriangulated) (τ : F ⟶ G)
    (hshift : ∀ (n : ℤ) (K : DerivedCategory A),
      τ.app (K⟦n⟧) ≫ (G.commShiftIso n).hom.app K =
        (F.commShiftIso n).hom.app K ≫ (τ.app K)⟦n⟧')
    (P : ObjectProperty A) (hPiso : P.IsClosedUnderIsomorphisms)
    (hP : ∀ M, P M → IsIso (τ.app ((DerivedCategory.singleFunctor A 0).obj M)))
    (K : DerivedCategory A) (hb : DerivedCategory.TStructure.t.bounded K)
    (hK : ∀ n : ℤ, P ((DerivedCategory.homologyFunctor A n).obj K)) :
    IsIso (τ.app K) := by
  have := hF
  have := hG
  have := hPiso
  have : NatTrans.CommShift τ ℤ := ⟨fun n ↦ by
    apply NatTrans.ext
    funext M
    exact (hshift n M).symm⟩
  exact DerivedCategory.prop_of_bounded τ.isoLocus P hP K hb hK

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  upperStar lowerStar upperStarFromPoint condensedAmbientExchange
  modulePullbackDerivedCommShift modulePushforwardDerivedCommShift modulePullbackExactComparison

/-- Closed proper base change over any qcqs base, on bounded constructible complexes of
finite Tor amplitude, for the discrete or induced ell-adic admissible coefficient list.

Source: blueprint main-20261015, det-sf-comp-coherence-refinement.proof.md, (2), the
closed-complement calculation on the bounded constructible finite-Tor generator
(blueprint: lem-sfb-qcqs-proper-constructible-closed-base-change).

Proof: Properness of q makes Y qcqs. The degree-zero closed-test theorem proves
exchange on every constructible module sheaf, for each of the six coefficient families;
the coefficient disjunction lists the same six families. The actual ambient
exchange carries the canonical shift structures and is a transformation of triangulated
functors. Its isomorphism locus is therefore replete and triangulated. Constructibility
is invariant under module isomorphisms: transport each finite scalar model along the
induced isomorphism on the stratum and its pro-etale trivializing cover. Finite Postnikov
induction now places every bounded complex with constructible cohomology in this
isomorphism locus. Apply this to L; its finite Tor amplitude is not needed in the
induction. -/
theorem qcqs_proper_constructible_closed_baseChange
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsNormTopologicalLocalizingAdmissibleCoefficient ℓ Λ)
    {S X Y C : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (q : Y ⟶ S) [IsProper q] (f : X ⟶ Y) [IsProper f]
    (c : C ⟶ Y) [IsClosedImmersion c]
    [QuasiCompact (Scheme.Opens.ι (X := Y)
      ⟨(Set.range c)ᶜ, c.isClosedEmbedding.isClosed_range.isOpen_compl⟩)]
    (L : ConstantModelConstructibleFiniteTor Λ X) :
    IsIso ((condensedAmbientExchange Λ
      (g' := pullback.fst f c) (f' := pullback.snd f c) (f := f) (g := c)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app L.obj) := by
  apply isIso_of_bounded_cohomology
    (moduleObjectDerivedPushforward Λ f ⋙ moduleObjectDerivedPullback Λ c)
    (moduleObjectDerivedPullback Λ (pullback.fst f c) ⋙
      moduleObjectDerivedPushforward Λ (pullback.snd f c))
    (ambient_qcqs_exchange_canonical_shifts Λ
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).1
    (ambient_qcqs_exchange_canonical_shifts Λ
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).2.1
    (condensedAmbientExchange Λ
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ })
    (ambient_qcqs_exchange_canonical_shifts Λ
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).2.2
    (IsConstantModelConstructible Λ X) (constructible_iso Λ X)
    ?_ L.obj L.property.1.1 L.property.1.2
  intro M hM
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated q
  exact proper_constructible_closed_exchange_heart Λ ℓ hΛ f c M hM

end AlgebraicGeometry.ProEtale.CondensedRing
