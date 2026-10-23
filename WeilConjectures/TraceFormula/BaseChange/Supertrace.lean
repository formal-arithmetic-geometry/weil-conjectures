/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CategoricalTrace
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.TraceFormula.Main

/-!

# The trace on `Dᵇc(Spec Ω)⟦ℚ̲̄_ℓ⟧` as a supertrace

For a separably closed field `Ω`, the categorical trace of an endomorphism `v` of a dualizable
object `P` of `Dᵇc(Spec Ω)⟦ℚ̲̄_ℓ⟧`, with the Koszul braiding, is the alternating sum of the
categorical traces of the induced endomorphisms `Hʲ(v)` of the homology sheaves `Hʲ(P)`
(blueprint `prop-trf-trace-formal-laws`, item (4)). The two traces live in different rings: the
supertrace in `End (𝟙_ Mod_{Spec Ω})`, the trace in `End (𝟙_ Dᵇc(Spec Ω)⟦ℚ̲̄_ℓ⟧)`; they are
compared through the ring homomorphism `homologyUnitEndRingHom` placing an endomorphism of the
unit module in degree `0`.

## Main definitions

- `ProEtale.CondensedRing.homologyUnitEndRingHom`: `End (𝟙_ Mod_X) →+* End (𝟙_ Dᵇc(X)⟦Λ⟧)`.

## Sorried input

- `ProEtale.CondensedRing.trace_eq_homologyUnitEndRingHom_superTrace` (blueprint
  `prop-trf-trace-formal-laws`, item (4), subsection `sk-p-trace`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] [IsEllAdicFinitenessCoefficient ℓ Λ] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The endomorphisms of the unit module `Λ_X` act on the unit of `Dᵇc(X)⟦Λ⟧`: an endomorphism
of `Λ_X` is placed in degree `0`. -/
noncomputable def homologyUnitEndRingHom :
    End (𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) →+* End (𝟙_ (Dᵇc(X.left)⟦Λ⟧)) :=
  let F := HomologicalComplex.single
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj Λ X.left))
      (ComplexShape.up ℤ) 0 ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh
  have hι : Function.Bijective ((ObjectProperty.ι _).mapEndRingHom (𝟙_ (Dᵇc(X.left)⟦Λ⟧))) :=
    (ObjectProperty.fullyFaithfulι _).map_bijective _ _
  have : IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := CategoryTheory.Mod (Sheaf
      (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left)))) :=
    inferInstanceAs (IsIso (𝟙 _))
  ((RingEquiv.ofBijective _ hι).symm.toRingHom.comp
    ((asIso (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := CategoryTheory.Mod (Sheaf
        (Scheme.ProEt.topology X.left) Ab.{u + 1})
          (condensedRingObj Λ X.left))))).symm.conjRingEquiv.toRingHom.comp
      (F.mapEndRingHom (CategoryTheory.Mod.regular (condensedRingObj Λ X.left)))))

attribute [local instance] boundedConstructibleBraiding in
/-- **The trace as a supertrace over a field** (blueprint `prop-trf-trace-formal-laws`,
item (4)): for a separably closed field `Ω` and an endomorphism `v` of a dualizable object `P` of
`Dᵇc(Spec Ω)⟦ℚ̲̄_ℓ⟧`, the categorical trace of `v` is the alternating sum
`∑ⱼ (-1)ʲ Tr(Hʲ(v) | Hʲ(P))` of the traces on the homology sheaves, placed in degree `0`. -/
theorem trace_eq_homologyUnitEndRingHom_superTrace (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    [Fact (ringChar Ω).Prime] [Fact (ringChar Ω ≠ ℓ)]
    (P : Dᵇc((point Ω).left)⟦Profinite.padicAlgClRingObj ℓ⟧) [HasRightDual P] (v : P ⟶ P) :
    trace v = homologyUnitEndRingHom (Profinite.padicAlgClRingObj ℓ) ℓ (point Ω)
      (superTrace
        (fun j ↦ ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ j).obj P)
        (fun j ↦ ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ j).map v)) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
