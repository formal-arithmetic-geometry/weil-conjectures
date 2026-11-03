/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.FiniteRingTrace.FiniteTraceMapFromExternalDuality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointUnitSections

/-! # The Verdier trace class, arbitrary finite coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/
sk-d-pairing/def-trf-trace-class.md (blueprint: def-trf-trace-class).

The coefficient ring `A` is an arbitrary finite commutative ring killed by a positive power of
`ell`, with its discrete topology, as in the cited `def-trf-coefficient-conventions`,
`def-trf-trace-class-source` and `lem-trf-trace-map-from-external-duality` (the node's
`A = A_{E,n}` is the special case). The trace class is the specified composite
`Tr_c(u) = 𝔱_{c,K} ∘ û`:
* `ũ : A_C → H_c(K)` is the specified mate `traceClassMate` of def-trf-trace-class-source;
* `û : A → RΓ(C, H_c(K))` is its image under the global-sections map
  `f ↦ RΓ(C, f) ∘ η_C`, where `η_C : A → RΓ(C, A_C)` is `Fib_s` of the unit of
  `La_C^* ⊣ Ra_{C*}` at `A_s` followed by the unit comparison `La_C^* A_s ≅ A_C`;
* `𝔱_{c,K}` is the trace map `traceMapFromExternalDuality` of
  lem-trf-trace-map-from-external-duality.
The coefficient object `A ∈ D(A)` is `Fib_s(A_s)`, the image of the constant coefficient
sheaf under geometric-point evaluation (def-weil-finite-coefficient-point).
The element of `Hom_{D(F,A)}(A_F, ω_{F,A})` is the unique preimage of the composite under the
same global-sections map on `F`, which is bijective (lem-pur-rhom-global-sections, unit case).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.FiniteRingTrace

attribute [local instance] vdDiscreteTopology tmDiscrete tmTopologicalRing tmCharPrime
  tmSeparated tmFiniteType tmQuasiCompact tmBaseFiniteType tmBaseQuasiCompact
  tmBaseSeparated

variable (A : Type) [CommRing A] [Finite A]
  (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
  (X : Over (Spec (.of D.k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- Geometric-point evaluation `Fib_s : D(s, A) → D(A)`, the right derived functor of the
coefficient sections over `s = Spec k`.
Source: "`R\Gamma` is ordinary derived global sections as in
[def-weil-ordinary-compact-cohomology]" (blueprint: def-trf-trace-class). -/
abbrev tcPointSections :
    Ambient A (Spec (.of D.k)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (MonObj.Γ (coefficient A))) :=
  (condensedRingCoefficientSections (coefficient A) (Spec (.of D.k))).rightDerivedFunctor

/-- The coefficient object `A ∈ D(A)`, as `Fib_s(A_s)`: geometric-point evaluation of the
constant coefficient sheaf `A_s` (the tensor unit of `D(s, A)`).
Source: the source `A` of "`Tr_c(u) : A → RΓ(C, H_c(K)) → RΓ(F, ω_{F,A})`";
def-weil-finite-coefficient-point (blueprint: def-trf-trace-class). -/
def tcCoefficientUnit : DerivedCategory (ModuleCat.{u + 1} (MonObj.Γ (coefficient A))) :=
  (tcPointSections A D).obj (𝟙_ (Ambient A (Spec (.of D.k))))

/-- The unit section `η_T : A_s → Ra_{T*} A_T`: the unit of `La_T^* ⊣ Ra_{T*}` at `A_s`,
followed by `Ra_{T*}` of the unit comparison `La_T^* A_s ≅ A_T` of the derived pullback.
Source: "the global-sections adjunction", unit-object case
(blueprint: def-trf-trace-class). -/
def tcUnitSectionSheaf (T : Over (Spec (.of D.k))) :
    𝟙_ (Ambient A (Spec (.of D.k))) ⟶
      (lowerStar (coefficient A) T.hom).rightDerivedFunctor.obj (𝟙_ (Ambient A T.left)) :=
  (derivedUpperStarLowerStarAdjunction (coefficient A) T.hom).unit.app
      (𝟙_ (Ambient A (Spec (.of D.k)))) ≫
    (lowerStar (coefficient A) T.hom).rightDerivedFunctor.map
      (leftDerivedUpperStarUnitIso (coefficient A) T.hom).hom

/-- The unit section `η_T = Fib_s(η_T) : A → RΓ(T, A_T)`.
Source: "the global-sections adjunction", unit-object case
(blueprint: def-trf-trace-class). -/
def tcSectionsUnit (T : Over (Spec (.of D.k))) :
    tcCoefficientUnit A D ⟶ (tmSections A D T).obj (𝟙_ (Ambient A T.left)) :=
  (tcPointSections A D).map (tcUnitSectionSheaf A D T)

/-- The global-sections map `Hom_{D(T,A)}(A_T, M) → Hom_{D(A)}(A, RΓ(T, M))`,
`f ↦ RΓ(T, f) ∘ η_T`.
Source: "the global-sections adjunction
`Hom_{D(C,A)}(A_C, H_c(K)) ≅ Hom_{D(A)}(A, RΓ(C, H_c(K)))`"
(blueprint: def-trf-trace-class). -/
def tcGlobalSectionsMap (T : Over (Spec (.of D.k))) (M : Ambient A T.left)
    (f : 𝟙_ (Ambient A T.left) ⟶ M) : tcCoefficientUnit A D ⟶ (tmSections A D T).obj M :=
  tcSectionsUnit A D T ≫ (tmSections A D T).map f

/-- The global-sections map is bijective: the unit-object case of
lem-pur-rhom-global-sections, using `RHom_A(A_T, M) ≃ M`.
Source: "The global-sections identifications are the unit-object case of
[lem-pur-rhom-global-sections], using `R\mathcal Hom_A(A_T,M) ≃ M` for `T = C, F`"
(blueprint: def-trf-trace-class).
Proof: by the adjunction `La_T^* ⊣ Ra_{T*}` and the unit comparison `La_T^* A_s ≅ A_T`,
`f ↦ Ra_{T*}f ∘ η_T` is the bijection `Hom(A_T, M) ≅ Hom(A_s, Ra_{T*} M)`
(`Adjunction.homEquiv` composed with precomposition by an isomorphism). It remains that
`Fib_s` induces a bijection `Hom_{D(s,A)}(A_s, N) → Hom_{D(A)}(Fib_s A_s, Fib_s N)`: the
coefficient sections over the algebraically closed point are exact and represented by the
regular module `A_s` (`coyonedaSections`), so `Fib_s` is computed termwise and
`Hom_{D(s,A)}(A_s, N) = H^0(Γ(s, N)) = Hom_{D(A)}(A, Fib_s N)`, which is
lem-pur-rhom-global-sections with `L = A_s`, `RHom(A_s, N) ≃ N`. -/
theorem tcGlobalSectionsMap_bijective (T : Over (Spec (.of D.k))) (M : Ambient A T.left) :
    Function.Bijective (tcGlobalSectionsMap A D T M) := by
  let U := 𝟙_ (Ambient A (Spec (.of D.k)))
  let R := (lowerStar (coefficient A) T.hom).rightDerivedFunctor
  let i := leftDerivedUpperStarUnitIso (coefficient A) T.hom
  let adj := derivedUpperStarLowerStarAdjunction (coefficient A) T.hom
  let e : (𝟙_ (Ambient A T.left) ⟶ M) ≃ (U ⟶ R.obj M) :=
    (i.symm.homCongr (Iso.refl M)).trans (adj.homEquiv U M)
  have h : Function.Bijective (fun g : U ⟶ R.obj M ↦
      ((tcPointSections A D).map g :
        tcCoefficientUnit A D ⟶ (tmSections A D T).obj M)) :=
    finite_point_unit_sections_map_bijective (coefficient A) D.k (R.obj M)
  have heq : tcGlobalSectionsMap A D T M =
      (fun g : U ⟶ R.obj M ↦ (tcPointSections A D).map g) ∘ e := by
    funext f
    change tcGlobalSectionsMap A D T M f =
      (tcPointSections A D).map
        ((adj.homEquiv U M) ((i.symm.homCongr (Iso.refl M)) f))
    rw [Iso.homCongr_apply, Adjunction.homEquiv_unit]
    simp only [tcGlobalSectionsMap, tcSectionsUnit, tcUnitSectionSheaf, tmSections,
      tcPointSections, Functor.comp_map, Iso.symm_inv, Iso.refl_hom,
      Category.comp_id, Functor.map_comp, Category.assoc, i, adj, U]
  rw [heq]
  exact h.comp e.bijective

/-- The global-sections identification `Hom_{D(T,A)}(A_T, M) ≃ Hom_{D(A)}(A, RΓ(T, M))`, the
specified map `tcGlobalSectionsMap` packaged with its bijectivity; its inverse is the unique
preimage, so no choice is made.
Source: "identified with an element of `Hom_{D(F,A)}(A_F, ω_{F,A})` by the global-sections
adjunction" (blueprint: def-trf-trace-class). -/
def tcGlobalSectionsEquiv (T : Over (Spec (.of D.k))) (M : Ambient A T.left) :
    (𝟙_ (Ambient A T.left) ⟶ M) ≃ (tcCoefficientUnit A D ⟶ (tmSections A D T).obj M) :=
  Equiv.ofBijective (tcGlobalSectionsMap A D T M) (tcGlobalSectionsMap_bijective A D T M)

section Correspondence

variable {A D ell hell hA X}

end Correspondence

end WeilConjectures.FiniteRingTrace
