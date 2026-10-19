/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

import Sheaf.AlgebraicGeometry.EllAdicFiniteIndHeartWeakSerre
import Sheaf.CategoryTheory.IndCoproductClosure
import Sheaf.AlgebraicGeometry.LocallyFreeConstantModelComparison
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Sheaf.Paper.IndHeartKernelsCokernels
import Sheaf.Paper.IndConstructibleExtensions
import Sheaf.Paper.ConstructibleCokernelsExtensions
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-! # Closure properties of the ind-constructible adic heart

Source: blueprint `sk-prop-ind-heart` and `det-prop-int-compactness-compact` (1)-(2).
The filtered colimits are taken in the ordinary category of internal module sheaves.
(blueprint: new-lem-sfb-adic-ind-heart-closure)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

private theorem finite_coproducts_of_extensions
    {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderExtensions] : P.IsClosedUnderFiniteCoproducts := by
  have : P.IsClosedUnderBinaryCoproducts := by
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro _ ⟨F, hF⟩
    let e : F ≅ pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩) :=
      Discrete.natIso (fun j ↦ by cases j with | mk j => cases j <;> exact Iso.refl _)
    exact P.prop_of_iso ((biprod.isoCoprod _ _).trans
      (HasColimit.isoOfNatIso e).symm)
      (P.prop_biprod (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩))
  exact ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

include ℓ k hΛ

/-- The ind-constructible heart is a weak Serre class closed under ambient coproducts.

Source: blueprint `sk-prop-ind-heart`, `det-ambient-ind-derived-sums` (1), and
`det-prop-int-compactness-compact` (1)-(2).
(blueprint: new-lem-sfb-adic-ind-heart-closure)

Proof: work on the Noetherian scheme X and distinguish the three coefficient families.
For a finite coefficient field, finite local presentations are lisse finite-dimensional
models after a pro-etale cover. Over the algebraic closure each finite presentation
and finite diagram descends to one finite coefficient extension. For integral
coefficients use the local torsion charts and finite locally free resolutions. In
all three cases constructibles form an abelian extension-closed category and their
realization from formal ind-objects is exact and fully faithful. Indeed finite
presentations descend morphisms and any finite equality to a common filtered stage;
exactness is checked on the common local charts, where filtered colimits of modules
are exact. Thus kernels and cokernels of morphisms of ind-constructibles are the
realizations of the corresponding formal ind-kernels and ind-cokernels. The same
finite-stage argument for extensions, using local presentations and their relations,
shows that the essential image is extension closed. Zero is constructible and its
constant filtered presentation puts it in the image. Finally any coproduct of
filtered presentations is the filtered colimit of their finite partial sums: use
finite subsets of the index set, together with one presentation index for each
member. Finite sums of constructibles are constructible, so these are ambient
ind-constructibles as required. Empty families give zero, and on the empty scheme
all the objects are zero. No derived-completion operation occurs in this argument.
-/
theorem ellAdic_indConstructible_heart_closure :
    let P := ObjectProperty.ind.{u + 1}
      (IsConstructibleModuleObject (condensedRingObj Λ X.left))
    P.ContainsZero ∧ P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels ∧
      P.IsClosedUnderExtensions ∧
      ∀ I : Type (u + 1), P.IsClosedUnderColimitsOfShape (Discrete I) := by
  let C : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
    (condensedRingObj Λ X.left)) := IsConstructibleModuleObject (condensedRingObj Λ X.left)
  let P := C.ind.{u + 1}
  have : C.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ AlgebraicGeometry.ProEtale.constructible_of_iso _ e h⟩
  have : C.ContainsZero := ⟨0, isZero_zero _,
    AlgebraicGeometry.ProEtale.constructible_of_isZero _ (isZero_zero _)⟩
  have : P.ContainsZero := ⟨0, isZero_zero _, ObjectProperty.le_ind _ _ C.prop_zero⟩
  have : C.IsClosedUnderExtensions :=
    (constructible_cokernels_extensions X.left (condensedRingObj Λ X.left)).2
  have : C.IsClosedUnderFiniteCoproducts := finite_coproducts_of_extensions C
  have hsum (I : Type (u + 1)) : P.IsClosedUnderColimitsOfShape (Discrete I) :=
    C.ind_isClosedUnderCoproducts I
  suffices h : P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels ∧
      P.IsClosedUnderExtensions from
    ⟨inferInstance, h.1, h.2.1, h.2.2, hsum⟩
  cases hΛ with
  | continuous E => exact (ellAdic_finite_indConstructible_weakSerre ℓ X).1 E
  | integral E => exact (ellAdic_finite_indConstructible_weakSerre ℓ X).2 E
  | algebraicClosure =>
    have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
    have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType X.hom)
    have : QuasiCompact (X.left ↘ Spec (.of k)) :=
      inferInstanceAs (QuasiCompact X.hom)
    have : IsSeparated (X.left ↘ Spec (.of k)) :=
      inferInstanceAs (IsSeparated X.hom)
    have : IsNoetherian X.left := {}
    have heq := constructible_eq_constantModels_of_lfp_locally_free
      (Profinite.padicAlgClRingObj ℓ) (algcl_lf ℓ) X.left
    change C.ind.IsClosedUnderKernels ∧ C.ind.IsClosedUnderCokernels ∧
      C.ind.IsClosedUnderExtensions
    dsimp only [C]
    rw [heq]
    let Q := ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X.left)
    have hKC := (indHeart_kernelsCokernels ℓ (ringChar k) k
      (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) X.left).2
    refine ⟨⟨?_⟩, ⟨?_⟩, ⟨fun hS hA hB ↦
      indConstructible_of_shortExact_padicAlgCl ℓ X.left _ hS hA hB⟩⟩
    · rintro _ ⟨f, fork, hfork, hA, hB⟩
      obtain ⟨_, _, _, _, _, _, _, hk, _⟩ := hKC _ _ f hA hB
      exact Q.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hfork) hk
    · rintro _ ⟨f, cofork, hcofork, hA, hB⟩
      obtain ⟨_, _, _, _, _, _, _, _, hc⟩ := hKC _ _ f hA hB
      exact Q.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hcofork) hc

end AlgebraicGeometry.ProEtale.CondensedRing
