/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q31 and S7
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Sheaf.Paper.IntegralModels
import Sheaf.Paper.AdicConstructibilityPredicateComparison
import Sheaf.AlgebraicGeometry.BoundedConstructibleTensorPreservation
import Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.Paper.CondensedConstructibleOpenClosedImages

/-!
# Integral inverse image and uncompleted tensor

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-tensor/_section.md;
Stacks Project, Tags 09BP, 09BM and 09AA (blueprint: sk-lem-int-tensor).

The completed inverse-image comparison uses the existing intrinsic completeness
predicate from IntegralModelsEmbedded, applied to the ordinary inverse image.
The principal Koszul completion criterion identifies this with invertibility of
the canonical quotient completion unit. Uniformizer powers and ell powers are
cofinal. The explicit ell-power cone reductions below remain available as models
of these reductions, with their canonical inclusions and transition squares.
No arbitrary comparison morphism or completion object is selected.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- As in the upstream bounded-constructible module, keep internal Hom constructions opaque.
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- A concrete model of the uncompleted derived reduction of a complex P.
The two-term flat resolution [O_E --ell^(n+1)--> O_E] of O_E/ell^(n+1)
shows that this cone represents P tensor^L O_E/ell^(n+1), without any flatness
assumption on P. Source: Stacks 099M and 099N (blueprint: sk-lem-int-tensor). -/
abbrev integralFiniteComplex (X : Scheme.{u})
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)) ℤ) (n : ℕ) :=
  CochainComplex.mappingCone (ℓ ^ (n + 1) • 𝟙 P)

/-- The canonical finite reduction map, given by the inclusion into the mapping cone.
Source: Stacks 099M and 099N (blueprint: sk-lem-int-tensor). -/
def integralFiniteComplexQuotient (X : Scheme.{u})
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)) ℤ) (n : ℕ) :
    P ⟶ integralFiniteComplex ℓ E X P n :=
  CochainComplex.mappingCone.inr (ℓ ^ (n + 1) • 𝟙 P)

/-- The finite-reduction transition is induced by the square with multiplication
by ell on the source and the identity on the target of the multiplication maps.
Source: Stacks 099M and 099N (blueprint: sk-lem-int-tensor). -/
def integralFiniteComplexTransition (X : Scheme.{u})
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)) ℤ) (n : ℕ) :
    integralFiniteComplex ℓ E X P (n + 1) ⟶ integralFiniteComplex ℓ E X P n :=
  HomologicalComplex.homotopyCofiber.mapArrowHom
    (ℓ ^ (n + 1 + 1) • 𝟙 P) (ℓ ^ (n + 1) • 𝟙 P)
    (fun j : ℤ ↦ ⟨j - 1, by simp⟩)
    { left := ℓ • 𝟙 P
      right := 𝟙 P
      w := by simp [pow_succ, mul_smul] }

/-- The canonical completed inverse-image comparison is invertible when the ordinary
inverse image is derived complete. We use the existing intrinsic completeness predicate
on the equivalent small ringed site, with the actual first residue map. The witness
is a generator of the maximal ideal, not a comparison morphism or a completion object.

This is the same condition as the canonical ell-power cone triangle: exact inverse
image carries the two-term scalar resolutions, their quotient units and transitions
to those on the target. Uniformizer powers and ell powers are cofinal. The principal
Koszul completion criterion identifies intrinsic completeness with invertibility of
that quotient unit; its Roos triangle has the prescribed cone-inclusion product leg.
Exact restriction of scalars preserves products and triangles and detects isomorphisms,
so this is also the completed inverse image after restriction to constant O_E.
Source: Stacks 099M, 099N(5), 0999 and 0A0E; integral models, clause (2)
(blueprint: sk-lem-int-tensor). -/
def IntegralPullbackIsCompleted {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y))) : Prop :=
  ∃ π : PadicAlgCl.integers ℓ E.val,
    Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.val) ∧
      IntegralModelsEmbedded.completedComplete ℓ E π X
        (((upperStar (Profinite.padicIntegersRingObj ℓ E.val) g).leftDerivedFunctor).obj K)

/-- Integral inverse image, its completed comparison, uncompleted tensor, extension by
zero for a quasi-compact open immersion, and closed direct image preserve Dbc.

Source: blueprint main-20261015, sk-lem-int-tensor; Stacks 09BP, 09BM and 09AA
(blueprint: sk-lem-int-tensor).

Proof:
1. The existing exact derived inverse-image preservation theorem gives bounded
constructibility. The coefficient-predicate comparison identifies this with finite
constant-model constructibility. Clause (2) of integral_models then gives intrinsic
derived completeness of the image, for a generator of the maximal ideal. The
canonical completion criterion in IntegralPullbackIsCompleted identifies this with
the completed inverse image, retaining the canonical quotient unit.
2. Apply the existing integral instance of boundedConstructible_tensor_closure,
which proves closure for the ambient uncompleted derived tensor by finite devissage.
3. Apply the exact open-extension preservation theorem.
4. For a closed immersion, condensed open-closed recollement supplies exactness.
The exact derived homology comparisons and constructible closed-image theorem give
bounded constructibility. Identify the exact and right-derived presentations.
-/
theorem integralTensorInverseImage (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of k))] :
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y)),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y) K →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)
          (((upperStar (Profinite.padicIntegersRingObj ℓ E.val) g).leftDerivedFunctor).obj K) ∧
        IntegralPullbackIsCompleted ℓ E g K) ∧
    (∀ K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) K →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) L →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)
        (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).obj K).obj L)) ∧
    (∀ (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of k))]
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X))),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) K →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y)
        (((openImmersionLowerShriek
          (Profinite.padicIntegersRingObj ℓ E.val) j).mapDerivedCategory).obj K)) ∧
    (∀ (i : X ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X))),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) K →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y)
        (((lowerStar (Profinite.padicIntegersRingObj ℓ E.val) i).rightDerivedFunctor).obj K)) := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.val
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : LocallyOfFiniteType (Over.mk (X ↘ Spec (.of k))).hom := by
    change LocallyOfFiniteType (X ↘ Spec (.of k))
    infer_instance
  have : QuasiCompact (Over.mk (X ↘ Spec (.of k))).hom := by
    change QuasiCompact (X ↘ Spec (.of k))
    infer_instance
  have : IsSeparated (Over.mk (X ↘ Spec (.of k))).hom := by
    change IsSeparated (X ↘ Spec (.of k))
    infer_instance
  have : LocallyOfFiniteType (Over.mk (Y ↘ Spec (.of k))).hom := by
    change LocallyOfFiniteType (Y ↘ Spec (.of k))
    infer_instance
  have : QuasiCompact (Over.mk (Y ↘ Spec (.of k))).hom := by
    change QuasiCompact (Y ↘ Spec (.of k))
    infer_instance
  have : IsSeparated (Over.mk (Y ↘ Spec (.of k))).hom := by
    change IsSeparated (Y ↘ Spec (.of k))
    infer_instance
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    have hpull := boundedConstructible_leftDerivedUpperStar_obj Λ ℓ
      (X := Over.mk (X ↘ Spec (.of k))) (Y := Over.mk (Y ↘ Spec (.of k)))
      (Over.homMk g (CategoryTheory.comp_over g (Spec (.of k)))) K hK
    refine ⟨hpull, ?_⟩
    obtain ⟨π, hπ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E.val
    have hπ' : Ideal.span {π} =
        IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.val) := hπ.symm
    refine ⟨π, hπ', ?_⟩
    have heq := (adicConstructibilityPredicateComparison ℓ X Λ
      (IsEllAdicCoefficient.integral E.val)).2
    have hconstant : constantModelBoundedConstructible Λ X
        (((upperStar Λ g).leftDerivedFunctor).obj K) := by
      rw [← heq]
      exact hpull
    exact (((integral_models k (ringChar k) ℓ (Ne.symm (Fact.out : ringChar k ≠ ℓ))
      X E π hπ').2.2.1 _).2.mp hconstant).1
  · intro K L hK hL
    exact boundedConstructible_tensor_closure Λ (Over.mk (X ↘ Spec (.of k))) K L hK hL
  · intro j _ _ _ K hK
    have : IsOpenImmersion (Over.homMk j (CategoryTheory.comp_over j
        (Spec (.of k))) : Over.mk (X ↘ Spec (.of k)) ⟶
          Over.mk (Y ↘ Spec (.of k))).left := by
      change IsOpenImmersion j
      infer_instance
    exact boundedConstructible_openImmersionLowerShriek_obj Λ ℓ
      (U := Over.mk (X ↘ Spec (.of k))) (X := Over.mk (Y ↘ Spec (.of k)))
      (Over.homMk j (CategoryTheory.comp_over j (Spec (.of k)))) K hK
  · intro i _ _ K hK
    have : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
      (Y ↘ Spec (.of k))
    have : IsNoetherian Y := ⟨⟩
    let U : Y.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    obtain ⟨hex, _⟩ := condensed_open_closed_recollement Λ i U.ι U.range_ι
    let := hex
    let e := (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.app K
    refine ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e.symm
      ((lowerStar Λ i).bounded_mapDerivedCategory_obj hK.1), fun n ↦ ?_⟩
    exact _root_.constructible_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e.symm)
      (_root_.constructible_of_iso
        (((lowerStar Λ i).mapDerivedCategoryHomologyFunctorIso n).app K)
        ((constructible_open_closed_images Λ U.ι i U.range_ι).2 _ (hK.2 n)))

end AlgebraicGeometry.ProEtale.CondensedRing
