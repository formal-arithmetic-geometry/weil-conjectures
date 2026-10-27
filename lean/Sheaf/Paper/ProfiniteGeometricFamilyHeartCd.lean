/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Paper.AffineProfiniteFamilySerreCd
import Sheaf.AlgebraicGeometry.ZeroDimensionalBaseAffineGlobal
import Sheaf.Paper.FiniteConstantStratifiedZariskiLocality
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Absolute cohomological dimension of a profinite geometric family

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph
(blueprint: lem-sfb-profinite-geometric-family-heart-cd).

This is the agent-formulated absolute input in the node, with the nonsharp bound `2e + 2`.
The full norm-topological coefficient statement remains a source obligation; the module
states it without claiming it follows from a torsion or completed-coefficient theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem restrict_generator {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsAffineOpen U)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ U.toScheme ((upperStar Λ U.ι).obj M) := by
  let : IsAffine U.toScheme := hU
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at hM ⊢
  exact (finiteConstantStratified_zariski_locality Λ X M).2.2
    inferInstance inferInstance |>.mp hM U hU

private theorem restrict_heart {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsAffineOpen U)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) M) :
    ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ U.toScheme) ((upperStar Λ U.ι).obj M) := by
  let F := upperStar Λ U.ι
  let P := ObjectProperty.weakSerreCoproductClosure.{u + 1}
    (IsConstantModelConstructible Λ U.toScheme)
  let Q := P.inverseImage F
  have : PreservesColimitsOfSize.{u + 1, u + 1} F :=
    (upperStarLowerStarAdjunction Λ U.ι).leftAdjoint_preservesColimits
  exact hM Q (fun N hN ↦ ObjectProperty.le_weakSerreCoproductClosure _ _
    (restrict_generator Λ U hU N hN)) inferInstance inferInstance inferInstance
    inferInstance (fun _ ↦ inferInstance)

private theorem fibre_dimension_open {C X : Scheme.{u}} (h : X ⟶ C)
    (e : ℕ) (he : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (c : Spec (CommRingCat.of K) ⟶ C),
      topologicalKrullDim (pullback h c : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (U : X.Opens) (K : Type u) [Field K] [IsAlgClosed K]
    (c : Spec (CommRingCat.of K) ⟶ C) :
    topologicalKrullDim (pullback (U.ι ≫ h) c : Scheme.{u}) ≤ (e : WithBot ℕ∞) := by
  let i := pullbackRightPullbackFstIso h c U.ι
  have hi := (Scheme.Hom.isOpenEmbedding i.inv).isEmbedding.isInducing
  have hj := (Scheme.Hom.isOpenEmbedding
    (pullback.snd U.ι (pullback.fst h c))).isEmbedding.isInducing
  exact hi.topologicalKrullDim_le.trans (hj.topologicalKrullDim_le.trans (he K c))

private noncomputable def open_underlying {X : Scheme.{u}} (U : X.Opens) :
    upperStar Λ U.ι ⋙ Mod.forget (condensedRingObj Λ U.toScheme) ≅
      Mod.forget (condensedRingObj Λ X) ⋙
        ProEtale.upperStar Ab.{u + 1} U.ι :=
  Functor.isoWhiskerLeft
    ((ProEtale.upperStar Ab.{u + 1} U.ι).mapMod (condensedRingObj Λ X))
    (Functor.isoWhiskerRight (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ U.ι))
      (Mod.forget (condensedRingObj Λ U.toScheme)))

private noncomputable def open_sections {X : Scheme.{u}} (U : X.Opens) :
    upperStar Λ U.ι ⋙ condensedModuleSections Λ U.toScheme ≅
      Mod.forget (condensedRingObj Λ X) ⋙
        sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
          (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (Opposite.op (Scheme.ProEt.mk U.ι)) := by
  let ev := sheafToPresheaf (Scheme.ProEt.topology U.toScheme) Ab.{u + 1} ⋙
    (evaluation U.toScheme.ProEtᵒᵖ Ab.{u + 1}).obj
      (Opposite.op (Scheme.ProEt.mk (𝟙 U.toScheme)))
  refine Functor.isoWhiskerRight (open_underlying Λ U) ev ≪≫
    Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ X))
      (Functor.isoWhiskerRight
        (ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} U.ι) ev) ≪≫ ?_
  let w : Scheme.ProEt.mk ((𝟙 U.toScheme) ≫ U.ι) ≅ Scheme.ProEt.mk U.ι :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by simp)
  exact NatIso.ofComponents (fun M ↦ M.X.obj.mapIso w.symm.op) (by
    intro M N f
    exact (f.hom.hom.naturality _).symm)

private noncomputable def open_derived_sections {X : Scheme.{u}} (U : X.Opens)
    (q : ℕ) :
    (upperStar Λ U.ι ⋙ (condensedModuleSections Λ U.toScheme).rightDerived q) ≅
      (Mod.forget (condensedRingObj Λ X) ⋙
        sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
          (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj
            (Opposite.op (Scheme.ProEt.mk U.ι))).rightDerived q := by
  have : (upperStar Λ U.ι).PreservesInjectiveObjects :=
    (openImmersionLowerShriekUpperStarAdjunction Λ U.ι)
      |>.preservesInjectiveObjects_of_preservesFiniteLimits
  let e := open_sections Λ U
  let d : (upperStar Λ U.ι ⋙ condensedModuleSections Λ U.toScheme).rightDerived q ≅
      (Mod.forget (condensedRingObj Λ X) ⋙
        sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
          (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj
            (Opposite.op (Scheme.ProEt.mk U.ι))).rightDerived q :=
    { hom := NatTrans.rightDerived e.hom q
      inv := NatTrans.rightDerived e.inv q
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id,
        NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id,
        NatTrans.rightDerived_id] }
  exact (Functor.rightDerivedCompIsoOfExact (upperStar Λ U.ι)
    (condensedModuleSections Λ U.toScheme) q).symm ≪≫ d

/-- Ordinary module-object cohomology of a proper family over an affine reduced,
zero-dimensional w-contractible base with separably closed residue fields vanishes above
`2e + 2` on the entire constructibly generated weak Serre coproduct heart.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph; agent-formulated
absolute estimate, exact reference for the full coefficient generality wanted
(blueprint: lem-sfb-profinite-geometric-family-heart-cd).

Proof plan, the four steps of the DAG node:
1. For an affine open V of Z, the composite V -> C is locally of finite type by properness
of h and openness of V. Since V and C are affine it is quasi-compact, hence finite type.
Each geometric fibre V_c is open in Z_c. Closure of irreducible chains in the ambient
space shows its dimension is at most e, including empty fibres.
2. Open module pullback is additive exact by det-prop-sfb-module-pullback-exact-main.
It preserves coproducts by the module pullback/direct-image adjunction and
lem-weil-pbc-left-adjoint-preserves-colimits. Restricting strata and their scalar-model
covers preserves the very same finitely presented scalar modules. Thus the inverse-image
class has every defining closure property of the weak Serre coproduct intersection,
and minimality sends N in P_Z to its restriction in P_V. This argument does not assert
that a cohomology vanishing class is closed under kernels.
3. Apply lem-sfb-affine-profinite-family-serre-cd to V -> C, the same e, coefficients,
and restricted N, to obtain affine-open cohomology vanishing in degrees q > e + 2.
No finite-subextension or completion replacement is made.
4. Apply lem-sfb-zero-dimensional-base-affine-global with base C, scheme Z, coefficient
ring Lambda_Z, module N, and a = e + 2. Properness supplies separatedness and finite type;
the ringed open comparison identifies the restriction with the pullback in Step 2.
The conclusion is vanishing for r > e + (e + 2) = 2e + 2. Both inputs include the empty
base, source and opens, and the bound is independent of N and of the affine open.
-/
theorem profinite_geometric_family_serreHeart_cohomology_vanishes
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    {C Z : Scheme.{u}} [IsAffine C] [IsReduced C]
    [IsWContractibleRing Γ(C, ⊤)]
    (hCdim : ∀ p : PrimeSpectrum Γ(C, ⊤), p.asIdeal.IsMaximal)
    (hCres : ∀ c : C, IsSepClosed (C.residueField c))
    (h : Z ⟶ C) [IsProper h] (e : ℕ)
    (he : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (c : Spec (CommRingCat.of K) ⟶ C),
      topologicalKrullDim (pullback h c : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (hN : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ Z) N)
    (r : ℤ) (hr : 2 * (e : ℤ) + 2 < r) :
    IsZero ((DerivedCategory.homologyFunctor _ r).obj
      ((condensedModuleSections Λ Z).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj N))) := by
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace h
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated h
  have hr0 : 0 ≤ r := by omega
  lift r to ℕ using hr0
  refine IsZero.of_iso ?_
    ((condensedModuleSections Λ Z).homologyRightDerivedFunctorObjSingleFunctorIso N r)
  apply proEtale_cohomology_vanishes_of_affine_of_zeroDimensional_base
    hCdim h e (e + 2) he (condensedRingObj Λ Z) N ?_ r (by omega)
  intro U hU q hq
  let : IsAffine U.toScheme := hU
  have hrestrict := restrict_heart Λ U hU N hN
  have hvan := affine_profinite_family_serreHeart_cohomology_vanishes ℓ Λ hΛ
    hCdim hCres (U.ι ≫ h) e (fibre_dimension_open h e he U)
    ((upperStar Λ U.ι).obj N) hrestrict q (by exact_mod_cast hq)
  let d := (condensedModuleSections Λ U.toScheme)
    |>.homologyRightDerivedFunctorObjSingleFunctorIso ((upperStar Λ U.ι).obj N) q
  exact (hvan.of_iso d.symm).of_iso ((open_derived_sections Λ U q).app N).symm

end AlgebraicGeometry.ProEtale.CondensedRing
