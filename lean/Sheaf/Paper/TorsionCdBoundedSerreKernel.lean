/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
import Sheaf.Paper.TorsionCdBoundedSerreCoimage
import Sheaf.Paper.TorsionCdCriticalCoimageSurjectivity
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologySequence
import Sheaf.Paper.FiniteDiscreteSerreHeartCd
import all Sheaf.Paper.CondensedCoefficientIsoConstructible
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-! # The kernel step of the arbitrary-affine torsion-dimension transfer

The former unrestricted filtered finite-heart presentation is false. This module
isolates the cohomological kernel step, without making that presentation claim.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Lifting a finite discrete coefficient carrier preserves its condensed ring object. -/
private theorem finiteCoefficientLiftIso (A : Type) [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] :
    Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj (ULift.{u} A))) := by
  let ei : A ≃+* ULift.{u} A := ULift.ringEquiv.symm
  have hc : Continuous ei := continuous_of_discreteTopology
  have hc' : Continuous ei.symm := continuous_of_discreteTopology
  let er : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} A) :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.toRingHom.compLeftContinuous S.unop hc).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.symm.toRingHom.compLeftContinuous S.unop hc').comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.symm_apply_apply (f.down x)
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.apply_symm_apply (f.down x) }
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
  have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ er.hom
  exact ⟨Mon.mkIso ea⟩


/-- The finite discrete branch of the topological transfer on any affine scheme.
Source: Stacks Tags 03SA(3), 099Y, and exact etale/pro-etale comparison.
(blueprint: lem-sfb-finite-coefficient-serre-cd)
Proof: lift the finite ring into the scheme universe and transport the module along
the induced condensed coefficient isomorphism. Exact scalar restriction transports
the weak Serre coproduct hull. The finite discrete bound applies to the identity
etale test and gives vanishing above d. Sections commute with scalar restriction;
classical right-derived evaluation agrees with the displayed unbounded derived
functor on heart objects. The coefficient ring may be zero and the affine base may
be empty or non-Noetherian. -/
private theorem finiteCoefficient_serreHeart_bound
    (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalRing A] [Finite A]
    (htors : ∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (e : Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))
    (X : Scheme.{u}) [IsAffine X] (d : ℕ)
    (hcd : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [Etale v],
      V.HasTorsionEtaleCohomologicalDimensionLE d)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) M)
    (q : ℤ) (hq : (d : ℤ) + 2 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((condensedModuleSections Λ X).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  classical
  -- A shorter proof uses étale origin directly and gives vanishing already above d.
  let B := ULift.{u} A
  let Λ' := FiniteDiscreteOrdinary.coefficient B
  let j : Mon.mk Λ ≅ Mon.mk Λ' := e ≪≫ (finiteCoefficientLiftIso A).some
  have : IsIso j.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map j.inv))
  let φ := (upperStarFromPoint X).map j.inv.hom
  let E := Mod.comapEquivalenceOfIsIso φ
  have : E.functor.Additive := inferInstanceAs (Mod.comap φ).Additive
  let P := IsConstantModelConstructible Λ' X
  let Q := ObjectProperty.weakSerreCoproductClosure.{u + 1} P
  have hN : Q (E.functor.obj M) := by
    apply hM (Q.inverseImage E.functor) ?_ inferInstance inferInstance inferInstance
      inferInstance (fun _ ↦ inferInstance)
    intro N hN
    exact ObjectProperty.le_weakSerreCoproductClosure P _
      (constructible_comap j.inv.hom X N hN)
  have htorsB : ∃ n : ℕ, ∀ a : B, (ℓ ^ n) • a = 0 := by
    obtain ⟨n, hn⟩ := htors
    exact ⟨n, fun a ↦ ULift.ext _ _ (hn a.down)⟩
  have hq0 : 0 ≤ q := by omega
  lift q to ℕ using hq0
  have hz := FiniteDiscreteOrdinary.finiteDiscrete_serreHeart_cohomology_vanishes B
    ℓ htorsB X d (hcd X (𝟙 X)) (E.functor.obj M) hN q (by omega)
  let eΓ : condensedModuleSections Λ X ≅ E.functor ⋙ condensedModuleSections Λ' X :=
    NatIso.ofComponents (fun N ↦ Iso.refl _) (by intros; rfl)
  have hz' : IsZero (((condensedModuleSections Λ X).rightDerived q).obj M) :=
    hz.of_iso (Functor.rightDerivedObjIsoOfIso eΓ q M ≪≫
      Functor.compRightDerivedObjIso E.functor (condensedModuleSections Λ' X)
        (fun _ _ ↦ Functor.rightAcyclic_of_injective _) q M)
  exact hz'.of_iso
    ((condensedModuleSections Λ X).homologyRightDerivedFunctorObjSingleFunctorIso M q)

/-- The actual kernel of a map between already bounded objects of the constructible
weak Serre hull has the same cohomological bound. Both input bounds are hypotheses;
this does not assert the bound for an arbitrary object of the hull.

Source: blueprint latest, `det-sf-comp-coherence-refinement.proof.md`, paragraph (2),
first paragraph, arbitrary-affine coefficient-transfer obligation; the relation-resolution
step recorded in `lem-sfb-weak-serre-supported-derived-generation`.
Exact full-generality reference WANTED.
(blueprint: lem-sfb-torsion-cd-bounded-serre-kernel)

Proof obligation in words: use the actual relation sheaf of the given map on affine
weakly contractible pro-etale charts, retaining continuous coefficient matrices. Resolve
these relations strictly, including relations between earlier kernel and quotient
objects, and descend through finite open-closed support trees. For finite discrete
coefficients the whole hull is of etale origin and the bound follows from torsion
etale dimension. For integral coefficients the relation-resolution reductions are
controlled by the torsion bound and the countable inverse-limit shift; rational
coefficients are treated by exact scalar localization. The two given input bounds
and the resulting relation comparison must make the kernel bound uniform at d+2.
This is an independent unresolved geometric obligation, not a consequence of the
long exact sequence alone. In particular no filtered finite-heart presentation,
Noetherianity, or completeness of an arbitrary kernel may be assumed. Empty schemes,
zero coefficients, the zero map and isomorphisms are included.
-/
theorem torsionCd_bounded_serre_kernel
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
    (X : Scheme.{u}) [IsAffine X] (d : ℕ)
    (hcd : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [Etale v],
      V.HasTorsionEtaleCohomologicalDimensionLE d)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (f : M ⟶ N)
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) M)
    (hN : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) N)
    (hMb : ∀ q : ℤ, (d : ℤ) + 2 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((condensedModuleSections Λ X).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))))
    (hNb : ∀ q : ℤ, (d : ℤ) + 2 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((condensedModuleSections Λ X).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj N))))
    (q : ℤ) (hq : (d : ℤ) + 2 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((condensedModuleSections Λ X).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj (kernel f)))) := by
  rcases hΛ with hfin | htop
  · obtain ⟨A, _, _, _, _, hA, htors, ⟨e⟩⟩ := hfin
    let : Finite A := hA
    exact finiteCoefficient_serreHeart_bound ℓ A htors Λ e X d hcd (kernel f)
      ((ObjectProperty.weakSerreCoproductClosure.{u + 1}
        (IsConstantModelConstructible Λ X)).prop_kernel f hM hN) q hq
  · let S := ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f)
      (cokernel.condition (kernel.ι f))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_cokernel (kernel.ι f)
        mono_f := by dsimp [S]; infer_instance
        epi_g := by dsimp [S]; infer_instance }
    by_cases hc : q = (d : ℤ) + 3
    · subst q
      have hex := (condensedModuleSections Λ X).rightDerivedHomologySequence_exact₁
        hS ((d : ℤ) + 2) ((d : ℤ) + 3) (by omega)
      have hep := torsionCd_critical_coimage_surjectivity
        ℓ Λ htop X d hcd M N f hM hN hMb hNb
      let := hep
      apply hex.isZero_of_both_zeros
      · change (condensedModuleSections Λ X).rightDerivedHomologyδ
          hS ((d : ℤ) + 2) ((d : ℤ) + 3) (by omega) = 0
        apply (cancel_epi ((DerivedCategory.homologyFunctor _ ((d : ℤ) + 2)).map
          ((condensedModuleSections Λ X).rightDerivedFunctor.map
            ((DerivedCategory.singleFunctor _ 0).map S.g)))).mp
        simp
      · exact (hMb _ hq).eq_zero_of_tgt _
    · exact ((condensedModuleSections Λ X).rightDerivedHomologySequence_exact₁
        hS (q - 1) q (by omega)).isZero_of_both_isZero
        (torsionCd_bounded_serre_coimage ℓ Λ htop X d hcd M N f hM hN hMb hNb
          (q - 1) (by omega)) (hMb q hq)

end AlgebraicGeometry.ProEtale
