/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.NormAlgclCoefficientMap
import Sheaf.Paper.NormAlgclGeometricComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Derived global sections and the norm topology on algebraic-closure coefficients

Source: blueprint main-20261015, `sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), the agent coefficient-topology obligation
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison).

The inclusion of the finite-subextension-valued sheaf into all continuous functions
is constructed sectionwise. After restriction to the finite coefficient field, its
image in the derived category is tensored with V. This is the actual map represented
on a flat-term K-flat resolution by z tensor v mapping to c(z) tensor v.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NormAlgclComparison

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
private theorem representationModel_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (W : Type (u + 1)) [NormedAddCommGroup W] [NormedSpace E W]
    (rho : G →* Module.End E W)
    (M N : Profinite.AlgclInvariantsComparison.RepresentationModel ℓ E G W rho) :
    Nonempty (M.object ≅ N.object) := by
  let A := Profinite.AlgclInvariantsComparison.scalarRing.{u} ℓ E
  let F := InternalAbelianSheafModule.sectionModuleFunctor
    (coherentTopology Profinite.{u}) A.X
  let ff := InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful
    (coherentTopology Profinite.{u}) A.X
  let e (S : Profinite.{u}) :
      Profinite.CondensedAction.sectionModule A.toMon M.object.module S ≃ₗ[
        CategoryTheory.CondensedBar.sectionRing A S]
      Profinite.CondensedAction.sectionModule A.toMon N.object.module S :=
    { toAddEquiv := (M.sections S).trans (N.sections S).symm
      map_smul' := by
        intro r m
        apply (N.sections S).injective
        change (N.sections S) ((N.sections S).symm ((M.sections S) (r • m))) =
          (N.sections S) (r • (N.sections S).symm ((M.sections S) m))
        ext t
        simp only [AddEquiv.apply_symm_apply, M.scalar, N.scalar] }
  have e_apply (S : Profinite.{u}) (m) :
      e S m = (N.sections S).symm ((M.sections S) m) := rfl
  have e_symm_apply (S : Profinite.{u}) (m) :
      (e S).symm m = (M.sections S).symm ((N.sections S) m) := rfl
  let ep : (F.obj M.object.module).val ≅ (F.obj N.object.module).val :=
    PresheafOfModules.isoMk (fun S ↦ (e S.unop).toModuleIso) (by
      intro S T f
      ext m
      change M.object.module.X.obj.obj S at m
      change (e T.unop) (M.object.module.X.obj.map f m) =
        N.object.module.X.obj.map f ((e S.unop) m)
      rw [e_apply, e_apply]
      apply (N.sections T.unop).injective
      rw [AddEquiv.apply_symm_apply]
      have hm := M.restriction S.unop T.unop f.unop m
      have hn := N.restriction S.unop T.unop f.unop
        ((N.sections S.unop).symm ((M.sections S.unop) m))
      simp only [Quiver.Hom.op_unop] at hm hn
      rw [hm, hn, AddEquiv.apply_symm_apply])
  let es : F.obj M.object.module ≅ F.obj N.object.module :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso ep
  let em : M.object.module ≅ N.object.module := ff.preimageIso es
  have he (S : Profinite.{u}) (m : M.object.module.X.obj.obj (Opposite.op S)) :
      (em.hom.hom.hom.app (Opposite.op S)) m = e S m := by
    have h := ff.map_preimage es.hom
    exact congrArg (fun f ↦ f.val.app (Opposite.op S) m) h
  have he' (S : Profinite.{u}) (m : N.object.module.X.obj.obj (Opposite.op S)) :
      (em.inv.hom.hom.app (Opposite.op S)) m = (e S).symm m := by
    have h := ff.map_preimage es.inv
    exact congrArg (fun f ↦ f.val.app (Opposite.op S) m) h
  refine ⟨{ hom := ⟨em.hom, ?_⟩
            inv := ⟨em.inv, ?_⟩
            hom_inv_id := by apply Subtype.ext; exact em.hom_inv_id
            inv_hom_id := by apply Subtype.ext; exact em.inv_hom_id }⟩
  · intro S g m
    rw [he, he, e_apply, e_apply]
    apply (N.sections S).injective
    ext t
    simp only [AddEquiv.apply_symm_apply, M.action, N.action]
  · intro S g m
    rw [he', he', e_symm_apply, e_symm_apply]
    apply (M.sections S).injective
    ext t
    simp only [AddEquiv.apply_symm_apply, M.action, N.action]

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (X : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The actual coefficient inclusion becomes invertible after ordinary derived global
sections, for every bounded constructible finite-field input with finite constant models.
Source: paragraph (3), agent coefficient-topology obligation; exact literature proof WANTED
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison).

Proof:
1. Choose a separable closure. The separate geometric normalization theorem
   (lem-sfb-norm-algcl-geometric-comparison-normalization), using the normalized geometric
   finite scalar model and Galois descent, supplies a bounded equivariant complex with
   finite-dimensional continuous E-representation cohomology and the actual coefficient square.
2. Apply lem-sfb-profinite-algcl-derived-invariants-comparison to each cohomology
   representation. Exactness and shift compatibility give the comparison on its shifts.
3. Use the standard derived t-structure and lem-sf-triangle-two-out-of-three along the
   finite truncation tower of the bounded geometric model. Begin with zero below the
   cohomological support; induction gives invertibility on the whole model. This requires
   neither a finite cohomological dimension nor an infinite Postnikov convergence claim.
4. The geometric normalization square intertwines every cohomology map of R Gamma(m_V)
   with the corresponding cohomology map of the invertible arithmetic comparison from step 3.
   Cancel the endpoint isomorphisms. Cohomology detects isomorphisms in the original unbounded
   derived category, so this proves the statement without identifying localization universes.
No sheaf-level isomorphism, flatness of c_X, or completeness of the algebraic closure is used. -/
theorem isIso_derivedGlobalSections_comparison
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (a : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hV : constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X V) :
    IsIso ((derivedGlobalSections ℓ X E).map (comparison ℓ X E V)) := by
  apply (DerivedCategory.isIso_iff Ab.{u + 1} _).2
  let := (constantSheafΓAdj (Scheme.ProEt.topology X) Ab.{u + 1}).isRightAdjoint
  let : (Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1}).Additive :=
    Functor.additive_of_preserves_binary_products _
  let ks := SeparableClosure k
  let G := ks ≃ₐ[k] ks
  obtain ⟨hA, hGroth, hcomp⟩ :=
    Profinite.AlgclInvariantsComparison.profinite_algcl_derived_invariants_comparison ℓ E G
  let := hA
  let := hGroth
  let := HasDerivedCategory.standard
    (CategoryTheory.CondensedBar.Equivariant
      (Profinite.AlgclInvariantsComparison.scalarRing.{u} ℓ E) G)
  let := HasDerivedCategory.standard Ab.{u + 1}
  obtain ⟨I, hAdd, TC, TB, c, eta, LC, LB, hc, heta, hlim, hcolim,
    hLC, hLB, hshift, hheart⟩ := hcomp
  let := hAdd
  let := hlim
  let := hcolim
  let := hLC
  let := hLB
  let alpha := Functor.whiskerRight
    (Profinite.AlgclInvariantsComparison.derivedCoefficientMap ℓ E G LC LB eta)
    (I.functor ⋙ Profinite.AlgclInvariantsComparison.pointEvaluation ℓ E).rightDerivedFunctor
  let : NatTrans.CommShift alpha ℤ := hshift
  have hnorm := geometric_comparison_normalization ℓ X E ks p hpℓ a
    I TC TB c eta LC LB hc heta V hV
  obtain ⟨K, hK, hmodels, eC, eB, hsquare⟩ := hnorm
  have hcohom (q : ℤ) :
      IsIso (alpha.app ((DerivedCategory.singleFunctor _ 0).obj
        ((DerivedCategory.homologyFunctor _ q).obj K))) := by
    obtain ⟨W, ng, ns, fd, rho, hcontinuous, hmodel⟩ := hmodels q
    let := ng
    let := ns
    let := fd
    obtain ⟨N, hN⟩ := hheart W rho hcontinuous
    obtain ⟨M, ⟨e⟩⟩ := hmodel
    obtain ⟨e'⟩ := representationModel_iso ℓ E G W rho M N
    exact (NatTrans.isIso_app_iff_of_iso alpha
      ((DerivedCategory.singleFunctor _ 0).mapIso (e ≪≫ e'))).2 hN
  let P : ObjectProperty (CategoryTheory.CondensedBar.Equivariant
      (Profinite.AlgclInvariantsComparison.scalarRing.{u} ℓ E) G) :=
    fun M ↦ IsIso (alpha.app ((DerivedCategory.singleFunctor _ 0).obj M))
  let : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦
    (NatTrans.isIso_app_iff_of_iso alpha
      ((DerivedCategory.singleFunctor _ 0).mapIso e)).1 h⟩
  have hα : IsIso (alpha.app K) :=
    DerivedCategory.prop_of_bounded alpha.isoLocus P (fun _ h ↦ h) K hK hcohom
  intro q
  have h := hsquare q
  have hi : IsIso ((eC q).hom ≫
      (DerivedCategory.homologyFunctor Ab.{u + 1} q).map (alpha.app K)) := by
    infer_instance
  rw [← h] at hi
  exact IsIso.of_isIso_comp_right _ (eB q).hom

end AlgebraicGeometry.ProEtale.NormAlgclComparison
