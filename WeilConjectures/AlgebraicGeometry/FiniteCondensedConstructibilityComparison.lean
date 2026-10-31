/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation

/-! # Constructibility in the two finite condensed coefficient models -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
open CondensedRing

variable (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

private theorem inverseConstant_finitelyPresented (X : Scheme.{u})
    (M : ModuleCat.{u + 1} (ULift.{u + 1} T)) [Finite M] :
    Mod.IsFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj T) X)
      ((finiteCoefficientModEquivalence X T).inverse.obj
        ((constantSheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj M)) := by
  classical
  let A := ULift.{u + 1} T
  let R := condensedRingObj (Profinite.continuousMapRingObj T) X
  let C := constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⋙
    (finiteCoefficientModEquivalence X T).inverse
  have : PreservesBinaryBiproducts C :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts C
  have : C.Additive := C.additive_of_preservesBinaryBiproducts
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  obtain ⟨n, m, g, f, hg, hfg⟩ := Module.FinitePresentation.exists_fin' A M
  let f' := ModuleCat.ofHom f
  let g' := ModuleCat.ofHom g
  let e : M ≅ cokernel f' :=
    (ModuleCat.isColimitCokernelCofork f' g' hfg hg).coconePointUniqueUpToIso
      (colimit.isColimit (parallelPair f' 0))
  let b (q : ℕ) : C.obj (ModuleCat.of A (Fin q → A)) ≅ Mod.finiteFree R q :=
    C.mapIso (ModuleCat.biproductIsoPi (fun _ : Fin q ↦ ModuleCat.of A A)).symm ≪≫
      C.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ (regularIsoInverseConstant T X).symm)
  let fR := (b m).inv ≫ C.map f' ≫ (b n).hom
  exact ⟨n, m, fR, ⟨C.mapIso e ≪≫ PreservesCokernel.iso C f' ≪≫
    cokernel.mapIso _ _ (b m) (b n) (by simp [fR])⟩⟩

private theorem locallyFinitelyPresented_of_finiteLocallyConstant {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))
    (hM : IsFiniteLocallyConstant (ULift.{u + 1} T)
      ((finiteCoefficientModEquivalence X T).functor.obj M)) :
    IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj T) X) M := by
  classical
  obtain ⟨ι, W, g, hg, h⟩ := hM
  let C₀ : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage X :=
    { I₀ := ι, X := W, f := g, mem₀ := hg }
  have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
    inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
  let C := C₀.restrictIndexOfSmall.{u}
  refine ⟨C, fun i ↦ ?_⟩
  let j := (show C.I₀ → C₀.I₀ from
    Precoverage.ZeroHypercover.Small.restrictFun C₀) i
  obtain ⟨N, hN, ⟨e⟩⟩ := h j
  have : Finite N := hN
  let F := finiteCoefficientModEquivalence (C.X i) T
  have ep : F.functor.obj
      ((CondensedRing.upperStar (Profinite.continuousMapRingObj T) (C.f i)).obj M) ≅
      (constantSheaf (Scheme.ProEt.topology (C.X i))
        (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj N :=
    (upperStarFiniteCoefficientModEquivalenceIso (C.f i) T).app M ≪≫ e
  apply (isFinitelyPresented_mapMod_iff (Profinite.continuousMapRingObj T) (C.f i) M).2
  exact (inverseConstant_finitelyPresented T (C.X i) N).of_iso
    (F.inverse.mapIso ep.symm ≪≫ (F.unitIso.app _).symm)

private theorem constructible_of_finiteCoefficientModEquivalence {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))
    (hM : IsConstructible (ULift.{u + 1} T)
      ((finiteCoefficientModEquivalence X T).functor.obj M)) :
    IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj T) X) M := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  apply (isLocallyFinitelyPresented_mapMod_iff
    (Profinite.continuousMapRingObj T) (S.immersion a) M).2
  exact locallyFinitelyPresented_of_finiteLocallyConstant T _
    (isFiniteLocallyConstant_of_iso
      ((upperStarFiniteCoefficientModEquivalenceIso (S.immersion a) T).app M).symm (hS a))

/-- The finite condensed coefficient equivalence preserves and reflects bounded
constructibility on every scheme, with the same global finite stratifications.
Source: Bhatt--Scholze, pro-etale topology, Section 6.8; the finite-coefficient comparison.
(blueprint: lem-fd-finite-condensed-constructibility-comparison).

Proof: the forward direction is the existing finite-coefficient etale-origin theorem.
For the converse, a pro-etale complex of etale origin has bounded cohomology and
intrinsically constructible cohomology sheaves. On every stratum, trivialize each such
sheaf by finite constant modules. A finite module over a finite ring is finitely
presented; apply the exact constant-sheaf functor and the inverse coefficient equivalence
to its finite free presentation. The regular-module comparison identifies the resulting
presentation with a finite free presentation over the pulled-back condensed ring.
Restrict the covering index to the scheme universe. The pullback comparisons transport
these presentations to the internal module sheaf, giving constructibility on the same
strata. Exactness and faithfulness of the equivalence preserve and reflect the finite
cohomological interval. -/
theorem boundedConstructible_finiteCoefficientDerivedEquivalence_iff
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [DiscreteTopology T] [Finite T] (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
        ((finiteCoefficientDerivedEquivalence X T).functor.obj K) := by
  constructor
  · exact isEtaleOrigin_of_isConstructible T
  · intro h
    have hi := DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic _ h
    refine ⟨(finiteCoefficientModEquivalence X T).functor
      |>.bounded_of_bounded_mapDerivedCategory_obj hi.1, fun n ↦ ?_⟩
    exact constructible_of_finiteCoefficientModEquivalence T _
      (isConstructible_of_iso
        (((finiteCoefficientModEquivalence X T).functor.mapDerivedCategoryHomologyFunctorIso
          n).app K).symm (hi.2 n))

end AlgebraicGeometry.ProEtale
