module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.GroupTheory.PGroup

import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Sheaf.RepresentationTheory.SylowModuleFiltration
import Mathlib.FieldTheory.Galois.Profinite
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.FieldTheory.OpenSubgroupFixedField
import Sheaf.AlgebraicGeometry.Curve.PrimaryModuleFiltrationSheafTransport

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits ZeroObject
namespace AlgebraicGeometry.IsConnectedCurve
/-- Core filtration and generic cover; annihilator supplied separately.
Proof: identify the finite primary stalk with its discrete Galois module,
apply the Sylow filtration after a coprime open-subgroup restriction, and
transport the resulting chain through the finite normalization model. The
fixed field supplies the displayed finite etale generic map and its degree.
(blueprint: lem-sc-generic-primary-coarse-filtration-core) -/
theorem exists_generic_primary_coarse_filtration_core
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C] [IsIntegral C]
    (hmodel : ∀ (L : Type u) [Field L] [Algebra C.functionField L]
      [FiniteDimensional C.functionField L],
      IsFinite (C.fromNormalizationIn L) ∧ IsAffine (C.normalizationIn L) ∧
        IsConnectedCurve (C.fromNormalizationIn L ≫ f) ∧
        Smooth (C.fromNormalizationIn L ≫ f) ∧
        ∃ e : Spec (.of L) ≅ Spec (C.normalizationIn L).functionField,
          e.hom ≫ (C.normalizationIn L).fromSpecFunctionField =
            (C.fromSpecOfAlgebraFunctionField L).toNormalization)
    (M : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hfinite : Finite (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))
    (hprimary : IsPGroup ℓ (Multiplicative (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))) :
    ∃ (D : Scheme.{u}) (π : D ⟶ C), IsFinite π ∧
      IsConnectedCurve (π ≫ f) ∧ Smooth (π ≫ f) ∧ IsAffine D ∧
      ∃ hIntegral : IsIntegral D,
      letI : IsIntegral D := hIntegral;
      ∃ (n : ℕ) (F : ℕ → Sheaf (Spec D.functionField).smallEtaleTopology
          AddCommGrpCat.{u + 1}),
        IsZero (F 0) ∧
        (∀ (a : ℕ), a < n →
          ∃ (S : ShortComplex (Sheaf (Spec D.functionField).smallEtaleTopology
              AddCommGrpCat.{u + 1})) (d : ℕ),
            S.ShortExact ∧ Nonempty (S.X₁ ≅ F a) ∧
              Nonempty (S.X₂ ≅ F (a + 1)) ∧
              Nonempty (S.X₃ ≅ Nat.rec (0 : _)
                (fun _ A ↦ A ⊞ (Spec D.functionField).constantZMod ℓ) d)) ∧
        ∃ (q : Spec D.functionField ⟶ Spec C.functionField),
          q ≫ C.fromSpecFunctionField = D.fromSpecFunctionField ≫ π ∧
          Etale q ∧
          ∃ (d : ℕ), q.IsFiniteLocallyFreeOfDegree d ∧ d.Coprime ℓ ∧
          Nonempty ((Etale.upperStar AddCommGrpCat.{u + 1} q).obj M ≅ F n) := by
  classical
  let K : Type u := C.functionField
  let Ω := AlgebraicClosure K
  let Ks := separableClosure K Ω
  obtain ⟨E, Eset, i, j, _, haction, _⟩ :=
    Scheme.abelianSheaves_equiv_discreteGModules.{u, u + 1} K Ks Ω
  let R := E.functor.obj M
  let iM : AddCommGrpCat.of R.obj.V ≅
      ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom
        (algebraMap K Ω)))).sheafFiber (A := AddCommGrpCat.{u + 1})).obj M := i.app M
  let : Finite R.obj.V := Finite.of_equiv _ iM.addCommGroupIsoToAddEquiv.toEquiv.symm
  have hR : IsPGroup ℓ (Multiplicative R.obj.V) :=
    hprimary.of_injective iM.hom.hom.toMultiplicative
      iM.addCommGroupIsoToAddEquiv.injective
  obtain ⟨H, hindex, n, A, hmono, hzero, htop, hstable, hstep⟩ :=
    Rep.exists_openSubgroup_primary_module_filtration (Gal(Ks/K)) ℓ hℓ R hR
  obtain ⟨hfd, hsep, hfix, _, _, _⟩ :=
    (openSubgroup_fixedField_finite_separable.{u, u, u} K Ks).1 H.toSubgroup H.isOpen
  let L := IntermediateField.fixedField H.toSubgroup
  let : FiniteDimensional K L := hfd
  let : Algebra.IsSeparable K L := hsep
  obtain ⟨hfin, haff, hcurve, hsmooth, e, he⟩ := hmodel L
  let D := C.normalizationIn L
  let π := C.fromNormalizationIn L
  let : IsIntegral D := inferInstance
  let q : Spec D.functionField ⟶ Spec C.functionField :=
    e.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap K L))
  obtain ⟨F, hFzero, hFstep, hFtop⟩ :=
    Scheme.exists_sheaf_filtration_of_invariant_primary_chain K Ks Ω M R iM
      (haction M) ℓ hℓ H n A hmono hzero htop hstable hstep
      (Spec D.functionField) e
  have hq : q ≫ C.fromSpecFunctionField = D.fromSpecFunctionField ≫ π := by
    change e.inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
      C.fromSpecFunctionField) = D.fromSpecFunctionField ≫ π
    change e.inv ≫ C.fromSpecOfAlgebraFunctionField L = D.fromSpecFunctionField ≫ π
    calc
      e.inv ≫ C.fromSpecOfAlgebraFunctionField L =
          e.inv ≫ ((C.fromSpecOfAlgebraFunctionField L).toNormalization ≫ π) :=
        congrArg (fun g ↦ e.inv ≫ g)
          (Scheme.Hom.toNormalization_fromNormalization
            (C.fromSpecOfAlgebraFunctionField L)).symm
      _ = e.inv ≫ (e.hom ≫ D.fromSpecFunctionField) ≫ π := by rw [he]
      _ = D.fromSpecFunctionField ≫ π := by simp
  have hrEtale : Etale (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    exact RingHom.etale_algebraMap.mpr .of_finite_of_isSeparable
  let := hrEtale
  have hrFinite : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
    apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr inferInstance
  let := hrFinite
  have hqEtale : Etale q := by dsimp [q]; infer_instance
  have hdegree : q.IsFiniteLocallyFreeOfDegree (Module.finrank K L) := by
    refine { toIsFiniteLocallyFree := ?_, fiberDegree_eq := ?_ }
    · exact { toIsFinite := by dsimp only [q]; infer_instance,
              toFlat := by dsimp only [q]; infer_instance,
              toLocallyOfFinitePresentation := by dsimp only [q]; infer_instance }
    · intro x
      change (e.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap K L))).fiberDegree x = _
      rw [Scheme.Hom.fiberDegree_comp_left_of_isIso, fiberDegree_eq_finrankΓ]
      exact Scheme.Hom.finrankΓ_SpecMap K L
  have hcoprime : (Module.finrank K L).Coprime ℓ := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, hfix]
    exact hindex
  exact ⟨D, π, hfin, hcurve, hsmooth, haff, inferInstance, n, F, hFzero, hFstep,
    q, hq, hqEtale, Module.finrank K L, hdegree, hcoprime, hFtop⟩

end AlgebraicGeometry.IsConnectedCurve
