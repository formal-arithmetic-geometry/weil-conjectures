/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantProjectionMap
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal
import WeilConjectures.AlgebraicGeometry.FlatCohomologyDerivedTensor
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
import WeilConjectures.AlgebraicGeometry.KummerLine.KummerRootLineComputation
import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Kummer computations with arbitrary finite ring coefficients

Source: blueprint thm-pur-kummer-affine-line, with the arbitrary-ring correction
of expert message 1385, answers 5–6 (2026-11-01).

The coefficient sheaf and insertions are the published Kummer module coefficient
functor. Multiplication on the coefficient ring gives its canonical ring action
on cohomology. Scalar extension uses `ModuleCat.extendScalars`, so no algebra
structure or flatness assumption is imposed on an arbitrary ring homomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.KummerLine

private lemma insertion_map (X : Scheme.{u}) (m : ℕ)
    (A B : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) (f : A ⟶ B) (a : A) :
    Scheme.kummerCoefficientInsertion X m A a ≫ (Scheme.kummerAbelianTwist X m).map f =
      Scheme.kummerCoefficientInsertion X m B (f a) := by
  apply Sheaf.hom_ext
  ext U y
  let η := X.kummerRootModulePresheaf m ◁ (Functor.const X.Etaleᵒᵖ).map f
  have h := congrArg (fun g ↦ g.app U) (toSheafify_naturality X.smallEtaleTopology η)
  exact (congrArg (fun g ↦ g (y ⊗ₜ[ULift.{u + 1} (ZMod m)] a)) h).symm

private lemma insertion_add (X : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) (a c : A) :
    Scheme.kummerCoefficientInsertion X m A (a + c) =
      Scheme.kummerCoefficientInsertion X m A a +
        Scheme.kummerCoefficientInsertion X m A c := by
  apply Sheaf.hom_ext
  ext U y
  change ((toSheafify X.smallEtaleTopology
    (X.kummerRootModulePresheaf m ⊗ (Functor.const X.Etaleᵒᵖ).obj A)).app U).hom (y ⊗ₜ (a + c)) =
    ((toSheafify X.smallEtaleTopology
    (X.kummerRootModulePresheaf m ⊗ (Functor.const X.Etaleᵒᵖ).obj A)).app U).hom (y ⊗ₜ a) +
      ((toSheafify X.smallEtaleTopology
    (X.kummerRootModulePresheaf m ⊗ (Functor.const X.Etaleᵒᵖ).obj A)).app U).hom (y ⊗ₜ c)
  rw [TensorProduct.tmul_add, map_add]

private def insertionLinear (k : Type u) [Field k] (b : Bool)
    (m : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) (q : ℕ)
    (x : Sheaf.H ((curve k b).rootsOfUnitySheaf m) q) :
    A →ₗ[A] ringCoefficientCohomology k b m A hA q where
  toFun a := Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) m
    (ringCoefficientModule m A hA) a) q x
  map_add' a c := by
    rw [insertion_add, Sheaf.H.map_add_apply]
  map_smul' a c := by
    rw [coefficient_smul]
    change Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) m
        (ringCoefficientModule m A hA) (a * c)) q x =
      Sheaf.H.map ((Scheme.kummerAbelianTwist (curve k b) m).map
        ((ModuleCat.restrictScalars (ringCoefficientScalar m A hA)).map
          (ModuleCat.ofHom (LinearMap.lsmul A (ModuleCat.of A A) a)))) q
        (Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) m
          (ringCoefficientModule m A hA) c) q x)
    let f := (ModuleCat.restrictScalars (ringCoefficientScalar m A hA)).map
      (ModuleCat.ofHom (LinearMap.lsmul A (ModuleCat.of A A) a))
    exact (congrArg (fun g ↦ Sheaf.H.map g q x)
      (insertion_map (curve k b) m (ringCoefficientModule m A hA)
        (ringCoefficientModule m A hA) f c)).symm.trans
      (Sheaf.H.map_comp_apply _ _ x)

private lemma line_curve (k : Type u) [Field k] (b : Bool) :
    IsCurve (structureMap k b) := by
  have hdim : topologicalKrullDim (curve k false) ≤ 1 := by
    change topologicalKrullDim (PrimeSpectrum (Polynomial k)) ≤ 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    rfl
  have hopen : IsOpenImmersion (inclusion k) :=
    IsOpenImmersion.of_isLocalization (S := LaurentPolynomial k) Polynomial.X
  have hcomp : inclusion k ≫ structureMap k false = structureMap k true := by
    rw [inclusion, structureMap, structureMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro x
    exact Polynomial.toLaurent_C x
  have hfinite : LocallyOfFiniteType (structureMap k false) := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom Polynomial.C))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have hsep (b : Bool) : IsSeparated (structureMap k b) := by
    cases b <;> dsimp [structureMap, curve] <;> infer_instance
  have hqc (b : Bool) : QuasiCompact (structureMap k b) := by
    cases b <;> dsimp [structureMap, curve] <;> infer_instance
  have hfalse : IsCurve (structureMap k false) := { krullDim_le_one := hdim }
  cases b
  · exact hfalse
  · have : LocallyOfFiniteType (structureMap k true) := by
      rw [← hcomp]
      infer_instance
    exact { krullDim_le_one :=
      (inclusion k).isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hdim }

private lemma line_cd (k : Type u) [Field k] [IsAlgClosed k] (b : Bool)
    [CompactSpace (curve k b)] [QuasiSeparatedSpace (curve k b)] :
    (curve k b).torsionEtaleCohomologicalDimension < ⊤ := by
  have : IsCurve (structureMap k b) := line_curve k b
  have : IsAffine (curve k b) := by cases b <;> dsimp [curve] <;> infer_instance
  apply lt_of_le_of_lt (sInf_le (a := (1 : ℕ∞)) ?_) (by simp)
  refine ⟨1, rfl, ?_⟩
  intro F hF q hq
  obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso (curve k b) q
  have := IsCurve.subsingleton_sheafH_of_two_le_of_isAffine
    (structureMap k b) F hF q hq
  let e' : Sheaf.H F q ≃+
      (DerivedCategory.singleFunctor (Sheaf (curve k b).smallEtaleTopology
        AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} (curve k b) q).obj F :=
    (e.app F).addCommGroupIsoToAddEquiv
  exact e'.symm.injective.subsingleton

private def basisFunctorIso (k : Type u) [Field k] (b : Bool) (m q : ℕ)
    (e : ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
      Sheaf.H ((curve k b).rootsOfUnitySheaf m) q)
    (α : tensorLeft (ModuleCat.of (ULift.{u + 1} (ZMod m))
        (Sheaf.H ((curve k b).rootsOfUnitySheaf m) q)) ⋙
        forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1} ≅
      Scheme.kummerAbelianTwist (curve k b) m ⋙
        Sheaf.functorH (curve k b).smallEtaleTopology q) :
    Scheme.kummerAbelianTwist (curve k b) m ⋙
        Sheaf.functorH (curve k b).smallEtaleTopology q ≅
      forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1} :=
  α.symm ≪≫ Functor.isoWhiskerRight
    ((curriedTensor _).mapIso e.symm.toModuleIso ≪≫ leftUnitorNatIso _ ) _

private lemma basis_insertion_bijective (k : Type u) [Field k] (b : Bool) (m : ℕ)
    [(forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1}).Full]
    [IsIso (Scheme.kummerCoefficientInsertion (curve k b) m
      (ModuleCat.of (ULift.{u + 1} (ZMod m)) (ULift.{u + 1} (ZMod m))) 1)]
    (q : ℕ)
    (e : ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
      Sheaf.H ((curve k b).rootsOfUnitySheaf m) q)
    (E : Scheme.kummerAbelianTwist (curve k b) m ⋙
        Sheaf.functorH (curve k b).smallEtaleTopology q ≅
      forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1})
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (m : A) = 0) :
    Function.Bijective (insertionLinear k b m A hA q (e 1)) := by
  let R := ULift.{u + 1} (ZMod m)
  let M := ringCoefficientModule m A hA
  let F := Scheme.kummerAbelianTwist (curve k b) m ⋙
    Sheaf.functorH (curve k b).smallEtaleTopology q
  have : F.Full := Functor.Full.of_iso E.symm
  let i := Scheme.kummerCoefficientInsertion (curve k b) m (ModuleCat.of R R) 1
  let I := (Sheaf.functorH (curve k b).smallEtaleTopology q).mapIso (asIso i)
  have hs : Function.Surjective (insertionLinear k b m A hA q (e 1)) := by
    intro y
    let a : M := (E.hom.app M).hom y
    let g : (Sheaf.functorH _ q).obj ((curve k b).rootsOfUnitySheaf m) ⟶ F.obj M :=
      AddCommGrpCat.ofHom
        ((LinearMap.toSpanSingleton R M a).toAddMonoidHom.comp e.symm.toAddMonoidHom) ≫
        E.inv.app M
    let f : ModuleCat.of R R ⟶ M := F.preimage (I.inv ≫ g)
    refine ⟨f 1, ?_⟩
    have hf : (Sheaf.functorH _ q).map i ≫ F.map f = g := by
      rw [F.map_preimage]
      exact I.hom_inv_id_assoc g
    have hval := ConcreteCategory.congr_hom hf (e 1)
    change (F.map f).hom (Sheaf.H.map i q (e 1)) = g.hom (e 1) at hval
    have hg : g.hom (e 1) = y := by
      change (E.inv.app M).hom ((LinearMap.toSpanSingleton R M a)
        (e.symm (e 1))) = y
      rw [e.symm_apply_apply, LinearMap.toSpanSingleton_apply_one]
      exact ConcreteCategory.congr_hom (E.hom_inv_id_app M) y
    change Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) m M (f 1))
      q (e 1) = y
    rw [← insertion_map (curve k b) m (ModuleCat.of R R) M f 1,
      Sheaf.H.map_comp_apply]
    exact hval.trans hg
  let equiv : ringCoefficientCohomology k b m A hA q ≃ A :=
    (E.app M).addCommGroupIsoToAddEquiv.toEquiv
  let : Finite (ringCoefficientCohomology k b m A hA q) := Finite.of_equiv A equiv.symm
  exact hs.bijective_of_nat_card_le (Nat.card_congr equiv).symm.le

private lemma derived_coefficient_vanishing (k : Type u) [Field k] (b : Bool) (m q : ℕ)
    (α : tensorLeft (ModuleCat.of (ULift.{u + 1} (ZMod m))
        (Sheaf.H ((curve k b).rootsOfUnitySheaf m) q)) ⋙
        forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1} ≅
      Scheme.kummerAbelianTwist (curve k b) m ⋙
        Sheaf.functorH (curve k b).smallEtaleTopology q)
    [Subsingleton (Sheaf.H ((curve k b).rootsOfUnitySheaf m) q)]
    (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) :
    Subsingleton (ringCoefficientCohomology k b m A hA q) := by
  let e : (Sheaf.H ((curve k b).rootsOfUnitySheaf m) q ⊗[ULift.{u + 1} (ZMod m)]
      ringCoefficientModule m A hA) ≃+ ringCoefficientCohomology k b m A hA q :=
    (α.app (ringCoefficientModule m A hA)).addCommGroupIsoToAddEquiv
  exact e.symm.injective.subsingleton

private def extensionBasis {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{u + 1} R) (e : R ≃ₗ[R] M) :
    (ModuleCat.extendScalars f).obj M ≃ₗ[S] S := by
  letI := f.toAlgebra
  let e' : M ≅ ModuleCat.of R R := e.symm.toModuleIso
  let a : (ModuleCat.extendScalars f).obj M ≃ₗ[S]
      (ModuleCat.extendScalars f).obj (ModuleCat.of R R) :=
    ((ModuleCat.extendScalars f).mapIso e').toLinearEquiv
  let b : (ModuleCat.extendScalars f).obj (ModuleCat.of R R) ≃ₗ[S] S :=
    TensorProduct.AlgebraTensorModule.rid R S S
  exact a.trans b

private lemma extensionBasis_tmul {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{u + 1} R) (e : R ≃ₗ[R] M) (s : S) (x : M) :
    extensionBasis f M e (s ⊗ₜ[R, f] x) = f (e.symm x) * s := by
  let := f.toAlgebra
  change (TensorProduct.AlgebraTensorModule.rid R S S)
    (s ⊗ₜ[R] e.symm x) = _
  rw [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
  rfl

private lemma residue_map_smul (m : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (m : A) = 0) {M P : Type (u + 1)} [AddCommGroup M] [AddCommGroup P]
    [Module (ULift.{u + 1} (ZMod m)) M] [Module A P]
    (f : M →+ P) (r : ULift.{u + 1} (ZMod m)) (x : M) :
    f (r • x) = ringCoefficientScalar m A hA r • f x := by
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective r.down
  have hr : r = (n : ULift.{u + 1} (ZMod m)) := by
    apply ULift.ext
    exact hn.symm
  rw [hr, map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]

private lemma insertion_basis_formula (k : Type u) [Field k] (b : Bool) (m : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) (q : ℕ)
    (e : ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
      Sheaf.H ((curve k b).rootsOfUnitySheaf m) q)
    (a : A) (x : Sheaf.H ((curve k b).rootsOfUnitySheaf m) q) :
    Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) m
      (ringCoefficientModule m A hA) a) q x =
        insertionLinear k b m A hA q (e 1)
          (ringCoefficientScalar m A hA (e.symm x) * a) := by
  have hx : x = e.symm x • e 1 := by rw [← e.map_smul]; simp
  conv_lhs => rw [hx]
  erw [residue_map_smul m A hA
    (P := ringCoefficientCohomology k b m A hA q)]
  exact ((insertionLinear k b m A hA q (e 1)).map_smul
    (ringCoefficientScalar m A hA (e.symm x)) a).symm

private lemma tensor_comparison_of_basis (k : Type u) [Field k] (b : Bool) (m : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) (q : ℕ)
    (e : ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
      Sheaf.H ((curve k b).rootsOfUnitySheaf m) q)
    (he : Function.Bijective (insertionLinear k b m A hA q (e 1))) :
    ∃ E : ringCoefficientTensor k b m A hA q ≃ₗ[A]
        ringCoefficientCohomology k b m A hA q,
      ∀ (x : Sheaf.H ((curve k b).rootsOfUnitySheaf m) q) (a : A),
        E (a ⊗ₜ[ULift.{u + 1} (ZMod m), ringCoefficientScalar m A hA] x) =
        Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) m
          (ringCoefficientModule m A hA) a) q x := by
  let E := LinearEquiv.ofBijective (insertionLinear k b m A hA q (e 1)) he
  refine ⟨(extensionBasis (ringCoefficientScalar m A hA) _ e).trans E, ?_⟩
  intro x a
  erw [LinearEquiv.trans_apply, extensionBasis_tmul]
  exact (insertion_basis_formula k b m A hA q e a x).symm

private lemma scalar_natural (m : ℕ) (A B : Type (u + 1)) [CommRing A] [CommRing B]
    (hA : (m : A) = 0) (hB : (m : B) = 0) (φ : A →+* B)
    (r : ULift.{u + 1} (ZMod m)) :
    φ (ringCoefficientScalar m A hA r) = ringCoefficientScalar m B hB r := by
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective r.down
  have hr : r = (n : ULift.{u + 1} (ZMod m)) := by
    apply ULift.ext
    exact hn.symm
  rw [hr, map_intCast, map_intCast, map_intCast]

set_option maxHeartbeats 800000 in
-- The coefficient-extension equality unfolds the sheafified tensor action.
private lemma scalar_extension_of_basis (k : Type u) [Field k] (b : Bool) (m : ℕ)
    (A B : Type (u + 1)) [CommRing A] [CommRing B]
    (hA : (m : A) = 0) (hB : (m : B) = 0) (φ : A →+* B) (q : ℕ)
    (e : ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
      Sheaf.H ((curve k b).rootsOfUnitySheaf m) q)
    (heA : Function.Bijective (insertionLinear k b m A hA q (e 1)))
    (heB : Function.Bijective (insertionLinear k b m B hB q (e 1))) :
    ∃ E : (ModuleCat.extendScalars φ).obj (ringCoefficientCohomology k b m A hA q)
        ≃ₗ[B] ringCoefficientCohomology k b m B hB q,
      ∀ (x : Sheaf.H ((curve k b).rootsOfUnitySheaf m) q) (a : A) (c : B),
        E (c ⊗ₜ[A, φ]
        (Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) m
          (ringCoefficientModule m A hA) a) q x)) =
        Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) m
          (ringCoefficientModule m B hB) (φ a * c)) q x := by
  let EA : A ≃ₗ[A] ringCoefficientCohomology k b m A hA q :=
    LinearEquiv.ofBijective (insertionLinear k b m A hA q (e 1)) heA
  let EB : B ≃ₗ[B] ringCoefficientCohomology k b m B hB q :=
    LinearEquiv.ofBijective (insertionLinear k b m B hB q (e 1)) heB
  let E := (extensionBasis φ (ringCoefficientCohomology k b m A hA q) EA).trans EB
  refine ⟨E, ?_⟩
  intro x a c
  have hA' : Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) m
      (ringCoefficientModule m A hA) a) q x =
      EA (ringCoefficientScalar m A hA (e.symm x) * a) :=
    insertion_basis_formula k b m A hA q e a x
  have hB' : Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) m
      (ringCoefficientModule m B hB) (φ a * c)) q x =
      EB (ringCoefficientScalar m B hB (e.symm x) * (φ a * c)) :=
    insertion_basis_formula k b m B hB q e (φ a * c) x
  have hE (y : ringCoefficientCohomology k b m A hA q) :
      E (c ⊗ₜ[A, φ] y) = EB (φ (EA.symm y) * c) := by
    exact congrArg EB (extensionBasis_tmul φ _ EA c y)
  rw [hE, hA', EA.symm_apply_apply, hB']
  apply congrArg EB
  rw [φ.map_mul, scalar_natural, mul_assoc]

set_option maxHeartbeats 800000 in
-- The uniqueness proof compares two transported insertion maps through tensor actions.
private lemma restriction_of_basis (k : Type u) [Field k] (m : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0)
    (e₀ : (b : Bool) → ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
      Sheaf.H ((curve k b).rootsOfUnitySheaf m) 0)
    (hr : ∀ r, rootRestriction k m 0 (e₀ false r) = e₀ true r)
    (he : ∀ b, Function.Bijective (insertionLinear k b m A hA 0 (e₀ b 1))) :
    ∃! res : ringCoefficientCohomology k false m A hA 0 →ₗ[A]
        ringCoefficientCohomology k true m A hA 0,
      (∀ (x : Sheaf.H ((curve k false).rootsOfUnitySheaf m) 0) (a : A),
        res (Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k false) m
        (ringCoefficientModule m A hA) a) 0 x) =
          Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k true) m
            (ringCoefficientModule m A hA) a) 0 (rootRestriction k m 0 x)) ∧
      (∀ a : A, res (Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k false) m
        (ringCoefficientModule m A hA) a) 0 (e₀ false 1)) =
          Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k true) m
            (ringCoefficientModule m A hA) a) 0 (e₀ true 1)) := by
  let EA (b : Bool) : A ≃ₗ[A] ringCoefficientCohomology k b m A hA 0 :=
    LinearEquiv.ofBijective (insertionLinear k b m A hA 0 (e₀ b 1)) (he b)
  let res : ringCoefficientCohomology k false m A hA 0 →ₗ[A]
      ringCoefficientCohomology k true m A hA 0 :=
    ((EA false).symm.trans (EA true)).toLinearMap
  have hres (a : A) : res (EA false a) = EA true a := by
    change EA true ((EA false).symm (EA false a)) = _
    rw [LinearEquiv.symm_apply_apply]
  have hres' (a : A) :
      res (Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k false) m
        (ringCoefficientModule m A hA) a) 0 (e₀ false 1)) =
      Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k true) m
        (ringCoefficientModule m A hA) a) 0 (e₀ true 1) := hres a
  refine ⟨res, ⟨?_, hres'⟩, ?_⟩
  · intro x a
    obtain ⟨r, rfl⟩ := (e₀ false).surjective x
    have hf := insertion_basis_formula k false m A hA 0 (e₀ false) a (e₀ false r)
    have ht := insertion_basis_formula k true m A hA 0 (e₀ true) a (e₀ true r)
    have hs (b : Bool) : (e₀ b).symm (e₀ b r) = r := (e₀ b).symm_apply_apply r
    rw [hs] at hf ht
    change _ = EA false _ at hf
    change _ = EA true _ at ht
    calc
      res _ = res (EA false (ringCoefficientScalar m A hA r * a)) := congrArg res hf
      _ = EA true (ringCoefficientScalar m A hA r * a) := hres _
      _ = Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k true) m
          (ringCoefficientModule m A hA) a) 0 (e₀ true r) := ht.symm
      _ = _ := congrArg (fun x ↦ Sheaf.H.map
          (Scheme.kummerCoefficientInsertion (curve k true) m
            (ringCoefficientModule m A hA) a) 0 x) (hr r).symm
  · intro g hg
    apply LinearMap.ext
    intro y
    obtain ⟨a, ha⟩ := (EA false).surjective y
    subst y
    exact (hg.2 a).trans (hres a).symm

private lemma extension_subsingleton {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{u + 1} R) [Subsingleton M] :
    Subsingleton ((ModuleCat.extendScalars f).obj M) := by
  have hz : ∀ x : (ModuleCat.extendScalars f).obj M, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul s x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

private lemma coefficient_conclusions (k : Type u) [Field k] (m : ℕ)
    (hm : IsUnit (m : Γ(curve k true, ⊤)))
    (e₀ : (b : Bool) → ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
      Sheaf.H ((curve k b).rootsOfUnitySheaf m) 0)
    (e₁ : ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
      Sheaf.H ((curve k true).rootsOfUnitySheaf m) 1)
    (he₁ : e₁ 1 = generator k m hm)
    (hr : ∀ r, rootRestriction k m 0 (e₀ false r) = e₀ true r)
    (hv : ∀ (b : Bool) (q : ℕ), (if b then 1 else 0) < q →
      Subsingleton (Sheaf.H ((curve k b).rootsOfUnitySheaf m) q))
    (α : (b : Bool) → (q : ℕ) →
      tensorLeft (ModuleCat.of (ULift.{u + 1} (ZMod m))
          (Sheaf.H ((curve k b).rootsOfUnitySheaf m) q)) ⋙
          forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1} ≅
        Scheme.kummerAbelianTwist (curve k b) m ⋙
          Sheaf.functorH (curve k b).smallEtaleTopology q)
    (hfull : (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))
      AddCommGrpCat.{u + 1}).Full)
    (hunit : ∀ b : Bool, IsIso (Scheme.kummerCoefficientInsertion (curve k b) m
      (ModuleCat.of (ULift.{u + 1} (ZMod m)) (ULift.{u + 1} (ZMod m))) 1)) :
    (∀ (A : Type (u + 1)) [CommRing A] [Finite A]
          (hA : ((m : ℕ) : A) = 0),
        (∀ b : Bool, ∃ E₀ : A ≃ₗ[A]
            (ringCoefficientCohomology k b m A hA 0),
          ∀ a : A, E₀ a = Sheaf.H.map
            (Scheme.kummerCoefficientInsertion (curve k b) m
              (ringCoefficientModule m A hA) a) 0 ((e₀ b 1))) ∧
        (∀ (b : Bool) (q : ℕ), (if b then 1 else 0) < q →
          Subsingleton (ringCoefficientCohomology k b m A hA q)) ∧
        (∃ e₁ : A ≃ₗ[A] (ringCoefficientCohomology k true m A hA 1),
          ∀ a : A, e₁ a = Sheaf.H.map
            (Scheme.kummerCoefficientInsertion (curve k true) m
              (ringCoefficientModule m A hA) a) 1 (generator k m hm)) ∧
        (∀ (b : Bool) (q : ℕ),
          Finite (ringCoefficientCohomology k b m A hA q) ∧
          Module.Finite A (ringCoefficientCohomology k b m A hA q)) ∧
        (∀ (b : Bool) (q : ℕ), ∃ e :
            ringCoefficientTensor k b m A hA q ≃ₗ[A]
              ringCoefficientCohomology k b m A hA q,
          ∀ (x : Sheaf.H ((curve k b).rootsOfUnitySheaf m) q) (a : A),
            e (a ⊗ₜ[ULift.{u + 1} (ZMod m),
                ringCoefficientScalar m A hA] x) =
              Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) m
                (ringCoefficientModule m A hA) a) q x) ∧
        (∀ (B : Type (u + 1)) [CommRing B] [Finite B]
            (hB : ((m : ℕ) : B) = 0)
            (f : ringCoefficientModule m A hA →ₗ[ULift.{u + 1} (ZMod m)]
              ringCoefficientModule m B hB)
            (b : Bool) (q : ℕ)
            (x : Sheaf.H ((curve k b).rootsOfUnitySheaf m) q) (a : A),
          Sheaf.H.map ((Scheme.kummerAbelianTwist (curve k b) m).map
              (ModuleCat.ofHom f)) q
            (Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) m
              (ringCoefficientModule m A hA) a) q x) =
            Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) m
              (ringCoefficientModule m B hB) (f a)) q x) ∧
        (∃! res : ringCoefficientCohomology k false m A hA 0 →ₗ[A]
            ringCoefficientCohomology k true m A hA 0,
          (∀ (x : Sheaf.H ((curve k false).rootsOfUnitySheaf m) 0) (a : A),
            res (Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k false) m
              (ringCoefficientModule m A hA) a) 0 x) =
              Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k true) m
                (ringCoefficientModule m A hA) a) 0
                  (rootRestriction k m 0 x)) ∧
          (∀ a : A, res (Sheaf.H.map
              (Scheme.kummerCoefficientInsertion (curve k false) m
                (ringCoefficientModule m A hA) a) 0 ((e₀ false 1))) =
            Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k true) m
              (ringCoefficientModule m A hA) a) 0 ((e₀ true 1)))) ∧
        (∀ (B : Type (u + 1)) [CommRing B] [Finite B]
            (hB : ((m : ℕ) : B) = 0) (φ : A →+* B) (b : Bool) (q : ℕ),
          ∃ e : (ModuleCat.extendScalars φ).obj
              (ringCoefficientCohomology k b m A hA q) ≃ₗ[B]
                ringCoefficientCohomology k b m B hB q,
            ∀ (x : Sheaf.H ((curve k b).rootsOfUnitySheaf m) q)
                (a : A) (c : B),
              e (c ⊗ₜ[A, φ]
                (Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) m
                  (ringCoefficientModule m A hA) a) q x)) =
                Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) m
                  (ringCoefficientModule m B hB) (φ a * c)) q x)) := by
  have := hfull
  have (b : Bool) := hunit b
  have hins (b : Bool) (q : ℕ)
      (e : ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
        Sheaf.H ((curve k b).rootsOfUnitySheaf m) q)
      (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (m : A) = 0) :
      Function.Bijective (insertionLinear k b m A hA q (e 1)) :=
    basis_insertion_bijective k b m q e (basisFunctorIso k b m q e (α b q)) A hA
  have h0 (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (m : A) = 0) (b : Bool) :
      Function.Bijective (insertionLinear k b m A hA 0 (e₀ b 1)) :=
    hins b 0 (e₀ b) A hA
  have h1 (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (m : A) = 0) :
      Function.Bijective (insertionLinear k true m A hA 1 (e₁ 1)) :=
    hins true 1 e₁ A hA
  have hb (b : Bool) (q : ℕ) (hq : q ≤ (if b then 1 else 0)) :
      ∃ e : ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
          Sheaf.H ((curve k b).rootsOfUnitySheaf m) q,
        ∀ (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (m : A) = 0),
          Function.Bijective (insertionLinear k b m A hA q (e 1)) := by
    cases q with
    | zero => exact ⟨e₀ b, fun A _ _ hA ↦ h0 A hA b⟩
    | succ q =>
      cases b with
      | false => simp at hq
      | true =>
        have : q = 0 := by simpa using hq
        subst q
        exact ⟨e₁, fun A _ _ hA ↦ h1 A hA⟩
  -- Assemble the coefficient clauses from the derived bases and vanishing.
  intro A _ _ hA
  have hvan (b : Bool) (q : ℕ) (hq : (if b then 1 else 0) < q) :
      Subsingleton (ringCoefficientCohomology k b m A hA q) :=
    by
      have := hv b q hq
      exact derived_coefficient_vanishing k b m q (α b q) A hA
  refine ⟨?_, hvan, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    exact ⟨LinearEquiv.ofBijective _ (h0 A hA b), fun _ ↦ rfl⟩
  · refine ⟨LinearEquiv.ofBijective _ (h1 A hA), ?_⟩
    intro a
    change Sheaf.H.map _ 1 (e₁ 1) = _
    rw [he₁]
  · intro b q
    have hfin : Finite (ringCoefficientCohomology k b m A hA q) := by
      by_cases hq : (if b then 1 else 0) < q
      · let := hvan b q hq
        infer_instance
      · obtain ⟨e, he⟩ := hb b q (Nat.le_of_not_gt hq)
        exact Finite.of_equiv A (LinearEquiv.ofBijective _ (he A hA)).toEquiv
    exact ⟨hfin, Module.Finite.of_finite⟩
  · intro b q
    by_cases hq : (if b then 1 else 0) < q
    · let := hv b q hq
      have := hvan b q hq
      have : Subsingleton (ringCoefficientTensor k b m A hA q) :=
        extension_subsingleton (ringCoefficientScalar m A hA)
          (ModuleCat.of _ (Sheaf.H ((curve k b).rootsOfUnitySheaf m) q))
      exact ⟨LinearEquiv.ofSubsingleton _ _, fun _ _ ↦ Subsingleton.elim _ _⟩
    · obtain ⟨e, he⟩ := hb b q (Nat.le_of_not_gt hq)
      exact tensor_comparison_of_basis k b m A hA q e (he A hA)
  · intro B _ _ hB f b q x a
    exact (Sheaf.H.map_comp_apply _ _ x).symm.trans
      (congrArg (fun g ↦ Sheaf.H.map g q x)
        (insertion_map (curve k b) m (ringCoefficientModule m A hA)
          (ringCoefficientModule m B hB)
          (ModuleCat.ofHom (X := ringCoefficientModule m A hA)
            (Y := ringCoefficientModule m B hB) f) a))
  · exact restriction_of_basis k m A hA e₀ hr (h0 A hA)
  · intro B _ _ hB φ b q
    by_cases hq : (if b then 1 else 0) < q
    · let := hvan b q hq
      have : Subsingleton (ringCoefficientCohomology k b m B hB q) := by
        have := hv b q hq
        exact derived_coefficient_vanishing k b m q (α b q) B hB
      have := extension_subsingleton φ (ringCoefficientCohomology k b m A hA q)
      exact ⟨LinearEquiv.ofSubsingleton _ _, fun _ _ _ ↦ Subsingleton.elim _ _⟩
    · obtain ⟨e, he⟩ := hb b q (Nat.le_of_not_gt hq)
      exact scalar_extension_of_basis k b m A B hA hB φ q e (he A hA) (he B hB)

/-- Kummer computations for arbitrary finite commutative coefficient rings.
Source: blueprint thm-pur-kummer-affine-line, corrected by expert message 1385,
answers 5–6, 2026-11-01; Stacks Tags 03PK, 03PL, 03SC and 0F12
(blueprint: thm-pur-kummer-affine-line).

Proof: First use lem-pur-kummer-root-line-computation with `m = ℓ^N` and `ζ`.
The normalized degree-zero classes restrict identically, the actual boundary of `t`
is the degree-one generator, and the remaining groups vanish. The module-forgetting
comparison identifies these with the cohomology of `K = RΓ(μ_m)` in `D(R)`.
Both curves are affine and have torsion cohomological dimension at most one. Apply
lem-kun-0f12 to `μ_m[0]` and `A[0]`. The primitive-root trivialization makes `μ_m`
free, so flat-single normalization identifies its derived tensor with the ordinary
twist even for nonflat `A`. The cohomology of `K` is zero or free of rank one;
lem-pur-flat-cohomology-derived-tensor therefore gives the ordinary tensor comparison.
Naturality and invertibility of ordinary unit insertion show that the normalized
insertion maps are surjective: the derived comparison makes the coefficient cohomology
functor full, so a map sending the root basis to any class lifts to a map `R → A`.
The comparison also gives equal finite cardinalities, hence bijectivity. The root bases
then give the tensor map with pure tensors `x ⊗ a ↦ H(i_a)(x)`, coefficient naturality,
restriction, and finite modules. Tensor associativity gives extension along
any `A → B`, with precisely the displayed degree-zero and Kummer formulas. All steps
include the zero ring and require no flatness or freeness of `A`. -/
theorem kummer_affine_line_arbitrary (k : Type u) [Field k] [IsAlgClosed k]
    (ℓ N : ℕ) (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k)) (hN : 1 ≤ N)
    (ζ : kˣ) (hζ : IsPrimitiveRoot ζ (ℓ ^ N)) :
    ∃ (hm : IsUnit ((ℓ ^ N : ℕ) : Γ(curve k true, ⊤)))
      (z : (b : Bool) → Sheaf.H ((curve k b).rootsOfUnitySheaf (ℓ ^ N)) 0),
      (∀ b : Bool,
        (kernel.ι (ℓ ^ N • 𝟙 (curve k b).gmSheaf)).hom.app
          (op (Scheme.Etale.mk (𝟙 (curve k b))))
          (Sheaf.H.equiv₀ _ (MorphismProperty.Over.mkIdTerminal @Etale (curve k b)) (z b)) =
          ULift.up (Additive.ofMul (Units.map (scalar k b).toMonoidHom ζ))) ∧
      rootRestriction k (ℓ ^ N) 0 (z false) = z true ∧
      (∀ (A : Type (u + 1)) [CommRing A] [Finite A]
          (hA : ((ℓ ^ N : ℕ) : A) = 0),
        (∀ b : Bool, ∃ e₀ : A ≃ₗ[A]
            (ringCoefficientCohomology k b (ℓ ^ N) A hA 0),
          ∀ a : A, e₀ a = Sheaf.H.map
            (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N)
              (ringCoefficientModule (ℓ ^ N) A hA) a) 0 (z b)) ∧
        (∀ (b : Bool) (q : ℕ), (if b then 1 else 0) < q →
          Subsingleton (ringCoefficientCohomology k b (ℓ ^ N) A hA q)) ∧
        (∃ e₁ : A ≃ₗ[A] (ringCoefficientCohomology k true (ℓ ^ N) A hA 1),
          ∀ a : A, e₁ a = Sheaf.H.map
            (Scheme.kummerCoefficientInsertion (curve k true) (ℓ ^ N)
              (ringCoefficientModule (ℓ ^ N) A hA) a) 1 (generator k (ℓ ^ N) hm)) ∧
        (∀ (b : Bool) (q : ℕ),
          Finite (ringCoefficientCohomology k b (ℓ ^ N) A hA q) ∧
          Module.Finite A (ringCoefficientCohomology k b (ℓ ^ N) A hA q)) ∧
        (∀ (b : Bool) (q : ℕ), ∃ e :
            ringCoefficientTensor k b (ℓ ^ N) A hA q ≃ₗ[A]
              ringCoefficientCohomology k b (ℓ ^ N) A hA q,
          ∀ (x : Sheaf.H ((curve k b).rootsOfUnitySheaf (ℓ ^ N)) q) (a : A),
            e (a ⊗ₜ[ULift.{u + 1} (ZMod (ℓ ^ N)),
                ringCoefficientScalar (ℓ ^ N) A hA] x) =
              Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N)
                (ringCoefficientModule (ℓ ^ N) A hA) a) q x) ∧
        (∀ (B : Type (u + 1)) [CommRing B] [Finite B]
            (hB : ((ℓ ^ N : ℕ) : B) = 0)
            (f : ringCoefficientModule (ℓ ^ N) A hA →ₗ[ULift.{u + 1} (ZMod (ℓ ^ N))]
              ringCoefficientModule (ℓ ^ N) B hB)
            (b : Bool) (q : ℕ)
            (x : Sheaf.H ((curve k b).rootsOfUnitySheaf (ℓ ^ N)) q) (a : A),
          Sheaf.H.map ((Scheme.kummerAbelianTwist (curve k b) (ℓ ^ N)).map
              (ModuleCat.ofHom f)) q
            (Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N)
              (ringCoefficientModule (ℓ ^ N) A hA) a) q x) =
            Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N)
              (ringCoefficientModule (ℓ ^ N) B hB) (f a)) q x) ∧
        (∃! res : ringCoefficientCohomology k false (ℓ ^ N) A hA 0 →ₗ[A]
            ringCoefficientCohomology k true (ℓ ^ N) A hA 0,
          (∀ (x : Sheaf.H ((curve k false).rootsOfUnitySheaf (ℓ ^ N)) 0) (a : A),
            res (Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k false) (ℓ ^ N)
              (ringCoefficientModule (ℓ ^ N) A hA) a) 0 x) =
              Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k true) (ℓ ^ N)
                (ringCoefficientModule (ℓ ^ N) A hA) a) 0
                  (rootRestriction k (ℓ ^ N) 0 x)) ∧
          (∀ a : A, res (Sheaf.H.map
              (Scheme.kummerCoefficientInsertion (curve k false) (ℓ ^ N)
                (ringCoefficientModule (ℓ ^ N) A hA) a) 0 (z false)) =
            Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k true) (ℓ ^ N)
              (ringCoefficientModule (ℓ ^ N) A hA) a) 0 (z true))) ∧
        (∀ (B : Type (u + 1)) [CommRing B] [Finite B]
            (hB : ((ℓ ^ N : ℕ) : B) = 0) (φ : A →+* B) (b : Bool) (q : ℕ),
          ∃ e : (ModuleCat.extendScalars φ).obj
              (ringCoefficientCohomology k b (ℓ ^ N) A hA q) ≃ₗ[B]
                ringCoefficientCohomology k b (ℓ ^ N) B hB q,
            ∀ (x : Sheaf.H ((curve k b).rootsOfUnitySheaf (ℓ ^ N)) q)
                (a : A) (c : B),
              e (c ⊗ₜ[A, φ]
                (Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N)
                  (ringCoefficientModule (ℓ ^ N) A hA) a) q x)) =
                Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N)
                  (ringCoefficientModule (ℓ ^ N) B hB) (φ a * c)) q x)) := by
  classical
  let m := ℓ ^ N
  have hmpos : 0 < m := by
    change 0 < ℓ ^ N
    rw [← Nat.sub_add_cancel hN]
    exact pow_pos hℓ.pos _
  let : NeZero m := ⟨ne_of_gt hmpos⟩
  have hmk : IsUnit (m : k) := by simpa only [m, Nat.cast_pow] using hℓk.pow N
  let hm : IsUnit (m : Γ(curve k true, ⊤)) := by
    simpa only [map_natCast] using hmk.map (scalar k true)
  let (b : Bool) : ConnectedSpace (curve k b) := by
    cases b <;> dsimp [curve] <;> infer_instance
  obtain ⟨z, hz, hres, he0, hv, ⟨e₁, he₁⟩⟩ :=
    kummer_root_line_computation k m hmpos hmk ζ hζ hm
  let e₀ : (b : Bool) → ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
      Sheaf.H ((curve k b).rootsOfUnitySheaf m) 0 := fun b ↦ (he0 b).choose
  have he (b : Bool) : e₀ b 1 = z b := (he0 b).choose_spec
  have hr (a : ULift.{u + 1} (ZMod m)) :
      rootRestriction k m 0 (e₀ false a) = e₀ true a := by
    obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective a.down
    have ha : a = n • (1 : ULift.{u + 1} (ZMod m)) := by
      apply ULift.ext
      change a.down = n • (1 : ZMod m)
      simpa only [nsmul_eq_mul, mul_one] using hn.symm
    rw [ha, map_nsmul, map_nsmul, map_nsmul, he, he, hres]
  let (b : Bool) : CompactSpace (curve k b) := by
    cases b <;> dsimp [curve] <;> infer_instance
  let (b : Bool) : QuasiSeparatedSpace (curve k b) := by
    cases b <;> dsimp [curve] <;> infer_instance
  have hflat (b : Bool) (q : ℕ) :
      Module.Flat (ULift.{u + 1} (ZMod m)) (Sheaf.H ((curve k b).rootsOfUnitySheaf m) q) := by
    by_cases hq : (if b then 1 else 0) < q
    · have := hv b q hq
      infer_instance
    · cases q with
      | zero => exact Module.Flat.of_linearEquiv (e₀ b).symm
      | succ q =>
        cases b with
        | false => simp at hq
        | true =>
          have hq0 : q = 0 := by simp only [ite_true] at hq; omega
          subst q
          exact Module.Flat.of_linearEquiv e₁.symm
  have hc (b : Bool) := KummerDerived.kummer_derived_coefficient_comparison
    (curve k b) m hmpos (line_cd k b)
    ((curve k b).constantZModIsoRootsOfUnitySheaf m (structureMap k b)
      (IsPrimitiveRoot.coe_units_iff.mpr hζ)).symm
    (if b then 1 else 0) (hv b) (hflat b)
  let α (b : Bool) (q : ℕ) := ((hc b).1 q).some
  have := (hc false).2.1
  have (b : Bool) : IsIso (Scheme.kummerCoefficientInsertion (curve k b) m
      (ModuleCat.of (ULift.{u + 1} (ZMod m)) (ULift.{u + 1} (ZMod m))) 1) := (hc b).2.2
  refine ⟨hm, fun b ↦ e₀ b 1, ?_, hr 1, ?_⟩
  · intro b
    change (kernel.ι (m • 𝟙 (curve k b).gmSheaf)).hom.app
      (op (Scheme.Etale.mk (𝟙 (curve k b))))
      (Sheaf.H.equiv₀ ((curve k b).rootsOfUnitySheaf m)
        (MorphismProperty.Over.mkIdTerminal @Etale (curve k b)) (e₀ b 1)) = _
    rw [he]
    exact hz b
  · exact coefficient_conclusions k m hm e₀ e₁ he₁ hr hv α
      (hc false).2.1 (fun b ↦ (hc b).2.2)

end AlgebraicGeometry.KummerLine
