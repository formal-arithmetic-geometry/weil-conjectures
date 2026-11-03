/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.PoincareDuality.CohomologicalFiniteness.ConnectedIntegralCoefficientSections
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.CoefficientFiniteDescentSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapSections
import WeilConjectures.CategoryTheory.ModuleObjects.Preadditive
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Rational sections computed by the localization colimit

Source: current blueprint prop-cohomological-finiteness, final paragraph of step 4.
(blueprint: lem-weil-connected-rational-coefficient-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.Scheme Opposite
open scoped CategoryTheory.Obj

namespace WeilConjectures.CohomologicalFiniteness

private instance (X : Scheme.{u}) : (upperStarFromPoint X).Additive := by
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    (upperStarFromPointAdjunction X).leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  exact Functor.additive_of_preservesBinaryBiproducts _

set_option maxHeartbeats 800000 in
-- The point adjunction expands the two inverse-image functors.
private theorem continuous_constants_pullback (X : Scheme.{u}) (T : Type)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] (t : T) :
    (condensedRingScalarSections (Profinite.continuousMapRingObj T) X
        (Profinite.continuousMapConstRingHom T t)).hom ≫ continuousMapComparison X T =
      (continuousMapSectionRingHom X T (ContinuousMap.const X t)).hom := by
  change (Γ.mapFunctor (upperStarFromPoint X)
    (Profinite.continuousMapConstRingHom T t)).hom ≫ _ = _
  rw [Γ.mapFunctor_hom, Category.assoc]
  refine (upperStarFromPointAdjunction X).ε_comp_map_comp_homEquiv_symm_eq _ _ _ ?_
  refine Sheaf.unitHomEval_injective (J := coherentTopology Profinite.{u})
    Profinite.isTerminalPUnit _ ?_
  have hs : Sheaf.unitHomEval (J := coherentTopology Profinite.{u})
      (Profinite.of PUnit.{u + 1}) (Profinite.continuousMapConstRingHom T t).hom =
        ULift.up (ContinuousMap.const (Profinite.of PUnit.{u + 1}) t) :=
    Sheaf.unitHomEval_ringHomΓSheafCompose (J := coherentTopology Profinite.{u})
      (Profinite.of PUnit.{u + 1}) (Profinite.continuousMapRingSheaf.{u} T)
      (Profinite.continuousMapConstSectionRingHom.{u} T) (fun _ _ ↦ rfl) t
  rw [Sheaf.unitHomEval_comp (J := coherentTopology Profinite.{u}), hs]
  rw [Functor.LaxMonoidal.comp_ε, Functor.comp_map, Category.assoc, ← Functor.map_comp]
  erw [Sheaf.unitHomEval_ε_comp_sheafPushforwardContinuous_map
    (J := coherentTopology Profinite.{u}) (K := Scheme.ProEt.topology specZ.{u})
    (T := Profinite.of PUnit.{u + 1}) profiniteToProEt.{u}
    (Scheme.ProEt.isTerminalMkId specZ.{u})]
  rw [unitHomEval_ε_comp_lowerStar_map (toSpecZ X),
    unitHomEval_continuousMapSectionRingHom]
  rfl


private def coefficientFunction (X : Scheme.{u}) (T : Type)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : Γ (condensedRingObj (Profinite.continuousMapRingObj T) X)) : C(X, T) :=
  (Sheaf.unitHomEval (J := Scheme.ProEt.topology X) (Scheme.ProEt.mk (𝟙 X))
    (s.hom ≫ continuousMapComparison X T)).down


private theorem coefficientFunction_constant (X : Scheme.{u}) (T : Type)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] (t : T) :
    coefficientFunction X T
        (condensedRingScalarSections (Profinite.continuousMapRingObj T) X
          (Profinite.continuousMapConstRingHom T t)) = ContinuousMap.const X t := by
  unfold coefficientFunction
  rw [continuous_constants_pullback, unitHomEval_continuousMapSectionRingHom]
  rfl

private theorem localization_section_representative
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (j : ℕ → (Mod.regular
      (completedCoefficient X (Profinite.padicIntegersCondensedRing ell E)).X ⟶
        completedRationalModule X ell E))
    (hrec : ∀ n, ell • j (n + 1) = j n)
    (huni : ∀ (B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (completedCoefficient X (Profinite.padicIntegersCondensedRing ell E)).X)
      (b : ℕ → (Mod.regular
        (completedCoefficient X (Profinite.padicIntegersCondensedRing ell E)).X ⟶ B)),
      (∀ n, ell • b (n + 1) = b n) →
      ∃! a : completedRationalModule X ell E ⟶ B, ∀ n, j n ≫ a = b n)
    (s : Γ (completedCoefficient X (Profinite.padicSubfieldCondensedRing ell E)).X) :
    ∃ (n : ℕ) (t : Γ
        (completedCoefficient X (Profinite.padicIntegersCondensedRing ell E)).X),
      t.hom ≫ (j n).hom = s.hom := by
  classical
  let M := Mod.regular
    (completedCoefficient X (Profinite.padicIntegersCondensedRing ell E)).X
  let D := Functor.ofSequence (fun _ ↦ ell • 𝟙 M)
  let c : Cocone D := ⟨completedRationalModule X ell E,
    NatTrans.ofSequence j (fun n ↦ by
      simp only [D, Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      change (ell • 𝟙 M) ≫ j (n + 1) = j n ≫ 𝟙 _
      simpa only [Preadditive.nsmul_comp, Category.id_comp, Category.comp_id] using hrec n)⟩
  have hleg (d : Cocone D) : ∀ n, ell • d.ι.app (n + 1) = d.ι.app n := by
    intro n
    have h := d.w (homOfLE (Nat.le_succ n))
    dsimp only [D] at h
    rw [Functor.ofSequence_map_homOfLE_succ] at h
    change (ell • 𝟙 M) ≫ (d.ι.app (n + 1) : M ⟶ d.pt) = d.ι.app n at h
    simpa only [Preadditive.nsmul_comp, Category.id_comp] using h
  let hc : IsColimit c :=
    { desc := fun d ↦ (huni d.pt (fun n ↦ d.ι.app n) (hleg d)).choose
      fac := fun d n ↦ (huni d.pt (fun n ↦ d.ι.app n) (hleg d)).choose_spec.1 n
      uniq := fun d a ha ↦
        (huni d.pt (fun n ↦ d.ι.app n) (hleg d)).choose_spec.2 a ha }
  let U : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (completedCoefficient X (Profinite.padicIntegersCondensedRing ell E)).X ⥤
      Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} := Mod.forget _
  let d := U.mapCocone c
  have hd := isColimitOfPreserves U hc
  let e : ℕ ≌ AsSmall.{u + 1} ℕ := AsSmall.equiv
  let L := e.inverse
  let F := L ⋙ D ⋙ U
  let V := Scheme.ProEt.mk (𝟙 X)
  have : CompactSpace V.left := inferInstanceAs (CompactSpace X)
  have : QuasiSeparatedSpace V.left := inferInstanceAs (QuasiSeparatedSpace X)
  let A := (sheafSections (Scheme.ProEt.topology X) Ab.{u + 1}).obj (op V)
  have hbij := (filteredColimit_sections_abelian X V (AsSmall.{u + 1} ℕ) F).2
    (Or.inl (inferInstanceAs (QuasiSeparatedSpace X)))
  have : IsIso (colimit.post F A) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have : PreservesColimit F A := preservesColimit_of_isIso_post A F
  have hcol := isColimitOfPreserves (CategoryTheory.forget Ab.{u + 1})
    (isColimitOfPreserves A ((Functor.Final.isColimitWhiskerEquiv L d).symm hd))
  obtain ⟨n, t, ht⟩ := Types.jointly_surjective _ hcol
    (Sheaf.unitHomEval.{u + 1} V s.hom)
  obtain ⟨t', ht'⟩ := Sheaf.unitHomEval_surjective.{u + 1} (Scheme.ProEt.isTerminalMkId X) M.X t
  refine ⟨L.obj n, Γ.ofHom t', ?_⟩
  apply Sheaf.unitHomEval_injective.{u + 1} (J := Scheme.ProEt.topology X)
    (Scheme.ProEt.isTerminalMkId X)
  change (j (L.obj n)).hom.hom.app (op V) (Sheaf.unitHomEval.{u + 1} V t') =
    Sheaf.unitHomEval.{u + 1} V s.hom
  rw [ht']
  exact ht

private theorem scalar_integral_inclusion
    (X : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (r : PadicAlgCl.integers ell E) :
    (condensedRingScalarSections (Profinite.padicIntegersRingObj ell E) X
        (Profinite.continuousMapConstRingHom _ r)).hom ≫
      (completedCoefficientMap X
        (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ell E)).hom =
    (condensedRingScalarSections (Profinite.continuousMapRingObj E) X
      (Profinite.continuousMapConstRingHom E r.val)).hom := by
  let f := Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ell E
  let U := sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})
  have hn : (Profinite.continuousMapConstRingHom (PadicAlgCl.integers ell E) r).hom ≫
      U.map f = (Profinite.continuousMapConstRingHom E r.val).hom := by
    apply Sheaf.unitHomEval_injective.{u + 1} (J := coherentTopology Profinite.{u})
      Profinite.isTerminalPUnit
    have hi : Sheaf.unitHomEval (J := coherentTopology Profinite.{u})
        (Profinite.of PUnit.{u + 1})
        (Profinite.continuousMapConstRingHom (PadicAlgCl.integers ell E) r).hom =
      ULift.up (ContinuousMap.const (Profinite.of PUnit.{u + 1}) r) :=
      Sheaf.unitHomEval_ringHomΓSheafCompose
      (J := coherentTopology Profinite.{u}) (Profinite.of PUnit.{u + 1})
      (Profinite.continuousMapRingSheaf.{u} (PadicAlgCl.integers ell E))
      (Profinite.continuousMapConstSectionRingHom.{u} (PadicAlgCl.integers ell E))
      (fun _ _ ↦ rfl) r
    have he : Sheaf.unitHomEval (J := coherentTopology Profinite.{u})
        (Profinite.of PUnit.{u + 1}) (Profinite.continuousMapConstRingHom E r.val).hom =
      ULift.up (ContinuousMap.const (Profinite.of PUnit.{u + 1}) r.val) :=
      Sheaf.unitHomEval_ringHomΓSheafCompose
      (J := coherentTopology Profinite.{u}) (Profinite.of PUnit.{u + 1})
      (Profinite.continuousMapRingSheaf.{u} E)
      (Profinite.continuousMapConstSectionRingHom.{u} E) (fun _ _ ↦ rfl) r.val
    change (U.map f).hom.app (op (Profinite.of PUnit.{u + 1}))
      (Sheaf.unitHomEval (Profinite.of PUnit.{u + 1})
        (Profinite.continuousMapConstRingHom (PadicAlgCl.integers ell E) r).hom) = _
    rw [hi, he]
    rfl
  change (Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
    (upperStarFromPoint X).map _) ≫ (upperStarFromPoint X).map _ =
      Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map _
  rw [Category.assoc, ← Functor.map_comp, hn]

/-- On a connected qcqs scheme, rational coefficient sections are exactly scalars.

Source: current blueprint prop-cohomological-finiteness, final paragraph of step 4;
sk-prop-sfb-qlbar-colimit-x and det-lem-coefficient-finite-descent-sections.
(blueprint: lem-weil-connected-rational-coefficient-sections).

Proof: the localization theorem presents E_X as the sequential colimit of integral
regular modules under multiplication by ell. On a qcqs scheme, terminal sections
preserve this filtered colimit, so every section comes from an integral section at
some stage. The integral residue-limit calculation makes this section constant.
The zeroth colimit leg is integral inclusion; the recurrence and invertibility of
ell show that the n-th leg sends a constant r to the constant r/ell^n. Thus all rational
sections are scalars. Evaluation at a point proves injectivity. No realization of
all E-valued continuous maps is used to prove surjectivity.
-/
theorem connected_rationalScalarSections_bijective (X : Scheme.{u}) [ConnectedSpace X]
    [CompactSpace X] [QuasiSeparatedSpace X]
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell) :
    Function.Bijective
      (condensedRingScalarSections (Profinite.continuousMapRingObj E) X) := by
  classical
  let x : X := Classical.choice inferInstance
  let scalar (a : E) := condensedRingScalarSections (Profinite.continuousMapRingObj E) X
    (Profinite.continuousMapConstRingHom E a)
  have scalar_nsmul (n : ℕ) (a : E) : scalar (n • a) = n • scalar a := by
    exact map_nsmul ((condensedRingScalarSections (Profinite.continuousMapRingObj E) X).comp
      (Profinite.continuousMapConstRingHom E)) n a
  obtain ⟨j, hj, _⟩ := completedCondensedRational ell E
  obtain ⟨hiso, hzero, hrec, huni⟩ := hj X
  have : IsIso (ell • 𝟙 (completedRationalModule X ell E).X) := hiso
  have hleg (n : ℕ) (r : PadicAlgCl.integers ell E) :
      (condensedRingScalarSections (Profinite.padicIntegersRingObj ell E) X
          (Profinite.continuousMapConstRingHom _ r)).hom ≫ (j X n).hom =
        (scalar (r.val / (ell : E) ^ n)).hom := by
    induction n with
    | zero =>
      rw [hzero]
      simpa only [pow_zero, div_one] using scalar_integral_inclusion X ell E r
    | succ n hn =>
      apply (cancel_mono (ell • 𝟙 (completedRationalModule X ell E).X)).1
      have hrec' : (j X (n + 1)).hom ≫ (ell • 𝟙 _) = (j X n).hom := by
        simpa only [Preadditive.comp_nsmul, Category.comp_id, Mod.nsmul_hom] using
          congrArg Mod.Hom.hom (hrec n)
      rw [Category.assoc, hrec', hn, Preadditive.comp_nsmul, Category.comp_id]
      change (scalar (r.val / (ell : E) ^ n)).hom =
        (ell • scalar (r.val / (ell : E) ^ (n + 1))).hom
      rw [← scalar_nsmul]
      apply congrArg (fun a : E ↦ (scalar a).hom)
      have hell : (ell : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ell.Prime).ne_zero
      rw [nsmul_eq_mul]
      field_simp [pow_succ, hell]; ring
  constructor
  · intro a b hab
    obtain ⟨a', rfl⟩ := Profinite.continuousMapConstRingHom_surjective E a
    obtain ⟨b', rfl⟩ := Profinite.continuousMapConstRingHom_surjective E b
    have h := congrArg (fun z ↦ coefficientFunction X E z x) hab
    rw [coefficientFunction_constant, coefficientFunction_constant] at h
    exact congrArg _ h
  · intro s
    obtain ⟨n, t, ht⟩ := localization_section_representative X ell E (j X) hrec huni s
    obtain ⟨a, ha⟩ := (connected_integralScalarSections_bijective X ell E).2 t
    obtain ⟨r, rfl⟩ := Profinite.continuousMapConstRingHom_surjective _ a
    refine ⟨Profinite.continuousMapConstRingHom E (r.val / (ell : E) ^ n), ?_⟩
    apply Γ.ext
    exact (hleg n r).symm.trans ((congrArg (fun z ↦ z.hom ≫ (j X n).hom) ha).trans ht)

end WeilConjectures.CohomologicalFiniteness
