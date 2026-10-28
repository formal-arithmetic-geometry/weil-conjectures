/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.TateTwist.ProEtale
public import Sheaf.Targets.PoincareTateBoundedConstructible
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.Paper.CondensedQbarCoefficientConstruction
import Sheaf.SmoothPurity.RepresentingTraceClassification
import Sheaf.SmoothPurity.NativeTraceSystem
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek

/-! The representing trace required by condensed smooth purity.

The intended geometric construction uses the normalized finite and adic purity system.
The current existential-uniqueness statement below omits that normalization. The private
counterexample refutes it at an algebraically closed point in relative dimension zero,
independently of the disputed theorem. Merely requiring Hom bijections leaves the action
of automorphisms of the representing object unrestricted.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj
open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- The declared finite and integral input steps apply to the actual underlying
morphism of schemes. The native-system theorem retains all finite trace quotient
counit equations for this same compactification. This lemma extracts only the
reconstruction conclusion; it constructs no arbitrary trace or orientation data.
Source: def-route-smooth-trace, Steps 1--2, and sk-thm-purity-transport, Steps 1--2. -/
private theorem smoothTrace_nativeReconstructionInputs
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (d : ℕ) (hsm : SmoothOfRelativeDimension d f.left) :
    ∃ (hfq : QuasiCompact f.left) (hfs : IsSeparated f.left)
      (c : Compactification f.left) (hX : IsNoetherian X.left) (hY : IsNoetherian Y.left),
      Scheme.PurityIntegralTower.ReconstructionResult ell f.left d hfq hfs c hX hY := by
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let : f.left.IsOver (Spec (.of k)) := ⟨Over.w f⟩
  let : IsSeparated (X.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated X.hom)
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  let : QuasiCompact (X.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact X.hom)
  let : IsSeparated (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Y.hom)
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  let : QuasiCompact (Y.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Y.hom)
  have := hsm
  obtain ⟨hfq, hfs, c, hX, hY, hrec, _⟩ :=
    smoothTrace_nativeSystem ell k (Fact.out : (ringChar k).Prime).pos f.left d
  exact ⟨hfq, hfs, c, hX, hY, hrec⟩

section NormalizedOpenTrace

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The supplied zero-Tate orientation gives an actual identification with the native
unit. Source: def-route-smooth-trace, the dimension-zero normalization, and the
single-functor unit comparison. Full faithfulness lifts the specified ambient
isomorphism; no representing witness or smooth-purity assertion is chosen. -/
private noncomputable def smoothTrace_zeroSourceIso
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hM : M.obj ≅ (shiftFunctor _ (2 * ((0 : ℕ) : ℤ))).obj
      (tateTwistDerived X.left ℓ 0)) :
    M ≅ 𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) := by
  let e : tateTwistDerived X.left ℓ 0 ≅
      𝟙_ (DerivedCategory (Mod (Sheaf (ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))) :=
    DerivedCategory.singleFunctorObjUnitIso _
  exact (ObjectProperty.ι _).preimageIso
    (hM ≪≫ ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _) ≪≫ e)

/-- The open comparison and the specified source/target identifications construct the
orientation to the chosen exceptional right adjoint. Source: def-route-smooth-trace,
dimension-zero normalization. In particular the source identification is retained,
rather than replaced by an arbitrary isomorphism to the exceptional object. -/
private noncomputable def smoothTrace_openOrientation
    (j : X ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hM : M.obj ≅ (shiftFunctor _ (2 * ((0 : ℕ) : ℤ))).obj
      (tateTwistDerived X.left ℓ 0))
    (U : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hU : U = 𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :
    M ≅ (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj U :=
  smoothTrace_zeroSourceIso ℓ M hM ≪≫
    (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).symm ≪≫
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).mapIso
        (eqToIso hU).symm

/-- The normalized trace for an open immersion is the explicit exceptional counit
composite. Source: def-route-smooth-trace, Steps 3--4, and the open normalization in
sk-thm-purity-transport. This is a construction from the specified orientation. -/
private noncomputable def smoothTrace_openCounit
    (j : X ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hM : M.obj ≅ (shiftFunctor _ (2 * ((0 : ℕ) : ℤ))).obj
      (tateTwistDerived X.left ℓ 0))
    (U : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hU : U = 𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj M ⟶ U :=
  (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map
      (smoothTrace_openOrientation ℓ j M hM U hU).hom ≫
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app U

/-- All Hom maps for this explicitly constructed open trace are bijections.
Source: def-route-smooth-trace, the dimension-zero case of its representing-pair
step. Compose the specified orientation's Hom equivalence with inverse adjunction. -/
private theorem smoothTrace_openCounit_representing
    (j : X ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hM : M.obj ≅ (shiftFunctor _ (2 * ((0 : ℕ) : ℤ))).obj
      (tateTwistDerived X.left ℓ 0))
    (U : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hU : U = 𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :
    ∀ K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      Function.Bijective (fun a : K ⟶ M ↦
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map a ≫
          smoothTrace_openCounit ℓ j M hM U hU) :=
  representingTrace_of_iso _ (boundedConstructibleUpperShriekAdjunction _ ℓ j)
    (smoothTrace_openOrientation ℓ j M hM U hU)

/-- The specified open orientation fixes the trace uniquely. Source:
def-route-smooth-trace, the corrected normalized final step, and
sk-thm-purity-transport, Step 3. Take its explicit counit composite and apply the
inverse laws of the chosen exceptional adjunction. No uniqueness among all
unnormalized representing traces is asserted. -/
private theorem existsUnique_smoothTrace_openNormalized
    (j : X ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hM : M.obj ≅ (shiftFunctor _ (2 * ((0 : ℕ) : ℤ))).obj
      (tateTwistDerived X.left ℓ 0))
    (U : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hU : U = 𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :
    ∃! t : (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj M ⟶ U,
      (∀ K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
        Function.Bijective (fun a : K ⟶ M ↦
          (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map a ≫ t)) ∧
      (boundedConstructibleUpperShriekAdjunction _ ℓ j).homEquiv M U t =
        (smoothTrace_openOrientation ℓ j M hM U hU).hom := by
  let adj := boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ j
  have hn : adj.homEquiv M U (smoothTrace_openCounit ℓ j M hM U hU) =
      (smoothTrace_openOrientation ℓ j M hM U hU).hom := by
    rw [smoothTrace_openCounit, ← adj.homEquiv_counit]
    exact (adj.homEquiv M U).apply_symm_apply _
  refine ⟨smoothTrace_openCounit ℓ j M hM U hU, ⟨?_, hn⟩, ?_⟩
  · exact smoothTrace_openCounit_representing ℓ j M hM U hU
  · intro t ht
    exact (adj.homEquiv M U).injective (ht.2.trans hn.symm)

/-- The exceptional open-unit comparison preserves the actual extension-by-zero
counit. Source: the open comparison is the mate of the compact-support comparison
in def-route-smooth-trace. Apply the mate counit identity, then move the monoidal
unit map through the compact-support comparison by naturality. -/
private theorem smoothTrace_openUnit_counit_formula
    (j : X ⟶ Y) [IsOpenImmersion j.left] :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map
        (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv ≫
      (boundedConstructibleUpperShriekAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _) =
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.app
        (𝟙_ _) ≫
      (boundedConstructibleOpenImmersionLowerShriek
        (Profinite.padicAlgClRingObj ℓ) ℓ j).map
          (Functor.Monoidal.εIso
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j)).hom ≫
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _) := by
  have hc :
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map
          ((boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).app (𝟙_ _)).inv ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _) =
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj (𝟙_ _)) ≫
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _) := by
    exact conjugateEquiv_counit
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
      (boundedConstructibleUpperShriekAdjunction _ ℓ j)
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom (𝟙_ _)
  change (boundedConstructibleLowerShriek _ ℓ j).map
      ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ j)).hom ≫
        ((boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).app (𝟙_ _)).inv) ≫
      _ = _
  rw [Functor.map_comp, Category.assoc, hc, ← Category.assoc]
  rw [(boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.naturality]
  simp only [Category.assoc]

/-- The constructed trace is the ordinary extension-by-zero counit, with exactly
the supplied zero-Tate orientation and the canonical monoidal unit map. Source:
def-route-smooth-trace, dimension-zero normalization. Expand only the small
orientation composite, use the preceding actual counit identity, and move the
source identification through the compact-support comparison by naturality.
This holds for the empty scheme too and makes no global choice of a Tate basis. -/
private theorem smoothTrace_openCounit_extensionByZero
    (j : X ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hM : M.obj ≅ (shiftFunctor _ (2 * ((0 : ℕ) : ℤ))).obj
      (tateTwistDerived X.left ℓ 0)) :
    smoothTrace_openCounit ℓ j M hM (𝟙_ _) rfl =
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.app M ≫
        (boundedConstructibleOpenImmersionLowerShriek
          (Profinite.padicAlgClRingObj ℓ) ℓ j).map
            (smoothTrace_zeroSourceIso ℓ M hM).hom ≫
        (boundedConstructibleOpenImmersionLowerShriek
          (Profinite.padicAlgClRingObj ℓ) ℓ j).map
            (Functor.Monoidal.εIso
              (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j)).hom ≫
          (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _) := by
  simp only [smoothTrace_openCounit, smoothTrace_openOrientation, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, eqToIso_refl, Iso.refl_inv,
    Functor.map_comp, Category.assoc]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [smoothTrace_openUnit_counit_formula, ← Category.assoc,
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.naturality]
  simp only [Category.assoc]

end NormalizedOpenTrace

section Counterexample

private theorem no_unique_representing_trace
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (M : C) (U : D) (e : M ≅ M) (he : e.hom ≠ 𝟙 M) :
    ¬ ∃! t : F.obj M ⟶ U,
      ∀ K : C, Function.Bijective (fun a : K ⟶ M ↦ F.map a ≫ t) := by
  rintro ⟨t, ht, huniq⟩
  exact he ((existsUnique_representingTrace_iff F t ht).1 ⟨t, ht, huniq⟩ e)

private theorem neg_id_ne_of_faithful {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Faithful] [F.Additive]
    (M : C) (h : -(𝟙 M) ≠ 𝟙 M) :
    -(𝟙 (F.obj M)) ≠ 𝟙 (F.obj M) := by
  intro he
  apply h
  apply F.map_injective
  rw [F.map_neg, F.map_id]
  exact he

private theorem neg_id_ne_of_iso {C : Type*} [Category C] [Preadditive C]
    {M N : C} (e : M ≅ N) (h : -(𝟙 M) ≠ 𝟙 M) : -(𝟙 N) ≠ 𝟙 N := by
  intro he
  apply h
  have h' := congrArg (fun q : N ⟶ N ↦ e.hom ≫ q ≫ e.inv) he
  simpa using h'

private theorem point_unit_neg_id_ne
    (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    -(𝟙 (𝟙_ (Mod (Sheaf (ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω)))))) ≠ 𝟙 _ := by
  intro h
  let S := ProEt.mk (𝟙 (Spec (.of Ω)))
  let e := (Mon.forget Ab.{u + 1}).mapIso
    (CondensedQbarGeometricEvaluation.fieldCoefficientIso Ω ℓ)
  have hs := congrArg (fun f ↦ f.hom.hom.app (op S)) h
  change -(𝟙 ((condensedRingObj (Profinite.padicAlgClRingObj ℓ)
    (Spec (.of Ω))).obj.obj (op S))) = 𝟙 _ at hs
  have hq : -(𝟙 (AddCommGrpCat.of (ULift.{u + 1} (PadicAlgCl ℓ)))) ≠ 𝟙 _ := by
    intro he
    have h11 := congrArg (fun f ↦ (f.hom (ULift.up 1)).down) he
    change (-1 : PadicAlgCl ℓ) = 1 at h11
    have h20 : (2 : PadicAlgCl ℓ) = 0 := by linear_combination -h11
    norm_num at h20
  exact (neg_id_ne_of_iso e.symm hq) hs

private theorem point_derived_unit_neg_id_ne
    (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    -(𝟙 (𝟙_ (DerivedCategory
      (Mod (Sheaf (ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω))))))) ≠ 𝟙 _ := by
  exact neg_id_ne_of_iso (DerivedCategory.singleFunctorObjUnitIso _)
    (neg_id_ne_of_faithful (DerivedCategory.singleFunctor _ 0) _
      (point_unit_neg_id_ne ℓ Ω))

private theorem point_bounded_unit_neg_id_ne
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Over (Spec (.of k))) (hX : X.left = Spec (.of k))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    -(𝟙 (𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) ≠ 𝟙 _ := by
  intro h
  have h' := congrArg (ObjectProperty.ι _).map h
  change -(𝟙 (𝟙_ (DerivedCategory (Mod (Sheaf (ProEt.topology X.left) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))))) = 𝟙 _ at h'
  rw [hX] at h'
  exact point_derived_unit_neg_id_ne ℓ k h'

attribute [local irreducible] AlgebraicGeometry.Spec

private theorem point_locallyOfFiniteType (k : Type u) [Field k] :
    LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))

private theorem point_quasiCompact (k : Type u) [Field k] :
    QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))

private theorem point_isSeparated (k : Type u) [Field k] :
    IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))

attribute [local instance] point_locallyOfFiniteType point_quasiCompact point_isSeparated

private theorem point_no_unique_representing_trace
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    let X := Over.mk (𝟙 (Spec (.of k)))
    ∀ F : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
    let U := 𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    ¬ ∃! t : F.obj U ⟶ U,
      ∀ K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
        Function.Bijective (fun a : K ⟶ U ↦ F.map a ≫ t) := by
  dsimp only
  intro F
  exact no_unique_representing_trace _ _ _ (-Iso.refl _)
    (point_bounded_unit_neg_id_ne ℓ k _ rfl)

private theorem point_zero_twist_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    let X := Over.mk (𝟙 (Spec (.of k)))
    Nonempty ((𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)).obj ≅
      (shiftFunctor _ (2 * ((0 : ℕ) : ℤ))).obj (tateTwistDerived X.left ℓ 0)) := by
  dsimp only
  exact ⟨(DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm⟩

private theorem point_smooth_zero (k : Type u) [Field k] :
    SmoothOfRelativeDimension 0 (𝟙 (Spec (.of k))) := by
  infer_instance

private theorem smoothTrace_point_claim_false
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    let X := Over.mk (𝟙 (Spec (.of k)))
    ∀ F : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
    ¬ ∀ (_hsm : SmoothOfRelativeDimension 0 (𝟙 X : X ⟶ X).left)
      (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
      (_hM : M.obj ≅ (shiftFunctor _ (2 * ((0 : ℕ) : ℤ))).obj
        (tateTwistDerived X.left ℓ 0))
      (U : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
      (_hU : U = 𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)),
      ∃! t : F.obj M ⟶ U,
        ∀ K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
          Function.Bijective (fun a : K ⟶ M ↦ F.map a ≫ t) := by
  dsimp only
  intro F h
  obtain ⟨hM⟩ := point_zero_twist_iso ℓ k
  exact point_no_unique_representing_trace ℓ k F
    (h (point_smooth_zero k) _ hM _ rfl)

private theorem normalized_trace_unique
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (M : C) (U : D)
    (E : ∀ K : C, (K ⟶ M) ≃ (F.obj K ⟶ U))
    (hE : ∀ (K L : C) (a : K ⟶ L) (b : L ⟶ M),
      E K (a ≫ b) = F.map a ≫ E L b) :
    ∃! t : F.obj M ⟶ U,
      ∀ (K : C) (a : K ⟶ M), F.map a ≫ t = E K a := by
  refine ⟨E M (𝟙 M), ?_, ?_⟩
  · intro K a
    simpa only [Category.comp_id] using (hE K M a (𝟙 M)).symm
  · intro t ht
    simpa only [F.map_id, Category.id_comp] using ht M (𝟙 M)

/-- A closed counterexample: ell = 2 and k = the algebraic closure of F_3.
All geometric hypotheses and the exact zero-Tate source identification are included
in the quantified assertion. The result holds for every candidate lower-shriek functor,
so its proof does not depend on the unfinished construction of that functor or on
existsUnique_smoothTrace. -/
private theorem smoothTrace_char_three_claim_false :
    have : Fact (Nat.Prime 2) := ⟨by decide⟩
    let k := AlgebraicClosure (ZMod 3)
    have : Fact (ringChar k).Prime := ⟨by rw [ringChar.eq k 3]; decide⟩
    have : Fact (ringChar k ≠ 2) := ⟨by rw [ringChar.eq k 3]; decide⟩
    let X := Over.mk (𝟙 (Spec (.of k)))
    ∀ F : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj 2⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicAlgClRingObj 2⟧,
    ¬ ∀ (_hsm : SmoothOfRelativeDimension 0 (𝟙 X : X ⟶ X).left)
      (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj 2⟧)
      (_hM : M.obj ≅ (shiftFunctor _ (2 * ((0 : ℕ) : ℤ))).obj
        (tateTwistDerived X.left 2 0))
      (U : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj 2⟧)
      (_hU : U = 𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj 2⟧)),
      ∃! t : F.obj M ⟶ U,
        ∀ K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj 2⟧,
          Function.Bijective (fun a : K ⟶ M ↦ F.map a ≫ t) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have : Fact (ringChar (AlgebraicClosure (ZMod 3))).Prime :=
    ⟨by rw [ringChar.eq (AlgebraicClosure (ZMod 3)) 3]; decide⟩
  have : Fact (ringChar (AlgebraicClosure (ZMod 3)) ≠ 2) :=
    ⟨by rw [ringChar.eq (AlgebraicClosure (ZMod 3)) 3]; decide⟩
  exact smoothTrace_point_claim_false 2 (AlgebraicClosure (ZMod 3))

end Counterexample

/-- STATEMENT-DISPUTED: Hom bijectivity does not normalize the representing trace.

The private theorem smoothTrace_char_three_claim_false above proves that this exact
claim is false for ell = 2, k = the algebraic closure of F_3, f = identity, d = 0,
and M = U = the coefficient unit. It supplies the required smoothness and the actual
zero-Tate/zero-shift identification, and uses no disputed smooth-purity theorem.

Precomposing any representing trace with the image of a source automorphism preserves
all Hom bijections. Uniqueness and injectivity at K = M would force that automorphism
to be the identity. Negation on the actual coefficient unit is nontrivial: the proved
geometric-field coefficient evaluation isomorphism would otherwise give -1 = 1 in Qbar_ell.
The faithful derived single functor carries the obstruction to the bounded constructible
derived unit.

The intended finite diagonal/deformation counits, adic reconstruction, and condensed
realization must instead specify a natural Hom equivalence. The proved private lemma
normalized_trace_unique shows precisely the corrected final step: its value on id_M
is the unique trace inducing that specified equivalence. Those normalization equations
are absent from the present predicate, so the advertised geometric plan cannot prove it.

Source: def-route-smooth-trace, Steps 1--4; the formal counterexample above diagnoses
its representing-uniqueness split.
(blueprint: lem-route-smooth-trace-representing-unique) -/
theorem existsUnique_smoothTrace
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (d : ℕ)
    (hsm : SmoothOfRelativeDimension d f.left)
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hM : M.obj ≅ (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d))
    (U : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hU : U = MonoidalCategoryStruct.tensorUnit (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :
    ∃! t :
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M ⟶ U,
      ∀ K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
        Function.Bijective (fun a : K ⟶ M ↦
          (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map a ≫ t) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
