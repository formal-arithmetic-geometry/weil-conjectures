/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import WeilConjectures.AlgebraicGeometry.GeometricFiberFiniteEtale
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.WeilSheaf.FiniteEtale
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.VerdierDualLocalization

/-!
# The Verdier dual on a finite reduced scheme

Weil complexes carry the canonical t-structure of the derived category of pro-étale Weil
sheaves (`AlgebraicGeometry.WeilComplex.tStructure`), Weil complexes being stable under the
truncations.

On a finite reduced `k₀`-scheme `Z` (finite étale over `k₀`), every Weil sheaf is lisse, and
`Z` is smooth of dimension zero, so that the Verdier dual of a Weil sheaf placed in degree zero
is again a Weil sheaf placed in degree zero (`𝔻_Z G ≅ G^∨`). By dévissage the Verdier dual
`𝔻_Z` is t-exact: it carries complexes concentrated in degrees `[a, b]` to complexes
concentrated in degrees `[-b, -a]`. In particular `𝓗⁻¹(𝔻_Z A) ≅ (𝓗¹ A)^∨` for every Weil
complex `A` on `Z`, which is step 5 of the local boundary duality
(`lem-a1-local-boundary-duality`).

## Main statements

- `AlgebraicGeometry.WeilComplex.isGE_isLE_verdierDual_of_isFinite`: `𝔻_Z` is t-exact.
- `AlgebraicGeometry.WeilComplex.nonempty_homologySheaf_neg_one_verdierDual_iso`:
  `𝓗⁻¹(𝔻_Z A) ≅ (𝓗¹ A)^∨ ⊗ ℚ̄_ℓ(0) ⊗ ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated Triangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- A finite reduced scheme over a perfect field is étale over it: it is the spectrum of a
finite reduced, hence étale, algebra (`Algebra.Etale.of_isReduced_of_perfectField`). -/
theorem etale_of_isFinite_of_isReduced {K : Type u} [Field K] [PerfectField K] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of K)) [IsFinite f] [IsReduced Z] : Etale f := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  let φ₀ : CommRingCat.of K ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop
  let : Algebra K Γ(Z, ⊤) := φ₀.hom.toAlgebra
  have : Module.Finite K Γ(Z, ⊤) :=
    RingHom.Finite.comp f.finite_appTop (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  have := Algebra.Etale.of_isReduced_of_perfectField K Γ(Z, ⊤)
  have hf : f = Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(Z, ⊤))) := by
    rw [← Iso.inv_comp_eq, ← Category.comp_id f, ← toSpecΓ_SpecMap_ΓSpecIso_inv,
      Scheme.toSpecΓ_naturality_assoc, Scheme.isoSpec_inv_toSpecΓ_assoc, ← Spec.map_comp]
    rfl
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap K Γ(Z, ⊤)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  rw [hf]
  infer_instance

namespace WeilComplex

section TStructure

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- Weil complexes are stable under the truncations of the canonical t-structure of the derived
category of pro-étale Weil sheaves: the truncations of a bounded complex are bounded, and their
cohomology objects are those of the complex or zero. -/
instance : (objectProperty k₀ l X).HasInducedTStructure _root_.DerivedCategory.TStructure.t :=
  .mk' fun K hK n ↦ by
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
    exact ⟨⟨⟨⟨a, inferInstance⟩, ⟨n, inferInstance⟩⟩,
        _root_.DerivedCategory.homologyProperty_truncLE hc n⟩,
      ⟨⟨⟨n, inferInstance⟩, ⟨b, inferInstance⟩⟩,
        _root_.DerivedCategory.homologyProperty_truncGE hc n⟩⟩

variable (k₀ l X) in
/-- The canonical t-structure on Weil complexes, induced by the canonical t-structure of the
derived category of pro-étale Weil sheaves. -/
noncomputable def tStructure : TStructure (WeilComplex k₀ l X) :=
  (objectProperty k₀ l X).tStructure _root_.DerivedCategory.TStructure.t

lemma tStructure_isLE_iff (K : WeilComplex k₀ l X) (n : ℤ) :
    (tStructure k₀ l X).IsLE K n ↔ K.obj.IsLE n :=
  ObjectProperty.tStructure_isLE_iff _ _ K n

lemma tStructure_isGE_iff (K : WeilComplex k₀ l X) (n : ℤ) :
    (tStructure k₀ l X).IsGE K n ↔ K.obj.IsGE n :=
  ObjectProperty.tStructure_isGE_iff _ _ K n

instance (G : WeilSheaf k₀ l X) : (tStructure k₀ l X).IsLE (WeilSheaf.toComplex.obj G) 0 :=
  (tStructure_isLE_iff _ _).2
    (inferInstanceAs (((_root_.DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀ l X) 0).obj
      G.obj).IsLE 0))

instance (G : WeilSheaf k₀ l X) : (tStructure k₀ l X).IsGE (WeilSheaf.toComplex.obj G) 0 :=
  (tStructure_isGE_iff _ _).2
    (inferInstanceAs (((_root_.DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀ l X) 0).obj
      G.obj).IsGE 0))

/-- A Weil complex concentrated in degree `b` is its cohomology sheaf `𝓗ᵇ` placed in
degree `b`. -/
theorem nonempty_iso_shift_toComplex_homologySheaf (K : WeilComplex k₀ l X) (b : ℤ)
    [(tStructure k₀ l X).IsGE K b] [(tStructure k₀ l X).IsLE K b] :
    Nonempty (K ≅ (WeilSheaf.toComplex.obj ((homologySheaf b).obj K))⟦-b⟧) := by
  have : K.obj.IsGE b := (tStructure_isGE_iff _ _).1 inferInstance
  have : K.obj.IsLE b := (tStructure_isLE_iff _ _).1 inferInstance
  obtain ⟨A, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K.obj b
  let eA : A ≅ ((homologySheaf b).obj K).obj :=
    ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ b).app A).symm ≪≫
      (_root_.DerivedCategory.homologyFunctor _ b).mapIso e.symm
  exact ⟨ObjectProperty.isoMk _ (e ≪≫ (_root_.DerivedCategory.singleFunctor _ b).mapIso eA ≪≫
    ((_root_.DerivedCategory.singleFunctors _).shiftIso (-b) b 0 (by lia)).symm.app _ ≪≫
    (((objectProperty k₀ l X).ι.commShiftIso (-b)).app
      (WeilSheaf.toComplex.obj ((homologySheaf b).obj K))).symm)⟩

end TStructure

section Finite

variable {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsFinite (Z ↘ Spec (CommRingCat.of k₀))] [IsReduced Z]

open Pretriangulated.Opposite

/-- On a finite reduced `k₀`-scheme `Z`, the Verdier dual of a Weil sheaf `G` placed in degree
zero is the Weil sheaf `G^∨ ⊗ ℚ̄_ℓ(0) ⊗ ℚ̄_ℓ` placed in degree zero: `G` is lisse and `Z` is étale,
that is smooth of relative dimension zero, over `k₀`. -/
theorem nonempty_verdierDual_toComplex_iso_of_isFinite (G : WeilSheaf k₀ l Z) :
    Nonempty ((verdierDual k₀ l Z).obj (op (WeilSheaf.toComplex.obj G)) ≅
      WeilSheaf.toComplex.obj ((G.dual (WeilSheaf.isLisse_of_isFinite_of_isReduced G)).tensorObj
        ((WeilSheaf.tateTwistSheaf k₀ l Z 0).tensorObj (WeilSheaf.adicConstant k₀ l Z)
          (WeilSheaf.isLisse_tateTwistSheaf k₀ l Z 0))
        (WeilSheaf.isLisse_of_isFinite_of_isReduced G).dual)) := by
  have : Etale (Z ↘ Spec (CommRingCat.of k₀)) :=
    etale_of_isFinite_of_isReduced (Z ↘ Spec (CommRingCat.of k₀))
  obtain ⟨e⟩ := nonempty_verdierDual_toComplex_iso_of_isLisse 0 G
    (WeilSheaf.isLisse_of_isFinite_of_isReduced G)
  exact ⟨e ≪≫ (shiftFunctorZero' _ (2 * (0 : ℕ) : ℤ) (by simp)).app _⟩

theorem isLE_verdierDual_toComplex (G : WeilSheaf k₀ l Z) :
    (tStructure k₀ l Z).IsLE ((verdierDual k₀ l Z).obj (op (WeilSheaf.toComplex.obj G))) 0 :=
  (tStructure k₀ l Z).isLE_of_iso (nonempty_verdierDual_toComplex_iso_of_isFinite G).some.symm 0

theorem isGE_verdierDual_toComplex (G : WeilSheaf k₀ l Z) :
    (tStructure k₀ l Z).IsGE ((verdierDual k₀ l Z).obj (op (WeilSheaf.toComplex.obj G))) 0 :=
  (tStructure k₀ l Z).isGE_of_iso (nonempty_verdierDual_toComplex_iso_of_isFinite G).some.symm 0

end Finite

end WeilComplex

end AlgebraicGeometry
