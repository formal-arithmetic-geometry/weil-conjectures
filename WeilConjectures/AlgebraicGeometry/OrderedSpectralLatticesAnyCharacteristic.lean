/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NoetherianStratifiedLattice
import all WeilConjectures.AlgebraicGeometry.Ordered.OrderedSpectralLattices

/-! # Ordered spectral lattices over fields of arbitrary characteristic

Source: latest blueprint, `det-lem-integral-models-generators`, proof (1),
stratified lattice inclusions and ordering by open prefixes.
(blueprint: lem-sfb-ordered-spectral-lattices).

This adds the characteristic-zero-inclusive statement and preserves the existing
positive-characteristic theorem and its complete proof in `OrderedSpectralLattices`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.upperStar Mod.extendRestrictAdjunction
  Mod.comap Padic.coefficientExtensionIntegers

/-- Package the Noetherian-space lattice theorem in the existing raw coefficient API.
Source: `sk-lem-stratified-lattice`; the two predicates have the same lattice data.
The proof applies the stated theorem directly, unfolding only the raw predicate.
(blueprint: lem-sfb-ordered-spectral-lattices). -/
private theorem small_spectral_raw_lattices_of_noetherianSpace
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type) [Field K] [Algebra ℚ_[ℓ] K]
    [FiniteDimensional ℚ_[ℓ] K] (S : Scheme.{u}) [TopologicalSpace.NoetherianSpace S] :
    letI := spectralNorm.nontriviallyNormedField ℚ_[ℓ] K
    let A₀ := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers ℓ K)
    let B₀ := Profinite.continuousMapRingObj.{u} K
    let a₀ : A₀ ⟶ B₀ := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers ℓ K).subtype continuous_subtype_val)
    RawStratifiedLattices A₀ B₀ a₀ S :=
  CondensedRing.exists_stratified_lisse_integral_lattice_of_noetherianSpace ℓ K S

/-- A lisse spectral-coefficient module has integral lattice inclusions on a finite
scheme stratification with open prefixes, over any field of characteristic different
from the coefficient prime, including characteristic zero.

Source: latest blueprint, `det-lem-integral-models-generators`, proof (1),
first lattice-and-ordering step (blueprint: lem-sfb-ordered-spectral-lattices).

Proof. Choose a finite basis to realize E as a small Q_l-algebra. Transport the spectral
norm, valuation ring, continuous-function rings and their inclusion along that algebra
isomorphism. The induced module equivalences preserve finite free charts, monomorphisms
and the extension/restriction adjunction. Apply the Noetherian stratified-lattice theorem
to the small model and transport its inclusions and scalar-extension adjoints back to E;
use the finite-free transport helpers to identify raw local freeness with lisseness.
The spectrum of any field is Noetherian, so S is Noetherian by finite type. Apply ordered
common refinement. Realize each refined piece by its fibre product with the original
scheme stratum containing its image, giving an actual refinement morphism even for
nonreduced strata. Pull the lattice inclusion back along this morphism. Exact coefficient
inverse image preserves monicity, and finite free charts pull back. The scalar/pullback
comparison, with its ordinary scalar-unit normalization, identifies the adjoint of this
very inclusion with the pullback of the old adjoint, hence makes it invertible. Pullback
composition identifies its target with L restricted to the refined stratum. The image
partition retains covering, disjointness, local closedness and open prefixes. Empty S
allows zero strata; empty strata and rank zero require no positive-rank assumption.
No step requires positive characteristic. -/
theorem exists_orderedSpectralLattices_of_char_ne (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (k : Type u) [Field k] (_hchar : ringChar k ≠ ℓ)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] :
  letI := spectralNorm.nontriviallyNormedField ℚ_[ℓ] E
  let A := coefficientHeartRingObj (Profinite.continuousMapRingSheafOfUniverse.{u, u}
    (Padic.coefficientExtensionIntegers ℓ E))
  letI : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers ℓ E))
      (fun U (a b : ULift.{u + 1} C(U.unop, Padic.coefficientExtensionIntegers ℓ E)) ↦
        mul_comm a b)
  let B := coefficientHeartRingObj (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
  letI : IsCommMonObj B := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
      (fun U (a b : ULift.{u + 1} C(U.unop, E)) ↦ mul_comm a b)
  let c := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val)
  ∀ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj B S),
    IsLisseCoefficientModule B L →
    ∃ R : S.FiniteLocallyClosedStratification,
      (∀ b : Fin (R.n + 1),
        IsOpen (⋃ i : Fin R.n, ⋃ (_ : i.val < b.val), R.stratum i)) ∧
      ∃ M : ∀ b : Fin R.n,
        Mod (Sheaf (Scheme.ProEt.topology (R.domain b)) Ab.{u + 1})
          (condensedRingObj A (R.domain b)),
        ∀ b : Fin R.n, IsLisseCoefficientModule A (M b) ∧
          ∃ ι : M b ⟶ (Mod.comap ((upperStarFromPoint (R.domain b)).map c)).obj
              ((CondensedRing.upperStar B (R.immersion b)).obj L),
            Mono ι ∧ IsIso
              (((Mod.extendRestrictAdjunction ((upperStarFromPoint (R.domain b)).map c)).homEquiv
                (M b) ((CondensedRing.upperStar B (R.immersion b)).obj L)).symm ι) := by
  classical
  let fE : Field E := inferInstance
  let aE : Algebra ℚ_[ℓ] E := inferInstance
  let := spectralNorm.nontriviallyNormedField ℚ_[ℓ] E
  let : Field E := fE
  let : Algebra ℚ_[ℓ] E := aE
  intro A B c
  let : IsMonHom c := Sheaf.isMonHom_sheafCompose_map _
    (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val)
  let : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers ℓ E))
    (fun U (a b : ULift.{u + 1} C(U.unop, Padic.coefficientExtensionIntegers ℓ E)) ↦
      mul_comm a b)
  let : IsCommMonObj B := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
    (fun U (a b : ULift.{u + 1} C(U.unop, E)) ↦ mul_comm a b)
  let OA := Profinite.continuousMapRingSheafOfUniverse.{u, u}
    (Padic.coefficientExtensionIntegers ℓ E)
  let model := smallAlgebraModel ℓ E
  let K := model.carrier
  let : Field K := model.field
  let : Algebra ℚ_[ℓ] K := model.algebra
  let : FiniteDimensional ℚ_[ℓ] K := model.finite
  let e : K ≃ₐ[ℚ_[ℓ]] E := model.equiv
  let fK : Field K := inferInstance
  let aK : Algebra ℚ_[ℓ] K := inferInstance
  let := spectralNorm.nontriviallyNormedField ℚ_[ℓ] K
  let : Field K := fK
  let : Algebra ℚ_[ℓ] K := aK
  let square := spectralCoefficientSquare ℓ e
  let rRing := square.integral
  let sRing := square.rational
  let H := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let A₀ := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers ℓ K)
  let B₀ := Profinite.continuousMapRingObj.{u} K
  let a₀ : A₀ ⟶ B₀ := H.map
    (Profinite.continuousMapRingSheafMap
      (Padic.coefficientExtensionIntegers ℓ K).subtype continuous_subtype_val)
  let : IsMonHom a₀ := Sheaf.isMonHom_sheafCompose_map _
    (Profinite.continuousMapRingSheafMap
      (Padic.coefficientExtensionIntegers ℓ K).subtype continuous_subtype_val)
  let r : A₀ ≅ A := H.mapIso rRing
  let s : B₀ ≅ B := H.mapIso sRing
  have : IsMonHom r.hom := Sheaf.isMonHom_sheafCompose_map _ rRing.hom
  have : IsMonHom s.hom := Sheaf.isMonHom_sheafCompose_map _ sRing.hom
  have w : a₀ ≫ s.hom = r.hom ≫ c := by
    change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg H.map square.commutes
  have : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of k))
  have : CompactSpace S :=
    QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  have : IsNoetherian S := ⟨⟩
  have h : OrderedLatticeProperty A B c S :=
    ordered_lattices_of_coefficient_square OA A₀ B₀ B a₀ c r s w S
      (small_spectral_raw_lattices_of_noetherianSpace ℓ K S)
  exact ordered_lattice_unpack A B c S h

end AlgebraicGeometry.ProEtale
