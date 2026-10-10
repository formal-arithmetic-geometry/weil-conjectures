/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import WeilConjectures.CategoryTheory.RingObjects.Profinite.ContinuousMap
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.NumberTheory.Padics.Extension

/-!

# The condensed rings `ℤ_ℓ`, `ℚ_ℓ`, `𝒪_E`, `E` and `ℚ̄_ℓ`

Let `ℓ` be a prime. Following Section 6.8 of *Bhargav Bhatt and Peter Scholze, The pro-étale
topology for schemes*, the coefficient rings of `ℓ`-adic cohomology are sheaves of rings on the
pro-étale site of a point, i.e. on the category `Profinite` of profinite sets with the coherent
topology ("condensed rings"); their counterparts on the pro-étale site of a scheme `X` are
obtained by pullback along `X → Spec ℤ`, see
`WeilConjectures.CategoryTheory.RingObjects.Pullback`. This file constructs them as sheaves of
commutative rings on `Profinite`; their underlying abelian sheaves, through
`CategoryTheory.Sheaf.toAb`, are commutative ring objects of the category of abelian sheaves on
`Profinite`, with the monoidal structure given by the sheafification of the objectwise tensor
product.

* `ℤ_ℓ` and `ℚ_ℓ` are the sheaves of continuous maps `S ↦ C(S, ℤ_ℓ)` and `S ↦ C(S, ℚ_ℓ)` with the
  pointwise ring structure (`Profinite.padicIntSheaf`, `Profinite.padicSheaf`).
* For a subfield `E` of `ℚ̄_ℓ = PadicAlgCl ℓ`, given by an embedding `E → ℚ̄_ℓ` as in
  `WeilConjectures.NumberTheory.Padics.Extension`, `E` and `𝒪_E` are the sheaves of continuous
  maps `S ↦ C(S, E)` and `S ↦ C(S, 𝒪_E)`, for the topologies of `E` and of its ring of integers
  `𝒪_E` restricted from `ℚ̄_ℓ` (`Profinite.padicSubfieldSheaf`, `Profinite.padicIntegersSheaf`).
* `ℚ̄_ℓ` is **not** the sheaf of continuous maps into `ℚ̄_ℓ` with its valuation topology: the
  sections of the correct `ℚ̄_ℓ`-sheaf over an extremally disconnected `S` are the continuous
  maps `S → ℚ̄_ℓ` taking values in some *finite* subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, which is a
  strictly smaller ring than `C(S, ℚ̄_ℓ)` (a sequence of elements of unbounded degree converging
  to `0` in `ℚ̄_ℓ` extends to a continuous map on the Stone–Čech compactification of `ℕ`).
  Accordingly `ℚ̄_ℓ` is defined as the sheafification of the presheaf of rings
  `S ↦ {f ∈ C(S, ℚ̄_ℓ) | f takes values in a finite subextension}`
  (`PadicAlgCl.finiteExtensionValued`, `Profinite.padicAlgClSheaf`). This presheaf is the
  union of the presheaves `S ↦ C(S, E)` over the finite subextensions `E ⊆ ℚ̄_ℓ`, so that
  `ℚ̄_ℓ = colim_E E` as sheaves of rings, which is the `ℚ̄_ℓ`-sheaf of Bhatt–Scholze
  (`Profinite.isColimitPadicAlgClSheafCocone`, over the directed set
  `PadicAlgCl.FiniteExtension`).

All of these are sheaves of commutative rings, and the natural inclusions
`ℤ_ℓ ⟶ ℚ_ℓ ⟶ E ⟶ ℚ̄_ℓ`, `ℤ_ℓ ⟶ 𝒪_E ⟶ E` and `ℚ_ℓ ⟶ ℚ̄_ℓ` are morphisms of sheaves of rings.

## Main definitions

* `Profinite.padicIntSheaf`, `Profinite.padicSheaf`: the condensed rings `ℤ_ℓ` and `ℚ_ℓ`.
* `Profinite.padicSubfieldSheaf`, `Profinite.padicIntegersSheaf`: the condensed rings `E` and
  `𝒪_E` for `E ⊆ ℚ̄_ℓ`.
* `Profinite.padicAlgClSheaf`: the condensed ring `ℚ̄_ℓ`.
* `Profinite.padicIntSheafToPadicSheaf`, `Profinite.padicSheafToPadicSubfieldSheaf`,
  `Profinite.padicIntegersSheafToPadicSubfieldSheaf`,
  `Profinite.padicIntSheafToPadicIntegersSheaf`, `Profinite.padicSheafToPadicAlgClSheaf` and
  `Profinite.padicSubfieldSheafToPadicAlgClSheaf`: the inclusions.
* `Profinite.padicAlgClSheafCocone`: the cocone of the `E ⟶ ℚ̄_ℓ` over the finite subextensions
  `E`, and `Profinite.isColimitPadicAlgClSheafCocone`: it is a colimit, being the sheafification
  of the colimit `padicAlgClPresheafCocone` of presheaves.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type*) [TopologicalSpace U]

/-- The subring of `C(U, ℚ̄_ℓ)` of continuous maps whose values lie in some finite subextension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. Sums and products of such maps take values in the compositum of the two
subextensions, which is again finite. -/
def finiteExtensionValued : Subring C(U, PadicAlgCl ℓ) where
  carrier := {f | ∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
    FiniteDimensional ℚ_[ℓ] E ∧ ∀ x, f x ∈ E}
  mul_mem' := by
    rintro f g ⟨E, hE, hf⟩ ⟨F, hF, hg⟩
    refine ⟨E ⊔ F, by have := hE; have := hF; infer_instance, fun x ↦ ?_⟩
    rw [ContinuousMap.mul_apply]
    exact mul_mem (SetLike.le_def.mp le_sup_left (hf x)) (SetLike.le_def.mp le_sup_right (hg x))
  add_mem' := by
    rintro f g ⟨E, hE, hf⟩ ⟨F, hF, hg⟩
    refine ⟨E ⊔ F, by have := hE; have := hF; infer_instance, fun x ↦ ?_⟩
    rw [ContinuousMap.add_apply]
    exact add_mem (SetLike.le_def.mp le_sup_left (hf x)) (SetLike.le_def.mp le_sup_right (hg x))
  one_mem' := ⟨⊥, inferInstance, fun _ ↦ one_mem ⊥⟩
  zero_mem' := ⟨⊥, inferInstance, fun _ ↦ zero_mem ⊥⟩
  neg_mem' := by
    rintro f ⟨E, hE, hf⟩
    exact ⟨E, hE, fun x ↦ neg_mem (hf x)⟩

lemma mem_finiteExtensionValued_iff (f : C(U, PadicAlgCl ℓ)) :
    f ∈ finiteExtensionValued ℓ U ↔
      ∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ), FiniteDimensional ℚ_[ℓ] E ∧ ∀ x, f x ∈ E :=
  Iff.rfl

/-- The finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, ordered by inclusion. This is a directed
order, the compositum of two finite subextensions being finite. -/
abbrev FiniteExtension : Type :=
  {E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) // FiniteDimensional ℚ_[ℓ] E}

instance (E : FiniteExtension ℓ) : FiniteDimensional ℚ_[ℓ] E.1 := E.2

instance : Nonempty (FiniteExtension ℓ) := ⟨⟨⊥, inferInstance⟩⟩

instance : IsDirectedOrder (FiniteExtension ℓ) where
  directed E F := ⟨⟨E.1 ⊔ F.1, inferInstance⟩, le_sup_left (a := E.1), le_sup_right (a := E.1)⟩

end PadicAlgCl

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### `ℤ_ℓ` and `ℚ_ℓ` -/

/-- The condensed ring `ℤ_ℓ`: the sheaf of continuous maps `S ↦ C(S, ℤ_ℓ)` on profinite sets with
the pointwise ring structure [Bhatt–Scholze, Definition 6.8.1]. -/
noncomputable abbrev padicIntSheaf : Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} :=
  continuousMapRingSheaf ℤ_[ℓ]

/-- The condensed ring `ℚ_ℓ`: the sheaf of continuous maps `S ↦ C(S, ℚ_ℓ)` on profinite sets with
the pointwise ring structure [Bhatt–Scholze, Definition 6.8.1]. -/
noncomputable abbrev padicSheaf : Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} :=
  continuousMapRingSheaf ℚ_[ℓ]

/-- The inclusion `ℤ_ℓ ⟶ ℚ_ℓ`, a morphism of sheaves of rings. -/
noncomputable def padicIntSheafToPadicSheaf : padicIntSheaf.{u} ℓ ⟶ padicSheaf.{u} ℓ :=
  continuousMapRingSheafMap PadicInt.Coe.ringHom continuous_subtype_val

/-! ### Subfields `E` of `ℚ̄_ℓ` -/

section Subfield

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The condensed ring `E`, for a subfield `E` of `ℚ̄_ℓ` given by an embedding `E → ℚ̄_ℓ`: the
sheaf of continuous maps `S ↦ C(S, E)` with the pointwise ring structure, for the topology of `E`
restricted from `ℚ̄_ℓ` along the embedding (`PadicAlgCl.normedFieldOfAlgebra`). -/
noncomputable abbrev padicSubfieldSheaf :
    Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheaf E

/-- The embedding `E → ℚ̄_ℓ` is continuous for the topology of `E` restricted from `ℚ̄_ℓ`. -/
lemma continuous_algebraMap_padicAlgCl_of_algebra :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    Continuous (algebraMap E (PadicAlgCl ℓ)) :=
  continuous_induced_dom

variable [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-- The structure map `ℚ_ℓ → E` is continuous for the topology of `E` restricted from `ℚ̄_ℓ`:
composed with the embedding `E → ℚ̄_ℓ` it is the continuous structure map `ℚ_ℓ → ℚ̄_ℓ`. -/
lemma continuous_algebraMap_padic_of_algebra :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    Continuous (algebraMap ℚ_[ℓ] E) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  refine continuous_induced_rng.mpr ?_
  change Continuous ((algebraMap E (PadicAlgCl ℓ)) ∘ (algebraMap ℚ_[ℓ] E))
  rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
  exact continuous_algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)

/-- The inclusion `ℚ_ℓ ⟶ E`, a morphism of sheaves of rings. -/
noncomputable def padicSheafToPadicSubfieldSheaf : padicSheaf.{u} ℓ ⟶ padicSubfieldSheaf.{u} ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (algebraMap ℚ_[ℓ] E) (continuous_algebraMap_padic_of_algebra ℓ E)

end Subfield

/-! ### The rings of integers `𝒪_E` -/

section Integers

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The condensed ring `𝒪_E`, for a subfield `E` of `ℚ̄_ℓ` given by an embedding `E → ℚ̄_ℓ`: the
sheaf of continuous maps `S ↦ C(S, 𝒪_E)` with the pointwise ring structure into the ring of
integers `𝒪_E = PadicAlgCl.integers ℓ E` of `E`, for the topology of `𝒪_E` restricted from
`ℚ̄_ℓ` along the embedding. -/
noncomputable abbrev padicIntegersSheaf :
    Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheaf (PadicAlgCl.integers ℓ E)

/-- The inclusion `𝒪_E ⟶ E`, a morphism of sheaves of rings. -/
noncomputable def padicIntegersSheafToPadicSubfieldSheaf :
    padicIntegersSheaf.{u} ℓ E ⟶ padicSubfieldSheaf.{u} ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (PadicAlgCl.integers ℓ E).subtype continuous_subtype_val

variable [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-- The structure map `ℚ_ℓ → E` sends `ℤ_ℓ` into the ring of integers `𝒪_E`: the valuation of
`E` extends the `ℓ`-adic one. -/
lemma algebraMap_padicInt_mem_integers (x : ℤ_[ℓ]) :
    algebraMap ℚ_[ℓ] E x ∈ PadicAlgCl.integers ℓ E := by
  rw [PadicAlgCl.mem_integers_iff, ← IsScalarTower.algebraMap_apply]
  exact_mod_cast (PadicAlgCl.norm_extends ℓ (x : ℚ_[ℓ])).le.trans x.2

/-- The structure map `ℤ_ℓ → 𝒪_E`, the restriction of `ℚ_ℓ → E` to the rings of integers. -/
noncomputable def padicIntToIntegers : ℤ_[ℓ] →+* PadicAlgCl.integers ℓ E :=
  ((algebraMap ℚ_[ℓ] E).comp PadicInt.Coe.ringHom).codRestrict (PadicAlgCl.integers ℓ E)
    (algebraMap_padicInt_mem_integers ℓ E)

/-- The structure map `ℤ_ℓ → 𝒪_E` is continuous for the topology of `𝒪_E` restricted from
`ℚ̄_ℓ`. -/
lemma continuous_padicIntToIntegers :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    Continuous (padicIntToIntegers ℓ E) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  refine continuous_induced_rng.mpr ?_
  exact (continuous_algebraMap_padic_of_algebra ℓ E).comp continuous_subtype_val

/-- The inclusion `ℤ_ℓ ⟶ 𝒪_E`, a morphism of sheaves of rings. -/
noncomputable def padicIntSheafToPadicIntegersSheaf :
    padicIntSheaf.{u} ℓ ⟶ padicIntegersSheaf.{u} ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (padicIntToIntegers ℓ E) (continuous_padicIntToIntegers ℓ E)

end Integers

/-! ### `ℚ̄_ℓ` -/

/-- The presheaf of commutative rings `S ↦ {f ∈ C(S, ℚ̄_ℓ) | f takes values in a finite
subextension}` on profinite sets, the union over the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` of
the presheaves `S ↦ C(S, E)`. Its sheafification is the condensed ring `ℚ̄_ℓ`. -/
noncomputable def padicAlgClRingPresheaf : Profinite.{u}ᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj S := CommRingCat.of (ULift.{u + 1} (PadicAlgCl.finiteExtensionValued ℓ S.unop))
  map f := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((((ContinuousMap.compRightAlgHom ℤ (PadicAlgCl ℓ) f.unop.hom.hom).toRingHom).comp
          (PadicAlgCl.finiteExtensionValued ℓ _).subtype).codRestrict
          (PadicAlgCl.finiteExtensionValued ℓ _) (fun g ↦ by
            obtain ⟨E, hE, hg⟩ := g.2
            exact ⟨E, hE, fun x ↦ hg _⟩)).comp ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

lemma padicAlgClRingPresheaf_map_apply {S S' : Profinite.{u}ᵒᵖ} (f : S ⟶ S')
    (g : ULift.{u + 1} (PadicAlgCl.finiteExtensionValued ℓ S.unop)) :
    ((padicAlgClRingPresheaf ℓ).map f g).down.1 = g.down.1.comp f.unop.hom.hom :=
  rfl

/-- The condensed ring `ℚ̄_ℓ`: the sheafification of the presheaf of rings
`S ↦ {f ∈ C(S, ℚ̄_ℓ) | f takes values in a finite subextension of ℚ_ℓ}`, which is the union of
the presheaves `S ↦ C(S, E)` over the finite subextensions `E ⊆ ℚ̄_ℓ`. This is the `ℚ̄_ℓ`-sheaf of
[Bhatt–Scholze, Section 6.8], `colim_E E`; it differs from the sheaf of continuous maps into
`ℚ̄_ℓ` with its valuation topology. -/
noncomputable abbrev padicAlgClSheaf : Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} :=
  (presheafToSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
    (padicAlgClRingPresheaf ℓ)

section ToPadicAlgCl

variable {T : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  (ψ : T →+* PadicAlgCl ℓ) (hψ : Continuous ψ)
  (hE : ∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ), FiniteDimensional ℚ_[ℓ] E ∧ ∀ t, ψ t ∈ E)

/-- Postcomposition with a continuous ring homomorphism `ψ : T → ℚ̄_ℓ` whose image lies in a
finite subextension of `ℚ_ℓ`, as a morphism of presheaves of rings from `S ↦ C(S, T)` to the
presheaf of continuous maps into `ℚ̄_ℓ` with values in a finite subextension. -/
noncomputable def continuousMapRingPresheafToPadicAlgCl :
    continuousMapRingPresheaf.{u} T ⟶ padicAlgClRingPresheaf ℓ where
  app _ := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ψ.compLeftContinuous _ hψ).codRestrict (PadicAlgCl.finiteExtensionValued ℓ _)
          (fun g ↦ by
            obtain ⟨E, hE, h⟩ := hE
            exact ⟨E, hE, fun x ↦ h (g x)⟩)).comp ULift.ringEquiv.toRingHom))
  naturality _ _ _ := rfl

/-- The morphism of sheaves of rings `C(-, T) ⟶ ℚ̄_ℓ` induced by a continuous ring homomorphism
`ψ : T → ℚ̄_ℓ` whose image lies in a finite subextension of `ℚ_ℓ`. -/
noncomputable def continuousMapRingSheafToPadicAlgClSheaf :
    continuousMapRingSheaf.{u} T ⟶ padicAlgClSheaf ℓ :=
  Sheaf.homToSheafify (continuousMapRingPresheafToPadicAlgCl ℓ ψ hψ hE)

end ToPadicAlgCl

/-- The inclusion `ℚ_ℓ ⟶ ℚ̄_ℓ`, a morphism of sheaves of rings. -/
noncomputable def padicSheafToPadicAlgClSheaf : padicSheaf.{u} ℓ ⟶ padicAlgClSheaf ℓ :=
  continuousMapRingSheafToPadicAlgClSheaf ℓ (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ))
    (continuous_algebraMap ℚ_[ℓ] (PadicAlgCl ℓ))
    ⟨⊥, inferInstance, fun t ↦ IntermediateField.algebraMap_mem ⊥ t⟩

section SubfieldToPadicAlgCl

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The image of a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` is a finite subextension. -/
lemma finiteDimensional_fieldRange_toAlgHom :
    FiniteDimensional ℚ_[ℓ] (IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ)).fieldRange := by
  have h : FiniteDimensional ℚ_[ℓ] (IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ)).range :=
    (AlgEquiv.ofInjectiveField
      (IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ))).toLinearEquiv.finiteDimensional
  rw [← AlgHom.fieldRange_toSubalgebra] at h
  exact h

/-- The inclusion `E ⟶ ℚ̄_ℓ` for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, a morphism of sheaves
of rings. -/
noncomputable def padicSubfieldSheafToPadicAlgClSheaf :
    padicSubfieldSheaf.{u} ℓ E ⟶ padicAlgClSheaf ℓ :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafToPadicAlgClSheaf ℓ (algebraMap E (PadicAlgCl ℓ))
    (continuous_algebraMap_padicAlgCl_of_algebra ℓ E)
    ⟨_, finiteDimensional_fieldRange_toAlgHom ℓ E, fun t ↦ ⟨t, rfl⟩⟩

end SubfieldToPadicAlgCl

/-! ### `ℚ̄_ℓ` as the colimit of the `E` -/

/-- The inclusion `E ⟶ F` for subextensions `E ⊆ F ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, a morphism of sheaves of
rings. -/
noncomputable def padicSubfieldSheafMapOfLE {E F : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)}
    (h : E ≤ F) : padicSubfieldSheaf.{u} ℓ E ⟶ padicSubfieldSheaf.{u} ℓ F :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ F
  continuousMapRingSheafMap (IntermediateField.inclusion h).toRingHom
    (continuous_induced_rng.mpr continuous_induced_dom)

/-- The diagram `E ↦ E` of condensed rings, indexed by the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
ordered by inclusion. -/
noncomputable def padicSubfieldSheafFunctor :
    PadicAlgCl.FiniteExtension ℓ ⥤
      Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} where
  obj E := padicSubfieldSheaf ℓ E.1
  map f := padicSubfieldSheafMapOfLE ℓ (leOfHom f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The cocone of presheaves of rings over the diagram `E ↦ C(-, E)` with vertex the presheaf
`S ↦ {f ∈ C(S, ℚ̄_ℓ) | f takes values in a finite subextension}`, whose sheafification is
`padicAlgClSheafCocone`. -/
noncomputable def padicAlgClPresheafCocone :
    Cocone (padicSubfieldSheafFunctor.{u} ℓ ⋙ sheafToPresheaf _ _) :=
  Cocone.mk (padicAlgClRingPresheaf ℓ)
    { app E := letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
        continuousMapRingPresheafToPadicAlgCl ℓ (algebraMap E.1 (PadicAlgCl ℓ))
          (continuous_algebraMap_padicAlgCl_of_algebra ℓ E.1)
          ⟨_, finiteDimensional_fieldRange_toAlgHom ℓ E.1, fun t ↦ ⟨t, rfl⟩⟩
      naturality _ _ _ := rfl }

/-- The cocone of condensed rings over the diagram `E ↦ E` with vertex `ℚ̄_ℓ`, given by the
inclusions `E ⟶ ℚ̄_ℓ`. -/
noncomputable def padicAlgClSheafCocone : Cocone (padicSubfieldSheafFunctor.{u} ℓ) :=
  Cocone.mk (padicAlgClSheaf ℓ)
    { app E := padicSubfieldSheafToPadicAlgClSheaf ℓ E.1
      naturality _ _ f := by
        refine Eq.trans ?_ (Category.comp_id _).symm
        exact (Sheaf.comp_homToSheafify ((padicSubfieldSheafFunctor ℓ).map f) _).trans
          (congrArg Sheaf.homToSheafify ((padicAlgClPresheafCocone ℓ).ι.naturality f).symm) }

/-- The presheaf `S ↦ {f ∈ C(S, ℚ̄_ℓ) | f takes values in a finite subextension}` is the
colimit of the presheaves `S ↦ C(S, E)`: objectwise, it is the filtered union of the injective
maps `C(S, E) → C(S, ℚ̄_ℓ)`. -/
noncomputable def isColimitPadicAlgClPresheafCocone :
    IsColimit (padicAlgClPresheafCocone.{u} ℓ) := by
  haveI := preservesSmallestFilteredColimits_of_preservesFilteredColimits
    (forget CommRingCat.{u + 1})
  haveI : ReflectsColimitsOfShape (PadicAlgCl.FiniteExtension ℓ)
      (forget CommRingCat.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine evaluationJointlyReflectsColimits _ fun S ↦
    isColimitOfReflects (forget CommRingCat.{u + 1}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨⟨f, E, hE, hf⟩⟩ := x
    let := PadicAlgCl.normedFieldOfAlgebra ℓ E
    refine ⟨⟨E, hE⟩, ULift.up (⟨fun x ↦ ⟨f x, hf x⟩, continuous_induced_rng.mpr f.2⟩ :
      C(S.unop, E)), ?_⟩
    rfl
  · intro E x y h
    refine ⟨E, 𝟙 E, ?_⟩
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    have h' : ∀ t, (x t : PadicAlgCl ℓ) = y t := fun t ↦
      congrArg (fun z : ULift.{u + 1} (PadicAlgCl.finiteExtensionValued ℓ S.unop) ↦
        (z.down : C(S.unop, PadicAlgCl ℓ)) t) h
    have : x = y := ContinuousMap.ext fun t ↦ Subtype.val_injective (h' t)
    subst this
    rfl

/-- `ℚ̄_ℓ` is the colimit of the condensed rings `E = C(-, E)` over the finite subextensions
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` [Bhatt–Scholze, Section 6.8]: it is the sheafification of the colimit
`padicAlgClPresheafCocone` of the underlying presheaves, sheafification being a left adjoint. -/
noncomputable def isColimitPadicAlgClSheafCocone : IsColimit (padicAlgClSheafCocone.{u} ℓ) := by
  let α : (padicSubfieldSheafFunctor.{u} ℓ ⋙ sheafToPresheaf _ _) ⋙
      presheafToSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} ≅
        padicSubfieldSheafFunctor.{u} ℓ :=
    NatIso.ofComponents (fun E ↦ Sheaf.sheafifyObjIso _ _) fun f ↦
      (sheafificationAdjunction _ _).counit.naturality _
  refine (IsColimit.precomposeHomEquiv α _).1 ?_
  refine IsColimit.ofIsoColimit (isColimitOfPreserves (presheafToSheaf _ CommRingCat.{u + 1})
    (isColimitPadicAlgClPresheafCocone ℓ)) (Cocone.ext (Iso.refl _) fun E ↦ ?_)
  simp only [Functor.mapCocone_ι_app, Iso.refl_hom, Category.comp_id, Cocone.precompose_obj_ι,
    NatTrans.comp_app]
  exact Sheaf.presheafToSheaf_map_eq_sheafifyObjIso_hom_comp _

end Profinite
