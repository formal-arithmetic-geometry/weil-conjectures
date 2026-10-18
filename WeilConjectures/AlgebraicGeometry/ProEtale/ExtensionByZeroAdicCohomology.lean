/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicCohomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono

/-!
# Integral `ℓ`-adic cohomology of an extension by zero

Let `j : U ⟶ T` be an open immersion of schemes and `p` a prime (in practice `ℓ`). This file
develops, for the pro-étale cohomology of the extensions by zero
`Hⁿ(T, j_! ℤ_p) = Hⁿ(T_proét, j_! C(-, ℤ_p))`
(`AlgebraicGeometry.ProEtale.CompactIntegralAdicH`) and
`Hⁿ(T, j_! ℤ/pᵐ) = Hⁿ(T_proét, j_! C(-, ℤ_p / pᵐ))`
(`AlgebraicGeometry.ProEtale.CompactFiniteAdicH`), the lattice theory that
`WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicCohomology` develops for the constant
sheaves. When `T` is proper over an algebraically closed field these are the compactly
supported cohomology groups of `U`; the results feed the `ℚ̄_ℓ` stage of the compactly
supported case of blueprint `thm-pod-degreewise-perfectness-over-a-field`.

* the **Bockstein sequence**: the extension by zero `j_!` is exact, so it maps the Bockstein
  sequence `0 ⟶ ℤ_p --pᵐ--> ℤ_p ⟶ ℤ/pᵐ ⟶ 0` to a short exact sequence, whence
  `AlgebraicGeometry.ProEtale.exists_eq_pow_smul_of_compactReduction_eq_zero` and
  `AlgebraicGeometry.ProEtale.pow_smul_mem_range_compactReduction`;
* **separation** and **finite generation**
  (`AlgebraicGeometry.ProEtale.eq_zero_of_forall_compactReduction_eq_zero`,
  `AlgebraicGeometry.ProEtale.module_finite_compactIntegralAdicH`), from the fact that
  `j_! C(-, ℤ_p)` is the limit of the tower `j_! C(-, ℤ/pᵐ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian PadicInt

namespace PrimeSpectrum

section Compatible

local instance : PreservesFilteredColimitsOfSize.{0, 0} (forget CommRingCat.{u}) :=
  preservesFilteredColimitsOfSize_of_univLE.{u, u} (forget CommRingCat.{u})

variable (G : ℕ ⥤ CommRingCat.{u}) (q : ∀ n, PrimeSpectrum (G.obj n))
  (hq : ∀ n, comap (G.map (homOfLE n.le_succ)).hom (q (n + 1)) = q n)

include hq in
lemma comap_eq_of_compatible {m n : ℕ} (h : m ≤ n) :
    comap (G.map (homOfLE h)).hom (q n) = q m := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have : homOfLE (hmn.trans n.le_succ) = homOfLE hmn ≫ homOfLE n.le_succ := rfl
    rw [this, Functor.map_comp, CommRingCat.hom_comp, comap_comp_apply, hq, ih]

include hq in
lemma map_mem_iff_of_compatible {m n : ℕ} (h : m ≤ n) (y : G.obj m) :
    G.map (homOfLE h) y ∈ (q n).asIdeal ↔ y ∈ (q m).asIdeal := by
  rw [← comap_eq_of_compatible G q hq h]
  rfl

include hq in
lemma mem_iff_of_colimit_ι_eq {m n : ℕ} (y : G.obj m) (z : G.obj n)
    (h : colimit.ι G m y = colimit.ι G n z) : y ∈ (q m).asIdeal ↔ z ∈ (q n).asIdeal := by
  obtain ⟨k, f, g, hk⟩ := (Concrete.colimit_rep_eq_iff_exists G y z).1 h
  rw [← map_mem_iff_of_compatible G q hq (leOfHom f) y,
    ← map_mem_iff_of_compatible G q hq (leOfHom g) z]
  exact Iff.of_eq (congrArg (· ∈ (q k).asIdeal) hk)

/-- The ideal of `colim G` of the elements represented by an element of some `qₙ`, for a
compatible sequence of primes `qₙ` of the `G n`. -/
noncomputable def colimitIdealOfCompatible : Ideal (colimit G : CommRingCat) where
  carrier := {x | ∃ n y, colimit.ι G n y = x ∧ y ∈ (q n).asIdeal}
  add_mem' := by
    rintro _ _ ⟨m, y, rfl, hy⟩ ⟨n, z, rfl, hz⟩
    refine ⟨max m n, G.map (homOfLE (le_max_left m n)) y + G.map (homOfLE (le_max_right m n)) z,
      ?_, add_mem ((map_mem_iff_of_compatible G q hq _ y).2 hy)
        ((map_mem_iff_of_compatible G q hq _ z).2 hz)⟩
    rw [map_add, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, colimit.w, colimit.w]
  zero_mem' := ⟨0, 0, map_zero _, zero_mem _⟩
  smul_mem' := by
    rintro c _ ⟨n, z, rfl, hz⟩
    obtain ⟨m, y, rfl⟩ := Concrete.colimit_exists_rep G c
    refine ⟨max m n, G.map (homOfLE (le_max_left m n)) y * G.map (homOfLE (le_max_right m n)) z,
      ?_, Ideal.mul_mem_left _ _ ((map_mem_iff_of_compatible G q hq _ z).2 hz)⟩
    rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, colimit.w, colimit.w,
      smul_eq_mul]

include hq in
lemma ι_mem_colimitIdealOfCompatible_iff (n : ℕ) (y : G.obj n) :
    colimit.ι G n y ∈ colimitIdealOfCompatible G q hq ↔ y ∈ (q n).asIdeal :=
  ⟨fun ⟨_, z, hz, hz'⟩ ↦ (mem_iff_of_colimit_ι_eq G q hq z y hz).1 hz', fun h ↦ ⟨n, y, rfl, h⟩⟩

include hq in
lemma isPrime_colimitIdealOfCompatible : (colimitIdealOfCompatible G q hq).IsPrime where
  ne_top' := by
    rw [Ne, Ideal.eq_top_iff_one, ← map_one (colimit.ι G 0).hom,
      ι_mem_colimitIdealOfCompatible_iff]
    exact fun h ↦ (q 0).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  mem_or_mem' := by
    intro a b hab
    obtain ⟨m, y, rfl⟩ := Concrete.colimit_exists_rep G a
    obtain ⟨n, z, rfl⟩ := Concrete.colimit_exists_rep G b
    rw [← colimit.w G (homOfLE (le_max_left m n)), ← colimit.w G (homOfLE (le_max_right m n)),
      CommRingCat.comp_apply, CommRingCat.comp_apply, ← map_mul,
      ι_mem_colimitIdealOfCompatible_iff] at hab
    rw [← colimit.w G (homOfLE (le_max_left m n)), ← colimit.w G (homOfLE (le_max_right m n)),
      CommRingCat.comp_apply, CommRingCat.comp_apply, ι_mem_colimitIdealOfCompatible_iff,
      ι_mem_colimitIdealOfCompatible_iff]
    exact (q _).isPrime.mem_or_mem hab

include hq in
/-- **Points of the spectrum of a sequential colimit.** A compatible sequence of primes `qₙ` of
the rings `G n` of a sequence comes from a prime of `colim G`. -/
theorem exists_comap_colimit_ι_eq :
    ∃ P : PrimeSpectrum (colimit G : CommRingCat), ∀ n, comap (colimit.ι G n).hom P = q n :=
  ⟨⟨colimitIdealOfCompatible G q hq, isPrime_colimitIdealOfCompatible G q hq⟩, fun n ↦
    PrimeSpectrum.ext (Ideal.ext fun y ↦ ι_mem_colimitIdealOfCompatible_iff G q hq n y)⟩

end Compatible

end PrimeSpectrum

namespace AlgebraicGeometry.Scheme.AffineProEt

variable {S : Scheme.{u}} {W : ℕ → S.AffineProEt} {π : ∀ n, W (n + 1) ⟶ W n}

/-- **Points of a sequential limit** in the affine pro-étale site: a compatible sequence of
points `xₙ` of the `Wₙ` comes from a point of `W_∞ = Spec (colim Γ(Wₙ))`. -/
theorem exists_seqLimitπ_eq (x : ∀ n, (W n).left)
    (hx : ∀ n, (π n).left.base (x (n + 1)) = x n) :
    ∃ y : (seqLimit W π).left, ∀ n, (seqLimitπ W π n).left.base y = x n := by
  let q (n : ℕ) : PrimeSpectrum Γ((W n).left, ⊤) := (W n).left.isoSpec.hom.base (x n)
  have hq (n : ℕ) : PrimeSpectrum.comap ((ringSeq W π).map (homOfLE n.le_succ)).hom (q (n + 1)) =
      q n := by
    rw [ringSeq_map_succ]
    change (Spec.map (π n).left.appTop).base ((W (n + 1)).left.isoSpec.hom.base (x (n + 1))) = _
    rw [← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality, Scheme.Hom.comp_apply, hx]
  obtain ⟨P, hP⟩ := PrimeSpectrum.exists_comap_colimit_ι_eq (ringSeq W π) q hq
  refine ⟨P, fun n ↦ ?_⟩
  change ((W n).left.isoSpec.inv).base ((Spec.map (colimit.ι (ringSeq W π) n)).base P) = x n
  change ((W n).left.isoSpec.inv).base (PrimeSpectrum.comap (colimit.ι (ringSeq W π) n).hom P) = _
  rw [hP n, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

end AlgebraicGeometry.Scheme.AffineProEt

namespace AlgebraicGeometry.ProEtale

open Scheme

section ExtensionByZeroLimit

variable {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]

set_option synthInstance.maxHeartbeats 400000 in
/-- **A section of an extension by zero vanishes on a cover of the complement.** For a section
`r` of `j_! G` over an object `B` of the affine pro-étale site, there is a morphism `B' ⟶ B` of
the affine pro-étale site along which `r` vanishes and whose image contains every point of `B`
lying over the complement of `U`. Indeed `r` locally comes from the presheaf extension by zero,
whose sections over objects not factoring through `U` vanish; the members of a finite
jointly surjective family on which `r` vanishes are collected into a single disjoint union. -/
lemma exists_map_eq_zero_openImmersionLowerShriek_of_affineProEt
    (G : Sheaf (ProEt.topology U) AddCommGrpCat.{u + 1}) (B : T.AffineProEt)
    (r : ToType (((j)_!open[AddCommGrpCat.{u + 1}].obj G).obj.obj
      (op ((AffineProEt.toProEt T).obj B)))) :
    ∃ (B' : T.AffineProEt) (π : B' ⟶ B),
      ((j)_!open[AddCommGrpCat.{u + 1}].obj G).obj.map ((AffineProEt.toProEt T).map π).op r =
        0 ∧ ∀ x : B.left, B.hom.base x ∉ Set.range j.base → x ∈ Set.range π.left.base := by
  set H := (j)_!open[AddCommGrpCat.{u + 1}].obj G
  set L := openImmersionLocalization j
  let R : Sieve ((AffineProEt.toProEt T).obj B) :=
    { arrows := fun W f ↦ Set.range W.hom.base ⊆ Set.range j.base ∨ H.obj.map f.op r = 0
      downward_closed := by
        rintro W W' f (hf | hf) g
        · left
          rintro _ ⟨y, rfl⟩
          refine hf ⟨g.left.base y, ?_⟩
          rw [← MorphismProperty.Over.w g]
          rfl
        · right
          rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hf, map_zero] }
  have hR : R ∈ ProEt.topology T ((AffineProEt.toProEt T).obj B) := by
    have : Presheaf.IsLocallySurjective (ProEt.topology T)
        (toSheafify (ProEt.topology T) (L.op.leftKanExtension G.obj)) :=
      Presheaf.isLocallySurjective_toSheafify' (J := ProEt.topology T) _
    refine GrothendieckTopology.superset_covering _ ?_ (Presheaf.imageSieve_mem
      (ProEt.topology T) (toSheafify (ProEt.topology T) (L.op.leftKanExtension G.obj)) r)
    rintro W f ⟨t, ht⟩
    by_cases hc : IsEmpty (CostructuredArrow L.op (op W))
    · right
      have hI := (isColimitEquivIsInitialOfIsEmpty _ _).1
        (L.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.obj (op W))
      have : Subsingleton (ToType ((L.op.leftKanExtension G.obj).obj (op W))) :=
        AddCommGrpCat.subsingleton_of_isZero hI.isZero
      change ConcreteCategory.hom ((sheafify (ProEt.topology T)
        (L.op.leftKanExtension G.obj)).map f.op) r = 0
      rw [← ht, Subsingleton.elim t 0, map_zero]
    · left
      obtain ⟨c⟩ := not_isEmpty_iff.1 hc
      rintro _ ⟨y, rfl⟩
      refine ⟨(c.left.unop.hom).base ((c.hom.unop.left).base y), ?_⟩
      have h₁ := MorphismProperty.Over.w c.hom.unop
      change (c.hom.unop.left ≫ c.left.unop.hom ≫ j) = W.hom at h₁
      rw [← h₁]
      rfl
  have hRp : R.functorPullback (AffineProEt.toProEt T) ∈ AffineProEt.topology T B :=
    Functor.mem_restrictedTopology_of_functorPushforward_mem _
      (Functor.IsCoverDense.functorPullback_pushforward_covering ⟨R, hR⟩)
  obtain ⟨ι, _, V, f, hRf, hsurj⟩ :=
    AffineProEt.exists_finite_jointly_surjective_of_mem_topology hRp
  let ι' := {i : ι // H.obj.map ((AffineProEt.toProEt T).map (f i)).op r = 0}
  let V' (i : ι') : T.AffineProEt := V i.1
  let f' (i : ι') : V' i ⟶ B := f i.1
  refine ⟨AffineProEt.sigmaCover V' f', AffineProEt.sigmaCoverπ V' f', ?_, fun x hx ↦ ?_⟩
  · let Fa : T.AffineProEtᵒᵖ ⥤ Type (u + 1) :=
      (AffineProEt.toProEt T).op ⋙ H.obj ⋙ forget AddCommGrpCat.{u + 1}
    have hFa : Presheaf.IsSheaf (AffineProEt.topology T) Fa :=
      Presheaf.isSheaf_comp_of_isSheaf _ _ (forget AddCommGrpCat.{u + 1})
        (((AffineProEt.toProEt T).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (AffineProEt.topology T) (ProEt.topology T)).obj H).property
    refine AffineProEt.sigmaCover_ext V' f' hFa (z' := (0 : ToType (H.obj.obj
      (op ((AffineProEt.toProEt T).obj (AffineProEt.sigmaCover V' f')))))) fun i ↦ ?_
    change H.obj.map ((AffineProEt.toProEt T).map (AffineProEt.sigmaCoverι V' f' i)).op
        (H.obj.map ((AffineProEt.toProEt T).map (AffineProEt.sigmaCoverπ V' f')).op r) =
      H.obj.map ((AffineProEt.toProEt T).map (AffineProEt.sigmaCoverι V' f' i)).op 0
    rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      ← Functor.map_comp, AffineProEt.sigmaCoverι_π]
    exact i.2
  · obtain ⟨i, y, rfl⟩ := hsurj x
    have hi : H.obj.map ((AffineProEt.toProEt T).map (f i)).op r = 0 := by
      refine (hRf i).resolve_left fun h ↦ hx ?_
      obtain ⟨z, hz⟩ := h ⟨y, rfl⟩
      refine ⟨z, hz.trans ?_⟩
      rw [← MorphismProperty.Over.w (f i)]
      rfl
    refine ⟨(AffineProEt.sigmaCoverι V' f' ⟨i, hi⟩).left.base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← MorphismProperty.Comma.comp_left,
      AffineProEt.sigmaCoverι_π]
    rfl

end ExtensionByZeroLimit

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

section RingHom

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  {R : Type*} [Ring R]

/-- An additive functor maps an action `R →+* End X` of a ring on an object to an action on its
image. -/
@[simps]
def _root_.CategoryTheory.Functor.mapRingHom (G : C ⥤ D) [G.Additive] {X : C}
    (φ : R →+* End X) : R →+* End (G.obj X) where
  toFun r := G.map (φ r)
  map_one' := by rw [map_one]; exact G.map_id X
  map_mul' r s := by rw [map_mul]; exact G.map_comp _ _
  map_zero' := by rw [map_zero]; exact G.map_zero _ _
  map_add' r s := by rw [map_add]; exact G.map_add

end RingHom

variable {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (p : ℕ) [Fact p.Prime]

/-- The action of `ℤ_p` on `j_! C(-, ℤ_p)`. -/
noncomputable abbrev compactIntegralSmulRingHom :
    ℤ_[p] →+* End ((j)_!open[AddCommGrpCat.{u + 1}].obj (continuousSheaf U ℤ_[p])) :=
  (j)_!open[AddCommGrpCat.{u + 1}].mapRingHom (integralSmulRingHom U p)

/-- The action of `ℤ_p` on `j_! C(-, ℤ_p / pᵐ)`. -/
noncomputable abbrev compactFiniteSmulRingHom (m : ℕ) :
    ℤ_[p] →+* End ((j)_!open[AddCommGrpCat.{u + 1}].obj
      (continuousSheaf U (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p])))) :=
  (j)_!open[AddCommGrpCat.{u + 1}].mapRingHom (finiteSmulRingHom U p m)

/-- The integral `p`-adic pro-étale cohomology `Hⁿ(T, j_! ℤ_p) = Hⁿ(T_proét, j_! C(-, ℤ_p))` of
the extension by zero along an open immersion `j : U ⟶ T`, a `ℤ_p`-module. For `T` proper over
an algebraically closed field this is the compactly supported cohomology `Hⁿ_c(U, ℤ_p)`. -/
def CompactIntegralAdicH (n : ℕ) : Type (u + 1) :=
  Sheaf.H ((j)_!open[AddCommGrpCat.{u + 1}].obj (continuousSheaf U ℤ_[p])) n

noncomputable instance (n : ℕ) : AddCommGroup (CompactIntegralAdicH j p n) :=
  inferInstanceAs (AddCommGroup (Sheaf.H ((j)_!open[AddCommGrpCat.{u + 1}].obj
    (continuousSheaf U ℤ_[p])) n))

noncomputable instance (n : ℕ) : Module ℤ_[p] (CompactIntegralAdicH j p n) :=
  Ext.moduleOfRingHom (compactIntegralSmulRingHom j p) n

/-- The pro-étale cohomology `Hⁿ(T, j_! ℤ/pᵐ) = Hⁿ(T_proét, j_! C(-, ℤ_p / pᵐ))` of the
extension by zero along an open immersion `j : U ⟶ T`, a `ℤ_p`-module. -/
def CompactFiniteAdicH (m n : ℕ) : Type (u + 1) :=
  Sheaf.H ((j)_!open[AddCommGrpCat.{u + 1}].obj
    (continuousSheaf U (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p])))) n

noncomputable instance (m n : ℕ) : AddCommGroup (CompactFiniteAdicH j p m n) :=
  inferInstanceAs (AddCommGroup (Sheaf.H ((j)_!open[AddCommGrpCat.{u + 1}].obj
    (continuousSheaf U (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p])))) n))

noncomputable instance (m n : ℕ) : Module ℤ_[p] (CompactFiniteAdicH j p m n) :=
  Ext.moduleOfRingHom (compactFiniteSmulRingHom j p m) n

/-- The extension by zero `j_! C(-, ℤ_p) ⟶ j_! C(-, ℤ_p / pᵐ)` of the reduction. -/
noncomputable abbrev compactReductionSheafMap (m : ℕ) :
    (j)_!open[AddCommGrpCat.{u + 1}].obj (continuousSheaf U ℤ_[p]) ⟶
      (j)_!open[AddCommGrpCat.{u + 1}].obj
        (continuousSheaf U (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p]))) :=
  (j)_!open[AddCommGrpCat.{u + 1}].map (reductionSheafMap U p m)

lemma compactReductionSheafMap_comm (m : ℕ) (c : ℤ_[p]) :
    compactIntegralSmulRingHom j p c ≫ compactReductionSheafMap j p m =
      compactReductionSheafMap j p m ≫ compactFiniteSmulRingHom j p m c := by
  simp only [Functor.mapRingHom_apply, ← Functor.map_comp, reductionSheafMap_comm]

/-- The reduction `ρₘ : Hⁿ(T, j_! ℤ_p) ⟶ Hⁿ(T, j_! ℤ/pᵐ)`. -/
noncomputable def compactReduction (m n : ℕ) :
    CompactIntegralAdicH j p n →ₗ[ℤ_[p]] CompactFiniteAdicH j p m n :=
  Ext.postcompLinearMap (compactIntegralSmulRingHom j p) (compactFiniteSmulRingHom j p m)
    (compactReductionSheafMap j p m) (compactReductionSheafMap_comm j p m) n

lemma compactReduction_apply (m n : ℕ) (x : CompactIntegralAdicH j p n) :
    compactReduction j p m n x = Ext.comp (C := Sheaf (Scheme.ProEt.topology T)
      AddCommGrpCat.{u + 1}) x (Ext.mk₀ (compactReductionSheafMap j p m)) (add_zero n) :=
  rfl

/-- `pᵐ` kills `Hⁿ(T, j_! ℤ/pᵐ)`. -/
lemma pow_smul_compactFiniteAdicH (m n : ℕ) (y : CompactFiniteAdicH j p m n) :
    (p : ℤ_[p]) ^ m • y = 0 := by
  have h : finiteSmulRingHom U p m ((p : ℤ_[p]) ^ m) = 0 := by
    refine (continuousSheafMap_congr U fun x ↦ ?_).trans (continuousSheafMap_zero U)
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      refine (QuotientAddGroup.eq_zero_iff _).2 ?_
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  change Ext.comp y (Ext.mk₀ ((j)_!open[AddCommGrpCat.{u + 1}].map
    (finiteSmulRingHom U p m ((p : ℤ_[p]) ^ m)))) (add_zero n) = 0
  rw [h, Functor.map_zero, Ext.mk₀_zero, Ext.comp_zero]

/-- The extension by zero of the Bockstein short complex,
`j_! C(-, ℤ_p) --pᵐ--> j_! C(-, ℤ_p) ⟶ j_! C(-, ℤ_p / pᵐ)`. -/
noncomputable abbrev compactBocksteinShortComplex (m : ℕ) :
    ShortComplex (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) :=
  (bocksteinShortComplex U p m).map (j)_!open[AddCommGrpCat.{u + 1}]

lemma shortExact_compactBocksteinShortComplex (m : ℕ) :
    (compactBocksteinShortComplex j p m).ShortExact :=
  (shortExact_bocksteinShortComplex U p m).map_of_exact _

/-- **Bockstein, first part.** The kernel of `ρₘ : Hⁿ(T, j_! ℤ_p) ⟶ Hⁿ(T, j_! ℤ/pᵐ)` is
`pᵐ Hⁿ(T, j_! ℤ_p)`. -/
theorem exists_eq_pow_smul_of_compactReduction_eq_zero (m n : ℕ)
    {x : CompactIntegralAdicH j p n} (hx : compactReduction j p m n x = 0) :
    ∃ x', x = (p : ℤ_[p]) ^ m • x' := by
  obtain ⟨x', hx'⟩ := Ext.covariant_sequence_exact₂ _
    (shortExact_compactBocksteinShortComplex j p m) (n := n) x hx
  exact ⟨x', hx'.symm⟩

/-- The connecting map `δ : Hⁿ(T, j_! ℤ/pᵐ) ⟶ Hⁿ⁺¹(T, j_! ℤ_p)` of the Bockstein sequence. -/
noncomputable def compactBocksteinδ (m n : ℕ) :
    CompactFiniteAdicH j p m n →+ CompactIntegralAdicH j p (n + 1) :=
  AddMonoidHom.mk' (fun y ↦ Ext.comp (C := Sheaf (Scheme.ProEt.topology T)
    AddCommGrpCat.{u + 1}) y (shortExact_compactBocksteinShortComplex j p m).extClass rfl)
    fun _ _ ↦ Ext.add_comp _ _ _ _

private lemma pow_smul_eq_nsmul_compactIntegral (n e : ℕ) (x : CompactIntegralAdicH j p n) :
    (p : ℤ_[p]) ^ e • x = (p ^ e) • x := by
  rw [← Ext.smul_natCast_eq_nsmul (compactIntegralSmulRingHom j p) n (p ^ e) x, Nat.cast_pow]

private lemma pow_smul_eq_nsmul_compactFinite (m n e : ℕ) (y : CompactFiniteAdicH j p m n) :
    (p : ℤ_[p]) ^ e • y = (p ^ e) • y := by
  rw [← Ext.smul_natCast_eq_nsmul (compactFiniteSmulRingHom j p m) n (p ^ e) y, Nat.cast_pow]

/-- **Bockstein, second part.** If `pᵉ` kills the `p`-power torsion of `Hⁿ⁺¹(T, j_! ℤ_p)`,
then the image of `ρₘ : Hⁿ(T, j_! ℤ_p) ⟶ Hⁿ(T, j_! ℤ/pᵐ)` contains `pᵉ Hⁿ(T, j_! ℤ/pᵐ)`. -/
theorem pow_smul_mem_range_compactReduction (m n e : ℕ)
    (he : ∀ x : CompactIntegralAdicH j p (n + 1), (∃ k, (p : ℤ_[p]) ^ k • x = 0) →
      (p : ℤ_[p]) ^ e • x = 0)
    (y : CompactFiniteAdicH j p m n) :
    (p : ℤ_[p]) ^ e • y ∈ LinearMap.range (compactReduction j p m n) := by
  have hδ (k : ℕ) : compactBocksteinδ j p m n ((p : ℤ_[p]) ^ k • y) =
      (p : ℤ_[p]) ^ k • compactBocksteinδ j p m n y := by
    rw [pow_smul_eq_nsmul_compactFinite, pow_smul_eq_nsmul_compactIntegral, map_nsmul]
  have h0 : compactBocksteinδ j p m n ((p : ℤ_[p]) ^ e • y) = 0 := by
    rw [hδ, he _ ⟨m, by rw [← hδ, pow_smul_compactFiniteAdicH, map_zero]⟩]
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ _
    (shortExact_compactBocksteinShortComplex j p m) ((p : ℤ_[p]) ^ e • y) rfl h0
  exact ⟨x, hx⟩


section Separation

variable {j p}

/-- The tower `j_! C(-, ℤ_p / pᵐ)` of extensions by zero. -/
noncomputable abbrev compactContinuousSheafTower :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  continuousSheafTower U (powOpenAddSubgroup p) (powOpenAddSubgroup_succ_le p) ⋙
    (j)_!open[AddCommGrpCat.{u + 1}]

variable (j p) in
/-- The cone `j_! C(-, ℤ_p) ⟶ j_! C(-, ℤ_p / pᵐ)` over the tower `compactContinuousSheafTower`. -/
noncomputable abbrev compactContinuousSheafCone :
    Cone (compactContinuousSheafTower (j := j) (p := p)) :=
  (j)_!open[AddCommGrpCat.{u + 1}].mapCone
    (continuousSheafCone U (powOpenAddSubgroup p) (powOpenAddSubgroup_succ_le p))

/-- **Separation in degree `n + 1`**, given that `j_! C(-, ℤ_p)` is the limit of the tower
`j_! C(-, ℤ/pᵐ)`. -/
theorem eq_zero_of_forall_compactReduction_eq_zero_succ_of_isLimit
    (hlim : IsLimit (compactContinuousSheafCone j p)) (n : ℕ)
    (hfin : ∀ m, Finite (CompactFiniteAdicH j p m n)) (x : CompactIntegralAdicH j p (n + 1))
    (hx : ∀ m, compactReduction j p m (n + 1) x = 0) : x = 0 := by
  have hU := powOpenAddSubgroup_succ_le p
  have hrep := Scheme.ProEt.epiπAppZeroOfEpi_addCommGrpCat (S := T)
  have := Abelian.hasFiniteBiproducts (C := Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
  have := lim_preservesEpimorphisms_of_epi_π_app_zero hrep
  have := hasExactLimitsOfShape_of_preservesEpi
    (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) (Discrete ℕ)
  have hepi (k : ℕ) :
      Epi ((compactContinuousSheafTower (j := j) (p := p)).map (homOfLE k.le_succ).op) := by
    rw [Functor.comp_map, continuousSheafTower_map_succ]
    have : Epi (continuousSheafMap U (openAddSubgroupQuotientMap (powOpenAddSubgroup p) hU k)) :=
      (shortExact_continuousSheafShortComplex U (powOpenAddSubgroup p) hU k).epi_g
    exact (j)_!open[AddCommGrpCat.{u + 1}].map_epi _
  refine Ext.eq_zero_of_isLimit_tower _
    (fun P hP t ht ↦ epi_one_sub_of_epiπAppZeroOfEpi hrep hepi hP t ht) hlim (q := n)
    (fun y ↦ ?_) x hx
  let F := compactContinuousSheafTower (j := j) (p := p)
  have (k : ℕ) : Finite (Sheaf.H (F.obj (op k)) n) := hfin k
  obtain ⟨w, hw⟩ := AddCommGroup.exists_sub_map_succ_eq_of_finite
    (G := fun k ↦ Sheaf.H (F.obj (op k)) n)
    (fun k ↦ (Ext.mk₀ (F.map (homOfLE k.le_succ).op)).postcomp _ (add_zero n)) y
  exact ⟨w, hw⟩

/-- **Separation in degree `0`**, given that `j_! C(-, ℤ_p)` is the limit of the tower
`j_! C(-, ℤ/pᵐ)`. -/
theorem eq_zero_of_forall_compactReduction_eq_zero_zero_of_isLimit
    (hlim : IsLimit (compactContinuousSheafCone j p)) (x : CompactIntegralAdicH j p 0)
    (hx : ∀ m, compactReduction j p m 0 x = 0) : x = 0 := by
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
  have hf : f = 0 := by
    refine hlim.hom_ext fun ⟨m⟩ ↦ ?_
    rw [zero_comp]
    refine (Ext.mk₀_bijective _ _).1 ?_
    rw [Ext.mk₀_zero, ← Ext.mk₀_comp_mk₀]
    exact hx m
  rw [hf, Ext.mk₀_zero]

/-- **Separation**, given that `j_! C(-, ℤ_p)` is the limit of the tower `j_! C(-, ℤ/pᵐ)`: if
the groups `Hⁿ⁻¹(T, j_! ℤ/pᵐ)` are finite, a class of `Hⁿ(T, j_! ℤ_p)` whose reductions modulo
all `pᵐ` vanish is zero. -/
theorem eq_zero_of_forall_compactReduction_eq_zero_of_isLimit
    (hlim : IsLimit (compactContinuousSheafCone j p)) (n : ℕ)
    (hfin : ∀ m k, k + 1 = n → Finite (CompactFiniteAdicH j p m k))
    (x : CompactIntegralAdicH j p n) (hx : ∀ m, compactReduction j p m n x = 0) : x = 0 := by
  cases n with
  | zero => exact eq_zero_of_forall_compactReduction_eq_zero_zero_of_isLimit hlim x hx
  | succ n =>
    exact eq_zero_of_forall_compactReduction_eq_zero_succ_of_isLimit hlim n
      (fun m ↦ hfin m n rfl) x hx

/-- **Finite generation**, given that `j_! C(-, ℤ_p)` is the limit of the tower
`j_! C(-, ℤ/pᵐ)`: if the groups `Hⁿ⁻¹(T, j_! ℤ/pᵐ)` and `Hⁿ(T, j_! ℤ/p)` are finite, then
`Hⁿ(T, j_! ℤ_p)` is a finitely generated `ℤ_p`-module. -/
theorem module_finite_compactIntegralAdicH_of_isLimit
    (hlim : IsLimit (compactContinuousSheafCone j p)) (n : ℕ)
    (hfin : ∀ m k, k + 1 = n → Finite (CompactFiniteAdicH j p m k))
    [Finite (CompactFiniteAdicH j p 1 n)] :
    Module.Finite ℤ_[p] (CompactIntegralAdicH j p n) :=
  PadicInt.module_finite_of_finite_quotient (fun m ↦ compactReduction j p m n)
    (fun m y ↦ pow_smul_compactFiniteAdicH j p m n y)
    (fun m _ ha ↦ exists_eq_pow_smul_of_compactReduction_eq_zero j p m n ha)
    (fun a ha ↦ eq_zero_of_forall_compactReduction_eq_zero_of_isLimit hlim n hfin a ha)

end Separation

end AlgebraicGeometry.ProEtale
