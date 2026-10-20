/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Bounded-below flat representatives over the integers

Source: Stacks Project, Etale Cohomology, Tag 0F0E (lemma-pull-out-constant), first
model-construction paragraph; More on Algebra, Tag 0653 (lemma-last-one-flat)
(blueprint: lem-kun-torsionfree-complex-model).

Integer modules encode abelian groups with their unique integer module structure.
`Module.Flat` expresses exactness of tensoring, by `Module.Flat.iff_rTensor_exact`.
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory.Plus

-- Omitting the zero generator makes this free module zero whenever C.X n is zero.
private abbrev Generators (C : CochainComplex (ModuleCat.{u} ℤ) ℤ) (n : ℤ) :=
  {x : C.X n // x ≠ 0} →₀ ℤ

private noncomputable def evaluation (C : CochainComplex (ModuleCat.{u} ℤ) ℤ) (n : ℤ) :
    Generators C n →ₗ[ℤ] C.X n :=
  Finsupp.linearCombination ℤ (fun x : {x : C.X n // x ≠ 0} ↦ x.1)

private theorem evaluation_surjective (C : CochainComplex (ModuleCat.{u} ℤ) ℤ) (n : ℤ) :
    Function.Surjective (evaluation C n) := by
  classical
  intro x
  by_cases h : x = 0
  · exact ⟨0, by simp [h]⟩
  · exact ⟨Finsupp.single ⟨x, h⟩ 1, by simp [evaluation]⟩

private noncomputable def generatorCast (C : CochainComplex (ModuleCat.{u} ℤ) ℤ)
    (n : ℤ) : Generators C n ≃ₗ[ℤ] Generators C (n + 1 - 1) :=
  LinearEquiv.cast (by rw [show n + 1 - 1 = n by omega])

private theorem evaluation_cast (C : CochainComplex (ModuleCat.{u} ℤ) ℤ)
    (i j k : ℤ) (h : i = j) (x : Generators C i) :
    (C.d j k) (evaluation C j ((LinearEquiv.cast (R := ℤ) (M := Generators C) h) x)) =
      (C.d i k) (evaluation C i x) := by
  subst j
  rfl

private noncomputable def coverD (C : CochainComplex (ModuleCat.{u} ℤ) ℤ) (n : ℤ) :
    ModuleCat.of ℤ (Generators C n × Generators C (n - 1)) ⟶
      ModuleCat.of ℤ (Generators C (n + 1) × Generators C (n + 1 - 1)) :=
  ModuleCat.ofHom ((0 : Generators C n × Generators C (n - 1) →ₗ[ℤ]
    Generators C (n + 1)).prod
      ((generatorCast C n).toLinearMap.comp (LinearMap.fst ℤ _ _)))

private theorem coverD_sq (C : CochainComplex (ModuleCat.{u} ℤ) ℤ) (n : ℤ) :
    coverD C n ≫ coverD C (n + 1) = 0 := by
  ext x <;> simp [coverD]

private noncomputable def cover (C : CochainComplex (ModuleCat.{u} ℤ) ℤ) :
    CochainComplex (ModuleCat.{u} ℤ) ℤ :=
  CochainComplex.of (fun n ↦ ModuleCat.of ℤ (Generators C n × Generators C (n - 1)))
    (coverD C) (coverD_sq C)

private noncomputable def coverπF (C : CochainComplex (ModuleCat.{u} ℤ) ℤ) (n : ℤ) :
    (cover C).X n ⟶ C.X n :=
  ModuleCat.ofHom (((evaluation C n).comp (LinearMap.fst ℤ _ _)) +
    (((C.d (n - 1) n).hom.comp (evaluation C (n - 1))).comp (LinearMap.snd ℤ _ _)))

private theorem coverπF_comm (C : CochainComplex (ModuleCat.{u} ℤ) ℤ) (n : ℤ) :
    coverπF C n ≫ C.d n (n + 1) = (cover C).d n (n + 1) ≫ coverπF C (n + 1) := by
  dsimp only [cover, coverπF]
  simp only [CochainComplex.of_d]
  have hn : n + 1 - 1 = n := by omega
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hc := evaluation_cast C n (n + 1 - 1) (n + 1) hn.symm x.1
  simp [coverD, generatorCast, ← hc]

private noncomputable def coverπ (C : CochainComplex (ModuleCat.{u} ℤ) ℤ) : cover C ⟶ C :=
  CochainComplex.ofHom (coverπF C) (coverπF_comm C)

private theorem coverπ_surjective (C : CochainComplex (ModuleCat.{u} ℤ) ℤ) (n : ℤ) :
    Function.Surjective ((coverπ C).f n) := by
  intro x
  obtain ⟨y, hy⟩ := evaluation_surjective C n x
  refine ⟨(y, 0), ?_⟩
  change evaluation C n y + (C.d (n - 1) n) (evaluation C (n - 1) 0) = x
  simpa using hy

private theorem cover_isZero (C : CochainComplex (ModuleCat.{u} ℤ) ℤ)
    (a : ℤ) (hC : ∀ i : ℤ, i < a → IsZero (C.X i)) (n : ℤ) (hn : n < a) :
    IsZero ((cover C).X n) := by
  have h₁ := ModuleCat.subsingleton_of_isZero (hC n hn)
  have h₂ := ModuleCat.subsingleton_of_isZero (hC (n - 1) (by omega))
  have : IsEmpty {x : C.X n // x ≠ 0} := ⟨fun x ↦ x.2 (Subsingleton.elim _ _)⟩
  have : IsEmpty {x : C.X (n - 1) // x ≠ 0} := ⟨fun x ↦ x.2 (Subsingleton.elim _ _)⟩
  change IsZero (ModuleCat.of ℤ (Generators C n × Generators C (n - 1)))
  exact ModuleCat.isZero_of_subsingleton _

private theorem cover_flat (C : CochainComplex (ModuleCat.{u} ℤ) ℤ) (n : ℤ) :
    Module.Flat ℤ ((cover C).X n) := by
  change Module.Flat ℤ (Generators C n × Generators C (n - 1))
  infer_instance

private theorem kernel_cover_torsionFree (C : CochainComplex (ModuleCat.{u} ℤ) ℤ)
    (n : ℤ) : Module.IsTorsionFree ℤ ((kernel (coverπ C)).X n) := by
  have := cover_flat C n
  let f := (kernel.ι (coverπ C)).f n
  exact Function.Injective.moduleIsTorsionFree f
    ((ModuleCat.mono_iff_injective f).mp inferInstance) (fun r x ↦ f.hom.map_smul r x)

private theorem torsionFree_prod (R : Type*) [CommRing R] (M N : ModuleCat.{u} R)
    [Module.IsTorsionFree R M] [Module.IsTorsionFree R N] :
    Module.IsTorsionFree R (ModuleCat.of R (M × N)) := by
  constructor
  intro r hr x y h
  exact Prod.ext (hr.isSMulRegular (congrArg Prod.fst h))
    (hr.isSMulRegular (congrArg Prod.snd h))

private theorem torsionFree_of_mono (R : Type*) [CommRing R]
    {M N : ModuleCat.{u} R} (f : M ⟶ N) [Mono f] [Module.IsTorsionFree R N] :
    Module.IsTorsionFree R M :=
  Function.Injective.moduleIsTorsionFree f
    ((ModuleCat.mono_iff_injective f).mp inferInstance) (fun r x ↦ f.hom.map_smul r x)

private theorem torsionFree_of_iso_prod (R : Type*) [CommRing R]
    {L M N : ModuleCat.{u} R} (e : L ≅ ModuleCat.of R (M × N))
    [Module.IsTorsionFree R M] [Module.IsTorsionFree R N] :
    Module.IsTorsionFree R L := by
  have := torsionFree_prod R M N
  exact torsionFree_of_mono R e.hom

/-- Every bounded-below derived object of integer modules has a bounded-below flat representative.
Source: Stacks Project, Tag 0F0E, first model-construction paragraph, and Tag 0653
(blueprint: lem-kun-torsionfree-complex-model).

Proof plan:
1. Membership in the bounded-below derived category gives a lower cohomological bound `a`.
The standard t-structure (def-sbc-standard-tstructure-derived-category) supplies a representative
`C` zero below `a`, with an isomorphism `Q(C) ≅ K`.
2. For `n ≥ a` let `Aₙ` be the free integer module on the underlying set of `Cⁿ`, with evaluation
`eₙ : Aₙ → Cⁿ`. Below `a` take zero. Evaluation is surjective by the singleton generators;
each `Aₙ` is torsion free by evaluating coordinates in the integers.
3. Put `Fⁿ = Aₙ ⊕ Aₙ₋₁`, with differential `(x,y) ↦ (0,x)` and map
`qⁿ(x,y) = eₙ(x) + d_C(eₙ₋₁(y))`. The differential squares to zero, and `q` is a chain map
since both sides of its chain-map identity equal `d_C(eₙ(x))`. It is degreewise surjective,
zero below `a`, and has torsion-free terms.
4. Let `G = ker(q)` with restricted differential and inclusion `i : G → F`. Form its cone
`Pⁿ = Fⁿ ⊕ Gⁿ⁺¹`, with differential `(f,g) ↦ (d_F(f) + i(g), -d_G(g))`.
Its differential squares to zero because `d_F i = i d_G`. The map `p(f,g) = q(f)` is a chain
map since `qi = 0`. Both summands vanish below `a - 1`, so `P` has lower bound `a - 1`.
5. Given a cycle `c` in `Cⁿ`, lift it to `f` in `Fⁿ`. Then `d_F(f)` lies in `Gⁿ⁺¹`, and
`(f,-d_F(f))` is a cycle of `P` mapping to `c`. Thus `p` is surjective on cohomology.
6. If a cycle `(f,g)` maps to `d_C(c₀)`, lift `c₀` to `t` in `Fⁿ⁻¹` and subtract
`d_P(t,0)`. The remaining cycle `(f₁,g)` has `f₁ = f - d_F(t)` in `Gⁿ` and
`g = -d_G(f₁)`. It is the boundary `d_P(0,f₁)`. Hence `p` is also injective on cohomology,
and therefore a quasi-isomorphism, as in def-weil-abstract-derived-category.
7. Each `Gⁿ`, being a subgroup of the torsion-free `Fⁿ`, is torsion free; so is each `Pⁿ`.
Apply lem-weil-pbc-pid-torsion-free-module-flat to the PID of integers to get flatness,
without a finite-generation hypothesis. The zero ideal is principal, and every nonzero ideal
is generated by its least positive element by division with remainder.
8. By lem-weil-pbc-flat-tensor-exact, tensoring a short exact sequence with `Pⁿ` preserves
exactness at all three places: apply it to the triples starting or ending with zero as well
as the middle triple. Tensoring zero gives zero, so injectivity and surjectivity are preserved.
This is exactly the flatness meaning in the statement.
9. Localization (def-weil-abstract-derived-category) sends the quasi-isomorphism `p` to an
isomorphism `Q(P) ≅ Q(C)`. Compose it with the isomorphism from step 1. The lower bound from
step 4 and flatness from steps 7 and 8 give every required clause. -/
theorem exists_boundedBelow_flat_representative
    [HasDerivedCategory.{w} (ModuleCat.{u} ℤ)]
    (K : DerivedCategory.Plus (ModuleCat.{u} ℤ)) :
    ∃ (P : CochainComplex (ModuleCat.{u} ℤ) ℤ) (b : ℤ),
      (∀ (i : ℤ), i < b → IsZero (P.X i)) ∧
      (∀ (i : ℤ), Module.Flat ℤ (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Plus.ι.obj K) := by
  classical
  -- Use the explicit free cover and Mathlib's kernel-cone quasi-isomorphism.
  obtain ⟨a, ha⟩ := K.property
  have : (DerivedCategory.Plus.ι.obj K).IsGE a := ha
  obtain ⟨C, hC, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_Q_obj_of_isGE (DerivedCategory.Plus.ι.obj K) a
  have hzero (n : ℤ) (hn : n < a) : IsZero (C.X n) := C.isZero_of_isStrictlyGE a n hn
  let q := coverπ C
  have : Epi q := HomologicalComplex.epi_of_epi_f q (fun n ↦
    (ModuleCat.epi_iff_surjective _).mpr (coverπ_surjective C n))
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  let P := CochainComplex.mappingCone S.f
  have hPzero (n : ℤ) (hn : n < a - 1) : IsZero (P.X n) := by
    apply (CochainComplex.mappingCone.isZero_X_iff S.f n).mpr
    exact ⟨IsZero.of_mono ((kernel.ι q).f (n + 1))
      (cover_isZero C a hzero (n + 1) (by omega)),
      cover_isZero C a hzero n (by omega)⟩
  have hPflat (n : ℤ) : Module.Flat ℤ (P.X n) := by
    have := cover_flat C n
    have := kernel_cover_torsionFree C (n + 1)
    let e' := HomologicalComplex.homotopyCofiber.XIsoBiprod S.f n (n + 1) rfl ≪≫
      ModuleCat.biprodIsoProd ((kernel q).X (n + 1)) ((cover C).X n)
    have : Module.IsTorsionFree ℤ (P.X n) := torsionFree_of_iso_prod ℤ e'
    exact Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
      (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  have : QuasiIso (CochainComplex.mappingCone.descShortComplex S) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hS
  exact ⟨P, a - 1, hPzero, hPflat,
    ⟨asIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)) ≪≫
      e.symm⟩⟩

end DerivedCategory.Plus
