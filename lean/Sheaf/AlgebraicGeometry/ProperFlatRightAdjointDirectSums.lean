/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration
import Sheaf.AlgebraicGeometry.PerfectObjectCompact
import Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect
import Sheaf.AlgebraicGeometry.PerfectComplexRepresentatives
import Sheaf.AlgebraicGeometry.DerivedQCohCompactGenerationCore
import Sheaf.AlgebraicGeometry.SupportedPerfectGenerator
import Sheaf.AlgebraicGeometry.DerivedOpenLocalization
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# The right adjoint of proper flat derived direct image preserves direct sums

Source: Stacks Project, Duality for Schemes, Lemma 48.12.1, Section Tag 0E4H
(blueprint: lem-sc-proper-flat-right-adjoint-direct-sums).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem compact_tests_small
    {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{u} C]
    {D : Type*} [Category D] [Preadditive D] [HasCoproducts.{u} D]
    (R : C ⥤ D) (c : D ⥤ C) (adj : R ⊣ c) [R.Additive]
    (S : Type u) (G : S → C)
    (hcompact : ∀ s, IsCompactObject (G s) ∧ IsCompactObject (R.obj (G s)))
    (hdetect : ∀ (A B : C) (g : A ⟶ B),
      (∀ s, Function.Bijective (fun a : G s ⟶ A ↦ a ≫ g)) → IsIso g)
    (I : Type u) : PreservesColimitsOfShape (Discrete I) c := by
  classical
  have hpres (K : I → D) : PreservesColimit (Discrete.functor K) c := by
    have hq : IsIso (sigmaComparison c K) := by
      apply hdetect
      intro s
      let L : ∀ i, (R.obj (G s) ⟶ K i) →+ (G s ⟶ c.obj (K i)) :=
        fun i ↦ (adj.homAddEquiv (G s) (K i)).toAddMonoidHom
      let a := DirectSum.toAddMonoid
        (fun i ↦ Preadditive.rightComp (G s) (Sigma.ι (fun i ↦ c.obj (K i)) i))
      let b := DirectSum.toAddMonoid
        (fun i ↦ Preadditive.rightComp (R.obj (G s)) (Sigma.ι K i))
      let B := (adj.homAddEquiv (G s) (∐ K)).toAddMonoidHom
      let Q := Preadditive.rightComp (G s) (sigmaComparison c K)
      have square : Q.comp (a.comp (DirectSum.map L)) = B.comp b := by
        apply DirectSum.addHom_ext
        intro i f
        simp only [AddMonoidHom.comp_apply, DirectSum.map_of]
        dsimp [a, b]
        rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
        change (adj.homEquiv (G s) (K i) f ≫
          Sigma.ι (fun i ↦ c.obj (K i)) i) ≫ sigmaComparison c K =
          adj.homEquiv (G s) (∐ K) (f ≫ Sigma.ι K i)
        rw [Category.assoc, ι_comp_sigmaComparison, adj.homEquiv_naturality_right]
      have hL : Function.Bijective (DirectSum.map L) :=
        ⟨(DirectSum.map_injective L).2 (fun i ↦ (adj.homEquiv _ _).injective),
          (DirectSum.map_surjective L).2 (fun i ↦ (adj.homEquiv _ _).surjective)⟩
      have ha : Function.Bijective a := (hcompact s).1 I _
      have hb : Function.Bijective b := (hcompact s).2 I K
      have hcomp : Function.Bijective (Q ∘ (a ∘ DirectSum.map L)) := by
        change Function.Bijective (Q.comp (a.comp (DirectSum.map L)))
        rw [square]
        exact (adj.homEquiv _ _).bijective.comp hb
      exact (Function.Bijective.of_comp_iff Q (ha.comp hL)).mp hcomp
    exact PreservesCoproduct.of_iso_comparison c K
  exact preservesColimitsOfShape_of_discrete c

private theorem perfect_of_iso (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    {E F : schemeDerivedCategory X} (e : E ≅ F) (hE : Scheme.IsPerfect X E) :
    Scheme.IsPerfect X F := by
  intro x
  obtain ⟨U, hx, K, hK, ⟨eK⟩⟩ := hE x
  exact ⟨U, hx, K, hK, ⟨((SheafOfModules.overFunctor
    (moduleRings X.toRingedSpace) U).mapDerivedCategory.mapIso e.symm) ≪≫ eK⟩⟩

private theorem perfect_shift (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    {E : schemeDerivedCategory X} (hE : Scheme.IsPerfect X E) (n : ℤ) :
    Scheme.IsPerfect X (E⟦n⟧) := by
  intro x
  obtain ⟨U, hx, K, ⟨⟨a, b, hb⟩, hf⟩, ⟨eK⟩⟩ := hE x
  refine ⟨U, hx, K⟦n⟧, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨a - n, b - n, fun i hi ↦ ?_⟩
    exact hb (i + n) (by omega)
  · exact fun i ↦ hf (i + n)
  · let F := (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).mapDerivedCategory
    exact ⟨(F.commShiftIso n).app E ≪≫ (shiftFunctor _ n).mapIso eK ≪≫
      ((DerivedCategory.Q.commShiftIso n).app K).symm⟩

private theorem perfect_test_detection (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (htri : (schemeDerivedQCohProperty X).IsTriangulated)
    {S : Type u} (G : S → schemeDerivedQCohCategory X)
    (hperfect : ∀ s, Scheme.IsPerfect X (G s).obj)
    (hrep : ∀ P : schemeDerivedQCohCategory X, Scheme.IsPerfect X P.obj →
      ∃ s, Nonempty (P ≅ G s)) :
    ∀ (A B : schemeDerivedQCohCategory X) (g : A ⟶ B),
      (∀ s, Function.Bijective (fun a : G s ⟶ A ↦ a ≫ g)) → IsIso g := by
  classical
  let := htri
  let := derivedQCohDirectSums X
  have hgen := schemeDerivedQCoh_representatives_generate X htri G hrep
    (derivedQCohPerfectGeneration X)
  intro A B g hg
  have htests (P : schemeDerivedQCohCategory X) (hP : Scheme.IsPerfect X P.obj) :
      Function.Bijective (fun a : P ⟶ A ↦ a ≫ g) := by
    obtain ⟨s, ⟨e⟩⟩ := hrep P hP
    constructor
    · intro a b hab
      apply (cancel_epi e.inv).mp
      apply (hg s).injective
      simpa only [Category.assoc] using congrArg (fun k ↦ e.inv ≫ k) hab
    · intro b
      obtain ⟨a, ha⟩ := (hg s).surjective (e.inv ≫ b)
      refine ⟨e.hom ≫ a, ?_⟩
      change (e.hom ≫ a) ≫ g = b
      change a ≫ g = e.inv ≫ b at ha
      rw [Category.assoc, ha, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  have hshift (P : schemeDerivedQCohCategory X) (hP : Scheme.IsPerfect X P.obj)
      (n : ℤ) : Scheme.IsPerfect X (P⟦n⟧).obj := by
    exact perfect_of_iso X (((schemeDerivedQCohProperty X).ι.commShiftIso n).app P).symm
      (perfect_shift X hP n)
  have hbijshift (P : schemeDerivedQCohCategory X) (hP : Scheme.IsPerfect X P.obj)
      (n : ℤ) : Function.Bijective (fun a : P ⟶ A⟦n⟧ ↦ a ≫ g⟦n⟧') := by
    let adj := (shiftEquiv' (schemeDerivedQCohCategory X) (-n) n (neg_add_cancel n)).toAdjunction
    let eA := adj.homEquiv P A
    let eB := adj.homEquiv P B
    have h := htests (P⟦-n⟧) (hshift P hP (-n))
    have he : (fun a : P ⟶ A⟦n⟧ ↦ a ≫ g⟦n⟧') =
        eB ∘ (fun a : P⟦-n⟧ ⟶ A ↦ a ≫ g) ∘ eA.symm := by
      funext a
      change a ≫ (shiftEquiv' (schemeDerivedQCohCategory X) (-n) n
        (neg_add_cancel n)).inverse.map g =
        adj.homEquiv P B ((adj.homEquiv P A).symm a ≫ g)
      rw [adj.homEquiv_naturality_right]
      simp
    rw [he]
    exact eB.bijective.comp (h.comp eA.symm.bijective)
  obtain ⟨D, d, δ, hd⟩ := Pretriangulated.distinguished_cocone_triangle g
  have hD (P : schemeDerivedQCohCategory X) (hP : Scheme.IsPerfect X P.obj)
      (a : P ⟶ D) : a = 0 := by
    have hδ : a ≫ δ = 0 := by
      apply (hbijshift P hP 1).1
      have hzero := Pretriangulated.comp_distTriang_mor_zero₃₁ _ hd
      change δ ≫ (shiftFunctor _ (1 : ℤ)).map g = 0 at hzero
      simp only [Category.assoc, hzero, comp_zero, zero_comp]
    obtain ⟨b, hb⟩ := Pretriangulated.Triangle.coyoneda_exact₃ _ hd a hδ
    obtain ⟨b', hb'⟩ := (htests P hP).2 b
    have hgd : g ≫ d = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ _ hd
    change a = b ≫ d at hb
    rw [hb, ← hb', Category.assoc, hgd, comp_zero]
  have hDshift (s : S) (n : ℤ) (a : G s ⟶ D⟦n⟧) : a = 0 := by
    let adj := (shiftEquiv' (schemeDerivedQCohCategory X) (-n) n
      (neg_add_cancel n)).toAdjunction
    have : (shiftEquiv' (schemeDerivedQCohCategory X) (-n) n
        (neg_add_cancel n)).functor.Additive :=
      inferInstanceAs (shiftFunctor _ (-n)).Additive
    have : (shiftEquiv' (schemeDerivedQCohCategory X) (-n) n
        (neg_add_cancel n)).inverse.Additive :=
      inferInstanceAs (shiftFunctor _ n).Additive
    apply (adj.homEquiv (G s) D).symm.injective
    rw [hD ((G s)⟦-n⟧) (hshift (G s) (hperfect s) (-n))
      ((adj.homEquiv (G s) D).symm a)]
    exact (adj.homAddEquiv_symm_zero _ _).symm
  have hzD : IsZero D := by
    by_contra hn
    obtain ⟨n, a, ha⟩ := hgen D hn
    apply ha
    apply Sigma.hom_ext
    intro s
    simpa only [comp_zero] using hDshift s n (Sigma.ι G s ≫ a)
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hd).mp hzD

/-- The right adjoint of proper, flat, finitely presented derived direct image commutes
with every set-indexed direct sum. The natural isomorphism `hF` identifies `F` with the
restriction of the shared ambient `schemeDerivedDirectImage f` to quasi-coherent objects.
Source: Stacks Project, Duality for Schemes, Lemma 48.12.1, Section Tag 0E4H
(blueprint: lem-sc-proper-flat-right-adjoint-direct-sums).

Proof:
1. Properness over qcqs Y makes X qcqs. For every perfect P on X, apply
   `lem-pc-proper-support-perfect-direct-image` with E = P and G = O_X in degree zero.
   O_X is finitely presented and flat over Y, with proper support X, so Rf_*P is perfect.
   By `lem-pc-perfect-object-compact` on Y, Hom(Rf_*P, -) commutes with direct sums.
2. For a family K_i on Y, let v be the canonical map from the sum of a(K_i) to
   a of the sum of K_i. Adjunction identifies Hom(P, a(-)) with Hom(Rf_*P, -).
   Compactness of P (`lem-pc-perfect-object-compact` on X) and Step 1 show that
   Hom(P, v) is an isomorphism for every perfect P.
3. The cone C of v has Hom(P[n], C) = 0 for every perfect P and integer n, by the
   long exact Hom sequence. The objects A with Hom(A[n], C) = 0 for all n form a class
   closed under shifts, cones, retracts and arbitrary sums and containing the perfects.
   By `lem-pc-derived-qcoh-perfect-generation`, this class contains every object,
   in particular C. Thus its identity is zero, C is zero, and v is an isomorphism. -/
theorem proper_flat_rightAdjoint_preservesDirectSums
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (F : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (hF : F ⋙ ObjectProperty.ι (schemeDerivedQCohProperty Y) ≅
      ObjectProperty.ι (schemeDerivedQCohProperty X) ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X) (adj : F ⊣ a) :
    ∀ I : Type u, PreservesColimitsOfShape (Discrete I) a := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let := Classical.choice (nonempty_derivedOpenLocalization X)
  let := Classical.choice (nonempty_derivedOpenLocalization Y)
  let : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
  let : HasCoproducts.{u} (schemeDerivedQCohCategory Y) := derivedQCohDirectSums Y
  have htri : (schemeDerivedQCohProperty X).IsTriangulated := by
    simpa using (supported_perfect_generator X Set.univ isClosed_univ (by simp)).1
  obtain ⟨S, G, hperfect, hrep⟩ := Scheme.exists_perfectComplex_representatives X
  have himages (s : S) : Scheme.IsPerfect Y (F.obj (G s)).obj := by
    apply perfect_of_iso Y (hF.app (G s)).symm
    exact properFlat_derivedDirectImage_perfect f (G s).obj (hperfect s)
  have : F.IsLeftAdjoint := adj.isLeftAdjoint
  have : HasFiniteCoproducts (schemeDerivedQCohCategory X) :=
    hasFiniteCoproducts_of_hasCoproducts _
  have : HasFiniteBiproducts (schemeDerivedQCohCategory X) :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  have : HasBinaryBiproducts (schemeDerivedQCohCategory X) :=
    hasBinaryBiproducts_of_finite_biproducts _
  have : F.Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
    exact Functor.additive_of_preservesBinaryBiproducts F
  exact compact_tests_small F a adj S G
    (fun s ↦ ⟨perfectObjectCompact X (G s) (hperfect s),
      perfectObjectCompact Y (F.obj (G s)) (himages s)⟩)
    (perfect_test_detection X htri G hperfect hrep)

end AlgebraicGeometry
