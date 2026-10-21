/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q60, Q6
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts
import Sheaf.Paper.QcqsProperHullTailBound
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Proper pushforward and ambient coproducts over a qcqs base

Source: blueprint main-20261015, sec-six-functors-basics,
`det-sf-comp-coherence-refinement.proof.md`, (2), first paragraph.
(blueprint: lem-sfb-qcqs-proper-localizing-coproducts)

`PreservesColimit (Discrete.functor L)` expresses invertibility of the canonical
ambient coproduct comparison induced by the images of the coprojections. Ambient
coproducts exist by the Grothendieck derived-coproduct theorem, including for the
empty family. This formulation is independent of the choices of coproduct objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- The two truncation helpers follow EllAdicProperLocalizingCoproducts,
-- without importing its coefficient-specific geometric statements.
private theorem coproduct_isGE
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (K : I → DerivedCategory A) (a : ℤ)
    (hK : ∀ i, (K i).IsGE a) : (∐ K).IsGE a := by
  apply (DerivedCategory.isGE_iff (∐ K) a).2
  intro q hq
  exact (isColimitOfPreserves (DerivedCategory.homologyFunctor A q)
    (coproductIsCoproduct K)).isZero_pt
    (Functor.isZero _ fun i ↦ (DerivedCategory.isGE_iff (K i.as) a).1 (hK i.as) q hq)

private theorem truncGE_preservesCoproducts
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (a : ℤ) :
    PreservesColimitsOfShape (Discrete I) ((DerivedCategory.TStructure.t (C := A)).truncGE a) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := t.truncGE a
  let π := t.truncGEπ a
  have hK (K : I → DerivedCategory A) : PreservesColimit (Discrete.functor K) T := by
    let L := fun i ↦ T.obj (K i)
    have : (∐ L).IsGE a := coproduct_isGE L a (fun i ↦ inferInstance)
    let f : ∐ K ⟶ ∐ L := Sigma.desc (fun i ↦ π.app (K i) ≫ Sigma.ι L i)
    let r : T.obj (∐ K) ⟶ ∐ L := t.descTruncGE f a
    let c := sigmaComparison T K
    have hc : IsIso c := by
      refine ⟨⟨r, ?_, ?_⟩⟩
      · apply Sigma.hom_ext
        intro i
        change Sigma.ι L i ≫ (c ≫ r) = Sigma.ι L i ≫ 𝟙 _
        rw [← Category.assoc, ι_comp_sigmaComparison]
        apply t.from_truncGE_obj_ext
        simp only [Category.comp_id]
        rw [← Category.assoc]
        change (π.app (K i) ≫ T.map (Sigma.ι K i)) ≫ r =
          π.app (K i) ≫ Sigma.ι L i
        rw [← π.naturality (Sigma.ι K i)]
        change (Sigma.ι K i ≫ (t.truncGEπ a).app (∐ K)) ≫ t.descTruncGE f a = _
        rw [Category.assoc, t.π_descTruncGE, Sigma.ι_desc]
      · apply t.from_truncGE_obj_ext
        dsimp only [r]
        rw [← Category.assoc, t.π_descTruncGE]
        apply Sigma.hom_ext
        intro i
        change Sigma.ι K i ≫ f ≫ c = Sigma.ι K i ≫ π.app (∐ K) ≫ 𝟙 _
        calc
          _ = π.app (K i) ≫ (Sigma.ι L i ≫ c) := by simp [f]
          _ = π.app (K i) ≫ T.map (Sigma.ι K i) := by
            rw [ι_comp_sigmaComparison]
          _ = _ := by simpa using (π.naturality (Sigma.ι K i)).symm
    exact PreservesCoproduct.of_iso_comparison T K
  let : ∀ K : I → DerivedCategory A, PreservesColimit (Discrete.functor K) T := hK
  exact preservesColimitsOfShape_of_discrete T


/-- Proper pushforward preserves ambient small coproducts of objects in the localizing
hull of bounded constructible finite-Tor complexes, over an arbitrary qcqs base.

Source: blueprint main-20261015, `det-sf-comp-coherence-refinement.proof.md`, (2),
first paragraph (blueprint: lem-sfb-qcqs-proper-localizing-coproducts).

Proof plan:
1. The closed monoidal Grothendieck theorem for sheaves and the module-object theorem
   `lem-sfb-modobj-grothendieck` make the source and target module categories
   Grothendieck abelian. `lem-kun-grothendieck-derived-coproducts` gives ordinary
   ambient coproducts of unbounded complexes, with their specified coprojections.
2. Exactness of coproducts gives their commutation with cohomology and good lower
   truncations (`def-kun-truncations`), including the natural truncation maps.
3. Properness implies finite type and quasi-compactness, and separatedness implies
   quasi-separatedness (`lem-pc-separated-quasi-separated`). Apply
   `lem-sfb-adic-proper-bounded-below-coproducts` to the family truncated below a
   single integer a. This gives the invertible comparison for that family.
4. Choose c from `lem-sfb-qcqs-proper-hull-tail-bound`. In output degree n put
   a = n - c. The standard truncation triangle and the triangulated total right
   derived functor (`lem-pc-right-derived-functor-triangulated`) show that the map
   from K to its lower truncation induces an isomorphism on H^n after pushforward:
   the lower tail has vanishing H^n and H^(n+1). Use the long exact sequence
   `lem-sf-derived-homology-long-exact`. Apply this to each L_t and to their sum,
   which lies in the hull. The truncations need not themselves lie in the hull.
5. The square comparing the original family with its lower truncations commutes,
   by naturality of the truncation map, tested on every coprojection. On H^n both
   vertical maps are invertible by steps 2 and 4, and the bottom map by step 3.
   Thus the original comparison is invertible on every cohomology object.
   `lem-weil-pbc-unbounded-derived-iso-cohomology` detects its invertibility.
6. For the empty family both sums are zero and triangulated pushforward preserves
   zero. The cutoff depends on n, so no common bound on the original family and
   no completeness property of its ordinary ambient sum have been assumed. -/
theorem qcqs_proper_localizing_preservesCoproduct
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {S X Y : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (q : Y ⟶ S) [IsProper q] (f : X ⟶ Y) [IsProper f]
    (I : Type (u + 1))
    (L : I → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hL : ∀ t : I, localizingClosureOfSize.{u + 1}
      (constantModelBoundedConstructible Λ X ⊓
        fun K ↦ DerivedCategory.finiteTorAmplitude _ K) (L t)) :
    PreservesColimit (Discrete.functor L) (moduleObjectDerivedPushforward Λ f) := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)
  let D := Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj Λ Y)
  let F : DerivedCategory C ⥤ DerivedCategory D := (lowerStar Λ f).rightDerivedFunctor
  have : HasColimitsOfSize.{u + 1, u + 1} C := IsGrothendieckAbelian.hasColimits C
  have : HasColimitsOfSize.{u + 1, u + 1} D := IsGrothendieckAbelian.hasColimits D
  have : HasCoproducts.{u + 1} C := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  have : HasCoproducts.{u + 1} D := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  have : HasCoproducts.{u + 1} (DerivedCategory C) := derived_hasCoproducts
  have : HasCoproducts.{u + 1} (DerivedCategory D) := derived_hasCoproducts
  let Q := localizingClosureOfSize.{u + 1}
    (constantModelBoundedConstructible Λ X ⊓
      fun K ↦ DerivedCategory.finiteTorAmplitude _ K)
  -- The tail theorem uses the hull closed under the larger object-universe sums.
  -- Its defining properties in particular hold for the specified smaller sums.
  have hmem (K : DerivedCategory C) (hK : Q K) : localizingClosureProEtale Λ X K := by
    intro P hP hgen
    apply hK P ⟨hP.1, hP.2.1, ?_⟩ hgen
    intro J E hE hEobj
    let : P.IsClosedUnderIsomorphisms := hP.2.1
    let : P.IsClosedUnderColimitsOfShape (Discrete (ULift.{u + 2} J)) := by
      apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
      rintro _ ⟨E', hE'⟩
      exact hP.2.2 E' inferInstance (fun j ↦ hE' ⟨j⟩)
    let : P.IsClosedUnderColimitsOfShape (Discrete J) :=
      ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
        (Discrete.equivalence (Equiv.ulift : ULift.{u + 2} J ≃ J))
    exact P.prop_of_isColimit (colimit.isColimit E) (fun j ↦ hEobj j.as)
  obtain ⟨c, htail⟩ := exists_uniform_lowerTail_bound_of_isProper ℓ Λ hΛ q f
  have hc (q : ℤ) (K : DerivedCategory C) (hK : Q K) :
      IsIso ((F ⋙ DerivedCategory.homologyFunctor D q).map
        ((DerivedCategory.TStructure.t.truncGEπ (q - (c : ℤ))).app K)) := by
    let t := DerivedCategory.TStructure.t (C := C)
    let T := F.mapTriangle.obj ((t.triangleLEGE (q - (c : ℤ) - 1) (q - (c : ℤ)) (by omega)).obj K)
    have hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles :=
      F.map_distinguished _
        (t.triangleLEGE_distinguished (q - (c : ℤ) - 1) (q - (c : ℤ)) (by omega) K)
    exact DerivedCategory.isIso_homologyMap_mor₂ T hT q (q + 1) rfl
      (htail _ K (hmem K hK) q (by omega))
      (htail _ K (hmem K hK) (q + 1) (by omega))
  have hA (A : I → DerivedCategory C) (hA : ∀ i, Q (A i)) :
      PreservesColimit (Discrete.functor A) F := by
    have hS : Q (∐ A) := by
      intro P hP hgen
      exact hP.2.2 (Discrete.functor A) inferInstance (fun i ↦ hA i P hP hgen)
    have hcomp : IsIso (sigmaComparison F A) := by
      apply (DerivedCategory.isIso_iff D _).2
      intro q
      let H := DerivedCategory.homologyFunctor D q
      let G := F ⋙ H
      let t := DerivedCategory.TStructure.t (C := C)
      let T := t.truncGE (q - (c : ℤ))
      let π := t.truncGEπ (q - (c : ℤ))
      have : PreservesColimitsOfShape (Discrete I) T :=
        truncGE_preservesCoproducts (q - (c : ℤ))
      have hbound : ∀ i, (T.obj (A i)).IsGE (q - (c : ℤ)) := fun i ↦ inferInstance
      have : PreservesColimit (Discrete.functor (fun i ↦ T.obj (A i))) F :=
        condensed_boundedBelow_preservesCoproduct Λ f I _ _ hbound
      have : PreservesColimit (Discrete.functor A ⋙ T) F :=
        preservesColimit_of_iso_diagram F
          (Discrete.natIso (fun _ ↦ Iso.refl _) :
            Discrete.functor (fun i ↦ T.obj (A i)) ≅ Discrete.functor A ⋙ T)
      have : PreservesColimit (Discrete.functor A) (T ⋙ G) := inferInstance
      let d := sigmaComparison (T ⋙ G) A
      let l := Limits.Sigma.map (fun i ↦ G.map (π.app (A i)))
      let r := G.map (π.app (∐ A))
      have hd : IsIso d := inferInstance
      have hl (i : I) : IsIso (G.map (π.app (A i))) := hc q (A i) (hA i)
      have : IsIso l := by dsimp only [l]; infer_instance
      have : IsIso r := hc q (∐ A) hS
      have square : sigmaComparison G A ≫ r = l ≫ d := by
        apply Sigma.hom_ext
        intro i
        simp only [l, d, r, ι_comp_sigmaComparison_assoc, Sigma.ι_map_assoc]
        change G.map (Sigma.ι A i) ≫ G.map (π.app (∐ A)) =
          G.map (π.app (A i)) ≫
            Sigma.ι (fun i ↦ (T ⋙ G).obj (A i)) i ≫ sigmaComparison (T ⋙ G) A
        rw [ι_comp_sigmaComparison]
        simpa only [Functor.comp_map, ← G.map_comp, Functor.id_map] using
          congrArg G.map (π.naturality (Sigma.ι A i))
      have : IsIso (sigmaComparison G A ≫ r) := by rw [square]; infer_instance
      have : IsIso (sigmaComparison G A) := IsIso.of_isIso_comp_right _ r
      have heq : sigmaComparison G A =
          sigmaComparison H (fun i ↦ F.obj (A i)) ≫ H.map (sigmaComparison F A) := by
        exact (sigmaComparison_map_desc H (fun i ↦ F.obj (A i)) _
          (fun i ↦ F.map (Sigma.ι A i))).symm
      have : IsIso (sigmaComparison H (fun i ↦ F.obj (A i)) ≫
          H.map (sigmaComparison F A)) := by rw [← heq]; infer_instance
      exact IsIso.of_isIso_comp_left (sigmaComparison H (fun i ↦ F.obj (A i))) _
    exact PreservesCoproduct.of_iso_comparison F A
  exact hA L hL

end AlgebraicGeometry.ProEtale.CondensedRing
