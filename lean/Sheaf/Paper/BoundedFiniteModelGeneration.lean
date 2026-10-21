/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.NoetherianSpace
import Sheaf.Paper.FiniteModelStratumFiltration
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Finite generation from constant-model strata

Source: Stacks Project, Tags 08J5 and 09Y5; finite-stratum and Postnikov assembly
extracted from Bhatt--Scholze, Lemma 6.3.14 and Proposition 6.8.11(3)
(blueprint: lem-sfb-bounded-finite-model-generation).

The finite witness is a list of derived objects ending at K up to isomorphism.
Each entry is zero, a specified stratum generator, an integer shift of an earlier
entry up to isomorphism, or an extension of two strictly earlier entries.
The ordinary uncompleted derived category and arbitrary condensed coefficients are used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section FiniteConstructions

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

private def constructionStep (G P : ObjectProperty D) (X : D) : Prop :=
  IsZero X ∨ G X ∨
    (∃ (A : D) (n : ℤ), P A ∧ Nonempty (X ≅ A⟦n⟧)) ∨
    ∃ (A B : D), P A ∧ P B ∧
      ∃ (f : A ⟶ X) (g : X ⟶ B) (h : B ⟶ A⟦(1 : ℤ)⟧),
        Pretriangulated.Triangle.mk f g h ∈ distTriang D

private lemma constructionStep_mono {G P Q : ObjectProperty D} (h : P ≤ Q)
    {X : D} (hX : constructionStep G P X) : constructionStep G Q X := by
  rcases hX with hX | hX | ⟨A, n, hA, e⟩ | ⟨A, B, hA, hB, f, g, k, hk⟩
  · exact Or.inl hX
  · exact Or.inr (Or.inl hX)
  · exact Or.inr (Or.inr (Or.inl ⟨A, n, h A hA, e⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨A, B, h A hA, h B hB, f, g, k, hk⟩))

private def constructionCertificate (G : ObjectProperty D) {n : ℕ}
    (F : Fin n → D) : Prop :=
  ∀ r, constructionStep G (fun A ↦ ∃ i, i < r ∧ F i = A) (F r)

private lemma certificate_embed {G : ObjectProperty D} {n m : ℕ}
    {F : Fin n → D} {H : Fin m → D} (hF : constructionCertificate G F)
    (e : Fin n → Fin m) (he : StrictMono e) (h : ∀ i, H (e i) = F i) (r : Fin n) :
    constructionStep G (fun A ↦ ∃ i, i < e r ∧ H i = A) (H (e r)) := by
  rw [h r]
  apply constructionStep_mono _ (hF r)
  rintro A ⟨i, hi, rfl⟩
  exact ⟨e i, he hi, h i⟩

private lemma certificate_append {G : ObjectProperty D} {n m : ℕ}
    {F : Fin n → D} {H : Fin m → D}
    (hF : constructionCertificate G F) (hH : constructionCertificate G H) :
    constructionCertificate G (Fin.append F H) := by
  intro r
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) r
  · exact certificate_embed hF (Fin.castAdd m) (fun _ _ h ↦ h)
      (fun i ↦ Fin.append_left F H i) i
  · exact certificate_embed hH (Fin.natAdd n)
      (fun _ _ h ↦ by simpa only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left] using h)
      (fun i ↦ Fin.append_right F H i) i

private lemma certificate_snoc {G : ObjectProperty D} {n : ℕ}
    {F : Fin n → D} {X : D} (hF : constructionCertificate G F)
    (hX : constructionStep G (fun A ↦ ∃ i, F i = A) X) :
    constructionCertificate G (Fin.snoc (α := fun _ ↦ D) F X) := by
  intro r
  refine Fin.lastCases ?_ (fun i ↦ ?_) r
  · simp only [Fin.snoc_last]
    apply constructionStep_mono _ hX
    rintro A ⟨i, rfl⟩
    exact ⟨i.castSucc, Fin.castSucc_lt_last i, by simp⟩
  · exact certificate_embed hF Fin.castSucc (fun _ _ h ↦ h)
      (fun i ↦ by simp) i

private def finitelyBuilt (G : ObjectProperty D) : ObjectProperty D := fun X ↦
  ∃ (n : ℕ) (F : Fin n → D), constructionCertificate G F ∧
    ∃ i, Nonempty (F i ≅ X)

private lemma built_of_step {G : ObjectProperty D} {X : D}
    (hX : constructionStep G ⊥ X) : finitelyBuilt G X := by
  refine ⟨1, fun _ ↦ X, fun r ↦ constructionStep_mono bot_le hX, 0, ⟨Iso.refl X⟩⟩

private lemma built_iso {G : ObjectProperty D} {X Y : D} (e : X ≅ Y)
    (hX : finitelyBuilt G X) : finitelyBuilt G Y := by
  obtain ⟨n, F, hF, i, ⟨ei⟩⟩ := hX
  exact ⟨n, F, hF, i, ⟨ei ≪≫ e⟩⟩

private lemma built_shift {G : ObjectProperty D} {X : D}
    (hX : finitelyBuilt G X) (n : ℤ) : finitelyBuilt G (X⟦n⟧) := by
  obtain ⟨m, F, hF, i, ⟨e⟩⟩ := hX
  refine ⟨m + 1, Fin.snoc F (X⟦n⟧), certificate_snoc hF ?_, Fin.last m, ?_⟩
  · exact Or.inr (Or.inr (Or.inl
      ⟨F i, n, ⟨i, rfl⟩, ⟨(shiftFunctor D n).mapIso e.symm⟩⟩))
  · simp only [Fin.snoc_last]
    exact ⟨Iso.refl _⟩

private lemma built_extension {G : ObjectProperty D}
    (T : Pretriangulated.Triangle D) (hT : T ∈ distTriang D)
    (hA : finitelyBuilt G T.obj₁) (hB : finitelyBuilt G T.obj₃) :
    finitelyBuilt G T.obj₂ := by
  obtain ⟨n, F, hF, i, ⟨eA⟩⟩ := hA
  obtain ⟨m, H, hH, j, ⟨eB⟩⟩ := hB
  let L := Fin.append F H
  have hL := certificate_append hF hH
  have hstep : constructionStep G (fun A ↦ ∃ i, L i = A) T.obj₂ := by
    refine Or.inr (Or.inr (Or.inr ⟨F i, H j,
      ⟨i.castAdd m, Fin.append_left F H i⟩,
      ⟨j.natAdd n, Fin.append_right F H j⟩,
      eA.hom ≫ T.mor₁, T.mor₂ ≫ eB.inv,
      eB.hom ≫ T.mor₃ ≫ eA.inv⟦(1 : ℤ)⟧', ?_⟩))
    apply Pretriangulated.isomorphic_distinguished _ hT
    exact Pretriangulated.Triangle.isoMk _ _ eA (Iso.refl _) eB
      (by simp) (by simp) (by simp)
  refine ⟨n + m + 1, Fin.snoc L T.obj₂, certificate_snoc hL hstep,
    Fin.last (n + m), ?_⟩
  simp only [Fin.snoc_last]
  exact ⟨Iso.refl _⟩

private lemma built_mem {G C : ObjectProperty D}
    [C.IsClosedUnderIsomorphisms] [C.IsTriangulated]
    (hG : G ≤ C) {X : D} (hX : finitelyBuilt G X) : C X := by
  obtain ⟨n, F, hF, i, ⟨e⟩⟩ := hX
  have hmem : ∀ r, C (F r) := by
    intro r
    induction r using Fin.strong_induction_on with
    | h r ih =>
      rcases hF r with hz | hg | ⟨A, k, ⟨j, hj, hA⟩, ⟨he⟩⟩ |
        ⟨A, B, ⟨j, hj, hA⟩, ⟨l, hl, hB⟩, f, g, k, hk⟩
      · exact C.prop_of_isZero hz
      · exact hG _ hg
      · subst A
        exact C.prop_of_iso he.symm (C.le_shift k _ (ih j hj))
      · subst A B
        exact C.ext_of_isTriangulatedClosed₂ _ hk (ih j hj) (ih l hl)
  exact C.prop_of_iso e (hmem i)

end FiniteConstructions

private def stratumGenerator
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  fun K ↦ ∃ (V S : Scheme.{u}) (v : V ⟶ X), Exists fun [IsOpenImmersion v] ↦
    ∃ t : S ⟶ V, IsClosedImmersion t ∧ IsReduced S ∧
    ∃ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S),
      HasFiniteConstantLocalModel Λ S L ∧
      Nonempty (K ≅ (DerivedCategory.singleFunctor _ 0).obj
        ((openImmersionLowerShriek Λ v).obj ((lowerStar Λ t).obj L)))

private lemma constructible_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {F H : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : F ≅ H) (hF : IsConstantModelConstructible Λ X F) :
    IsConstantModelConstructible Λ X H := by
  classical
  have local_model {Y : Scheme.{u}}
      {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ Y M) :
      HasFiniteConstantLocalModel Λ Y N := by
    obtain ⟨U, hU⟩ := hM
    refine ⟨U, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
    exact ⟨P, hP, ⟨(upperStar Λ (U.f i)).mapIso e.symm ≪≫ eP⟩⟩
  unfold IsConstantModelConstructible at hF ⊢
  split_ifs at hF ⊢
  · obtain ⟨S, hS⟩ := hF
    exact ⟨S, fun a ↦ local_model ((upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  · intro U hU
    obtain ⟨S, hS⟩ := hF U hU
    exact ⟨S, fun a ↦ local_model
      ((upperStar Λ (S.immersion a)).mapIso ((upperStar Λ U.ι).mapIso e)) (hS a)⟩

private lemma sheaf_finitelyBuilt
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : IsConstantModelConstructible Λ X F) :
    finitelyBuilt (stratumGenerator Λ X) ((DerivedCategory.singleFunctor _ 0).obj F) := by
  classical
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let single := DerivedCategory.singleFunctor A 0
  obtain ⟨r, V, hV, hV0, hVr, S, t, ht, hmodel, hqc, hqc', hmono,
    hzero, hiso, d, hd, hdmono, he⟩ := exists_finiteModelStratumFiltration Λ X F hF
  have hb (k : Fin (r + 1)) : finitelyBuilt (stratumGenerator Λ X)
      (single.obj ((openFiltrationPiece Λ (V k)).obj F)) := by
    induction k using Fin.induction with
    | zero => exact built_of_step (Or.inl (single.map_isZero hzero))
    | succ k ih =>
      have := hdmono k
      let f := (d k).app F
      have hses : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
        { exact := ShortComplex.exact_cokernel f }
      have hquot : finitelyBuilt (stratumGenerator Λ X) (single.obj (cokernel f)) := by
        obtain ⟨e⟩ := he k
        let ev := (evaluation A A).obj F
        let eq : cokernel f ≅ (openFiltrationStratum Λ (V k.succ) (t k)).obj F :=
          (PreservesCokernel.iso ev (d k)).symm ≪≫ ev.mapIso e
        have := (ht k).1
        have := (ht k).2.1
        apply built_of_step
        exact Or.inr (Or.inl ⟨(V k.succ).toScheme, S k, (V k.succ).ι,
          inferInstance, t k, inferInstance, inferInstance,
          (upperStar Λ (t k)).obj ((upperStar Λ (V k.succ).ι).obj F),
          hmodel k, ⟨single.mapIso eq⟩⟩)
      exact built_extension hses.singleTriangle hses.singleTriangle_distinguished ih hquot
  have := hiso
  exact built_iso (single.mapIso (asIso ((openFiltrationCounit Λ
    (V (Fin.last r))).app F))) (hb (Fin.last r))

/-- Every bounded constant-model constructible complex lies in any isomorphism-closed
class containing zero and the indicated stratum sheaves and closed under integer shifts
and extensions. There is an explicit finite construction using precisely these operations.
Here `C.IsTriangulated` packages ContainsZero, IsStableUnderShift and
IsTriangulatedClosed₂; with isomorphism closure its last condition is exactly extension
closure in the middle vertex, not closure under retracts or infinite coproducts.

Source: Stacks Tags 08J5, 09Y5; Bhatt--Scholze Lemma 6.3.14 and Proposition 6.8.11(3),
finite-stratum/Postnikov assembly (blueprint: lem-sfb-bounded-finite-model-generation).

Proof plan (the five steps of the node):
1. For each constructible sheaf F, `lem-sfb-finite-model-stratum-filtration` supplies a
finite filtration from zero to F whose quotients are v_! t_* L with S reduced closed
in V and L having a finite constant local model. These are exactly the assumed generators.
2. Place each filtration sequence in degree zero. By
`lem-weil-pbc-complex-ses-triangle` it gives a distinguished triangle. Induction on the
finite filtration length, starting with zero, puts F[0] in C. Concatenating the finite
witnesses for the two outer vertices and appending the middle vertex records each step.
3. For K with cohomology in [a,b], set T_q = tau_le q K on a cochain representative.
By `lem-weil-pbc-truncation-cohomology`, T_(a-1) is acyclic and T_b -> K is a
quasi-isomorphism. The localization `def-weil-abstract-derived-category` therefore
identifies them with zero and K, respectively; no infinite truncation tower is used.
4. For q = a,...,b, `lem-weil-pbc-truncation-triangle` supplies the triangle
T_(q-1) -> T_q -> H^q(K)[-q] -> T_(q-1)[1]. Steps 1--2 construct H^q(K)[0]. Append
its integer shift, then this extension. Finite induction and the final isomorphism
put K in C and produce the displayed finite list.
5. The finitely many sheaf filtration lengths and the b-a+1 Postnikov steps have finite
sum. An acyclic K needs only a zero object. The empty scheme permits length zero.
No argument uses a field, finite Tor amplitude, or torsion-freeness, so arbitrary
commutative condensed rings and integral torsion local models are included. -/
theorem bounded_finiteModel_generation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (C : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    [C.IsClosedUnderIsomorphisms] [C.IsTriangulated]
    (hgen : ∀ (V S : Scheme.{u}) (v : V ⟶ X) [IsOpenImmersion v]
      (t : S ⟶ V) [IsClosedImmersion t] [IsReduced S]
      (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)),
      HasFiniteConstantLocalModel Λ S L →
        C ((DerivedCategory.singleFunctor _ 0).obj
          ((openImmersionLowerShriek Λ v).obj ((lowerStar Λ t).obj L))))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : constantModelBoundedConstructible Λ X K) :
    C K ∧ ∃ (N : ℕ) (F : Fin (N + 1) → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      Nonempty (F (Fin.last N) ≅ K) ∧ ∀ r : Fin (N + 1),
        IsZero (F r) ∨
        (∃ (V S : Scheme.{u}) (v : V ⟶ X), Exists fun [IsOpenImmersion v] ↦
          ∃ t : S ⟶ V, IsClosedImmersion t ∧ IsReduced S ∧
          ∃ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S),
            HasFiniteConstantLocalModel Λ S L ∧
            Nonempty (F r ≅ (DerivedCategory.singleFunctor _ 0).obj
              ((openImmersionLowerShriek Λ v).obj
                ((lowerStar Λ t).obj L)))) ∨
        (∃ (i : Fin (N + 1)) (n : ℤ), i < r ∧ Nonempty (F r ≅ (F i) ⟦n⟧)) ∨
        (∃ (i j : Fin (N + 1)), i < r ∧ j < r ∧
          ∃ (f : F i ⟶ F r) (g : F r ⟶ F j) (h : F j ⟶ (F i) ⟦(1 : ℤ)⟧),
            Pretriangulated.Triangle.mk f g h ∈ distTriang _) := by
  classical
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let G := stratumGenerator Λ X
  let P : ObjectProperty A := IsConstantModelConstructible Λ X
  have : (finitelyBuilt G).IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ built_iso e h⟩
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ constructible_of_iso Λ X e h⟩
  have hbuild : finitelyBuilt G K := by
    apply DerivedCategory.prop_of_bounded_of_degreewise (finitelyBuilt G)
      (fun _ hz ↦ built_of_step (Or.inl hz))
      (fun T hT h₁ h₃ ↦ built_extension T hT h₁ h₃) (fun _ ↦ P)
      (fun q F hF ↦ ?_) K hK.1 hK.2
    exact built_iso (((DerivedCategory.singleFunctors A).shiftIso (-q) q 0 (by omega)).app F)
      (built_shift (sheaf_finitelyBuilt Λ X F hF) (-q))
  refine ⟨built_mem (fun Y hY ↦ ?_) hbuild, ?_⟩
  · obtain ⟨V, S, v, hv, t, ht, hS, L, hL, ⟨e⟩⟩ := hY
    have := hv
    have := ht
    have := hS
    exact C.prop_of_iso e.symm (hgen V S v t L hL)
  · obtain ⟨n, F, hF, i, ⟨e⟩⟩ := hbuild
    -- Append a zero shift to make the last entry the desired endpoint.
    let H : Fin (n + 1) → DerivedCategory A := Fin.snoc F K
    have hH : constructionCertificate G H := certificate_snoc hF
      (Or.inr (Or.inr (Or.inl ⟨F i, 0, ⟨i, rfl⟩,
        ⟨e.symm ≪≫ ((shiftFunctorZero _ ℤ).app (F i)).symm⟩⟩)))
    refine ⟨n, H, ?_, fun r ↦ ?_⟩
    · exact ⟨by simpa [H] using Iso.refl K⟩
    · rcases hH r with hz | hg | ⟨Y, q, ⟨j, hj, hY⟩, eY⟩ |
        ⟨Y, Z, ⟨j, hj, hY⟩, ⟨l, hl, hZ⟩, f, g, k, hk⟩
      · exact Or.inl hz
      · exact Or.inr (Or.inl hg)
      · subst Y
        exact Or.inr (Or.inr (Or.inl ⟨j, q, hj, eY⟩))
      · subst Y Z
        exact Or.inr (Or.inr (Or.inr ⟨j, l, hj, hl, f, g, k, hk⟩))

end AlgebraicGeometry.ProEtale.CondensedRing
