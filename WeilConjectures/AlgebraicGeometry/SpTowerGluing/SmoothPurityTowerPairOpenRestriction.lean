/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

/-! # Restriction of representing pairs to source opens

Source: latest smooth-purity blueprint, Local pairs, Gluing and Uniformity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

private theorem finite_ctf_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L)
    (hK : spFiniteConstructibleTor T A K) : spFiniteConstructibleTor T A L := by
  obtain ⟨⟨a, b, hab, hb⟩, hc, ht⟩ := hK
  let Q : ObjectProperty (proEtaleDerivedCategory T A) := fun K ↦
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ i).obj K)} ∧
      ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T A
        ((DerivedCategory.homologyFunctor _ i).obj K)
  have hQ : Q.IsClosedUnderIsomorphisms :=
    (proEtale_bounded_constructible_isTriangulated T A).1
  let _ := hQ
  have hs : Q K := by
    refine ⟨(Set.finite_Icc a b).subset ?_, hc⟩
    intro i hi
    exact ⟨le_of_not_gt (fun ha ↦ hi (hb i (.inl ha))),
      le_of_not_gt (fun hb' ↦ hi (hb i (.inr hb')))⟩
  have hsL := Q.prop_of_iso e hs
  refine ⟨⟨a, b, hab, ?_⟩, hsL.2, ?_⟩
  · intro i hi
    exact (hb i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  · obtain ⟨c, d, ht⟩ := ht
    exact ⟨c, d, tor_of_iso T A e ht⟩

private theorem tower_ctf_of_iso (T : Scheme.{u})
    {K L : spDerivedCoefficientTowers l E T (q.abelian T)} (e : K ≅ L)
    (hK : spConstructibleTorTowers l E T (q.abelian T) K) :
    spConstructibleTorTowers l E T (q.abelian T) L := by
  refine ⟨fun n ↦ finite_ctf_of_iso T _
    ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).mapIso e) (hK.1 n), ?_⟩
  obtain ⟨a, b, c, d, hab, hcd, h⟩ := hK.2
  refine ⟨a, b, c, d, hab, hcd, fun n ↦ ⟨?_, ?_⟩⟩
  · intro i hi
    exact ((h n).1 i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso
        ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).mapIso e)).symm
  · exact tor_of_iso T _
      ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).mapIso e) (h n).2

/-- Open extension and restriction preserve the full constructible finite-Tor categories.
Source: latest blueprint, Local pairs, restriction through the supplied calculus
(blueprint: lem-sp-tower-pair-open-restriction).

Proof. A finite-type source over the field is Noetherian, so every open is quasi-compact.
Apply the etale preservation fields of the calculus to its inclusion. Transport etale
extension to open extension along openEtaleCoordinates; constructibility and each finite
uniform interval are invariant under that isomorphism. -/
theorem tower_pair_open_preserves
    (k : Type u) [Field k] (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h)
    (X : Over (Spec (.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (U : X.left.Opens) :
    (∀ M : SpTowerCalculus.C l E b q U.toScheme,
      spConstructibleTorTowers l E X.left (q.abelian X.left)
        ((SpTowerCalculus.openExtension l E b o q U.ι).obj M.obj)) ∧
    (∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E U.toScheme (q.abelian U.toScheme)
        ((SpTowerCalculus.etalePullback l E b o q U.ι).obj M.obj)) := by
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (U : Set X.left))
  let : U.toScheme.Over (Spec (.of k)) := ⟨U.ι ≫ X.hom⟩
  have : U.ι.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsSeparated (X.left ↘ Spec (.of k)) := by
    change IsSeparated X.hom
    infer_instance
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType X.hom
    infer_instance
  have : QuasiCompact (X.left ↘ Spec (.of k)) := by
    change QuasiCompact X.hom
    infer_instance
  have : IsSeparated (U.toScheme ↘ Spec (.of k)) := by
    change IsSeparated (U.ι ≫ X.hom)
    infer_instance
  have : LocallyOfFiniteType (U.toScheme ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (U.ι ≫ X.hom)
    infer_instance
  have : QuasiCompact (U.toScheme ↘ Spec (.of k)) := by
    change QuasiCompact (U.ι ≫ X.hom)
    infer_instance
  obtain ⟨hL, hR⟩ := cal.etale.etale_preserves U.ι
  refine ⟨?_, hR⟩
  intro M
  exact tower_ctf_of_iso l E b q X.left
    ((SpTowerCalculus.openEtaleCoordinates l E b o q z U.ι
      (cal.etale.etale U.ι)).app M.obj) (hL M)


private theorem restrict_representing_subcategory
    {A B D : Type*} [Category A] [Category B] [Category D]
    (P : ObjectProperty A) (Q : ObjectProperty B)
    (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R)
    (hL : ∀ M : P.FullSubcategory, Q (L.obj M.obj))
    (F : B ⥤ D) (G : A ⥤ D) (e : L ⋙ F ≅ G)
    (H : Q.FullSubcategory) (K : D) (eps : F.obj H.obj ⟶ K)
    (rep : ∀ N : Q.FullSubcategory,
      Function.Bijective (fun a : N.obj ⟶ H.obj ↦ F.map a ≫ eps))
    (M : P.FullSubcategory) :
    Function.Bijective (fun a : M.obj ⟶ R.obj H.obj ↦
      G.map a ≫ e.inv.app (R.obj H.obj) ≫ F.map (adj.counit.app H.obj) ≫ eps) := by
  let t := (adj.homEquiv M.obj H.obj).symm.trans
    (Equiv.ofBijective _ (rep ⟨L.obj M.obj, hL M⟩))
  let v := (Iso.homCongr (e.app M.obj) (Iso.refl K)).symm
  have hv : (fun a : M.obj ⟶ R.obj H.obj ↦
      G.map a ≫ e.inv.app (R.obj H.obj) ≫ F.map (adj.counit.app H.obj) ≫ eps) =
      fun a ↦ v.symm (t a) := by
    funext a
    dsimp [v, t, Iso.homCongr]
    simp only [Category.comp_id, Adjunction.homEquiv_counit, Functor.map_comp,
      Category.assoc]
    rw [e.inv.naturality_assoc]
    rfl
  rw [hv]
  exact v.symm.bijective.comp t.bijective

/-- Successive precomposition has exactly the compact-support functor of the composite.
Source: latest blueprint, Gluing, nested source opens
(blueprint: lem-sp-tower-pair-open-restriction).

Proof. Compact support depends on the open map into the same compactification and
on its proper map. The latter is unchanged. The former is i followed by j followed
by the original open map, which equals v followed by that map. Apply congruence to
the subtype of open immersions; proof irrelevance identifies its open-immersion proofs. -/
theorem compact_support_precomp_comp
    {X U W Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (j : U ⟶ X) (i : W ⟶ U) (v : W ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion v]
    (h : i ≫ j = v) :
    SpTowerCalculus.F l E b o q ((c.precomp j).precomp i) =
      SpTowerCalculus.F l E b o q (c.precomp v) := by
  let make (w : {w : W ⟶ c.Z // IsOpenImmersion w}) :=
    letI := w.property
    (SpTowerCalculus.realization l E b W (q.abelian W)).functor ⋙
      (SpTowerShriek.openD l E b (o.openOp w.val) ⋙
        SpTowerShriek.push l E b (o.geometry c.g)) ⋙
      (SpTowerCalculus.realization l E b Y (q.abelian Y)).inverse
  change make ⟨i ≫ j ≫ c.i, inferInstance⟩ = make ⟨v ≫ c.i, inferInstance⟩
  apply congrArg make
  apply Subtype.ext
  change i ≫ j ≫ c.i = v ≫ c.i
  rw [← Category.assoc, h]

/-- The actual counit of an open restriction of an ambient pair.
Source: latest blueprint, Gluing, restriction of pairs
(blueprint: def-sp-tower-open-counit-formulas). -/
def openMorphismCounit
    {X U Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (H : spDerivedCoefficientTowers l E X (q.abelian X))
    (K : spDerivedCoefficientTowers l E Y (q.abelian Y))
    (eps : (SpTowerCalculus.F l E b o q c).obj H ⟶ K)
    (j : U ⟶ X) [IsOpenImmersion j] :
    (SpTowerCalculus.F l E b o q (c.precomp j)).obj
      ((SpTowerCalculus.etalePullback l E b o q j).obj H) ⟶ K :=
  (SpTowerCalculus.openComposition l E b o q j c).inv.app _ ≫
    (SpTowerCalculus.F l E b o q c).map
      ((openAdjunction l E b o q j).counit.app H) ≫ eps

/-- An iterated local counit, transported to a fixed composite source open.
Source: latest blueprint, Gluing, overlap counits
(blueprint: def-sp-tower-open-counit-formulas). -/
def normalizedOpenCounit
    {X U W Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (j : U ⟶ X) (i : W ⟶ U) (v : W ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion v]
    (h : i ≫ j = v)
    (H : spDerivedCoefficientTowers l E U (q.abelian U))
    (K : spDerivedCoefficientTowers l E Y (q.abelian Y))
    (eps : (SpTowerCalculus.F l E b o q (c.precomp j)).obj H ⟶ K) :
    (SpTowerCalculus.F l E b o q (c.precomp v)).obj
      ((SpTowerCalculus.etalePullback l E b o q i).obj H) ⟶ K :=
  (eqToIso (compact_support_precomp_comp l E b o q c j i v h)).inv.app _ ≫
    openMorphismCounit l E b o q (c.precomp j) H K eps i

/-- Open extension preserves the full constructible finite-Tor category for every
open immersion over the field.
Source: latest smooth-purity blueprint, Gluing, open extension of tests
(blueprint: lem-sp-tower-pair-open-restriction).

Proof. The etale calculus preserves the category. Its specified comparison with
open extension transports this property through an actual derived-tower isomorphism. -/
theorem tower_open_morphism_extension_preserves
    (k : Type u) [Field k] (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h)
    (U X : Over (Spec (.of k)))
    [IsSeparated U.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left]
    (M : SpTowerCalculus.C l E b q U.left) :
    spConstructibleTorTowers l E X.left (q.abelian X.left)
      ((SpTowerCalculus.openExtension l E b o q j.left).obj M.obj) := by
  let : U.left.Over (Spec (.of k)) := ⟨U.hom⟩
  have : IsSeparated (U.left ↘ Spec (.of k)) := by
    change IsSeparated U.hom
    infer_instance
  have : LocallyOfFiniteType (U.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType U.hom
    infer_instance
  have : QuasiCompact (U.left ↘ Spec (.of k)) := by
    change QuasiCompact U.hom
    infer_instance
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  have : IsSeparated (X.left ↘ Spec (.of k)) := by
    change IsSeparated X.hom
    infer_instance
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType X.hom
    infer_instance
  have : QuasiCompact (X.left ↘ Spec (.of k)) := by
    change QuasiCompact X.hom
    infer_instance
  have : j.left.IsOver (Spec (.of k)) := ⟨Over.w j⟩
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  exact tower_ctf_of_iso l E b q X.left
    ((SpTowerCalculus.openEtaleCoordinates l E b o q z j.left
      (cal.etale.etale j.left)).app M.obj) ((cal.etale.etale_preserves j.left).1 M)

end AlgebraicGeometry.ProEtale.SpTowerGluing
