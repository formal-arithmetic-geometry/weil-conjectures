/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
import Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.CategoryTheory.Sites.Point.Linear
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.Curve.GenericFinitePrimaryDecomposition
import WeilConjectures.AlgebraicGeometry.Curve.FiniteStalkSubobjectsCover
import Mathlib.Order.Shrink
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject
import WeilConjectures.AlgebraicGeometry.Curve.EtaleSheafHLargeFilteredColimit

/-!
# The all-torsion cohomological dimension of a finite field

Source: main-20261015, det-pe-unbounded-classical-bounds, steps 1--3.
(blueprint: lem-sfb-finite-field-all-torsion-cd)
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

open ProEtale

private theorem ell_torsion_of_annihilated
    {A : Type u} [Category.{v} A] [Abelian A] [HasColimitsOfShape ℕ A]
    (l : ℕ) (hl : l.Prime) (M : A) (e : ℕ) (he : (l ^ e) • 𝟙 M = 0) :
    IsEllPowerTorsion l hl M := by
  have hi : 𝟙 M ≫ ((l ^ e) • 𝟙 M) = 0 := by simpa using he
  let D := ellPowerKernelFunctor l (F := M)
  let a := ellPowerKernelColimitMap l (F := M)
  let b : M ⟶ colimit D :=
    kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫ colimit.ι D e
  have hba : b ≫ a = 𝟙 M := by
    dsimp [b, a, ellPowerKernelColimitMap]
    rw [Category.assoc, colimit.ι_desc]
    exact kernel.lift_ι _ _ _
  have hab : a ≫ b = 𝟙 (colimit D) := by
    apply colimit.hom_ext
    intro r
    let t := e + r
    have her : e ≤ t := Nat.le_add_right e r
    have hrt : r ≤ t := Nat.le_add_left r e
    have hmap : kernel.ι ((l ^ r) • 𝟙 M) ≫
        kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫ D.map (homOfLE her) =
        D.map (homOfLE hrt) := by
      apply (cancel_mono (kernel.ι ((l ^ t) • 𝟙 M))).mp
      simp only [D, ellPowerKernelFunctor, ellPowerKernelMap, Category.assoc,
        kernel.lift_ι, Category.comp_id]
    calc
      colimit.ι D r ≫ a ≫ b =
          kernel.ι ((l ^ r) • 𝟙 M) ≫
            kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫ colimit.ι D e := by
        dsimp [a, b, ellPowerKernelColimitMap]
        rw [← Category.assoc, colimit.ι_desc]
        rfl
      _ = kernel.ι ((l ^ r) • 𝟙 M) ≫
            kernel.lift ((l ^ e) • 𝟙 M) (𝟙 M) hi ≫
              D.map (homOfLE her) ≫ colimit.ι D t := by rw [colimit.w]
      _ = D.map (homOfLE hrt) ≫ colimit.ι D t := by
        simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ colimit.ι D t) hmap
      _ = colimit.ι D r ≫ 𝟙 _ := by rw [colimit.w, Category.comp_id]
  exact ⟨⟨b, hab, hba⟩⟩

private theorem primary_annihilator (K : Type u) [Field K]
    (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (l : ℕ) (_hl : l.Prime)
    (hfinite : Finite (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap K (AlgebraicClosure K))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))
    (hprimary : IsPGroup l (Multiplicative (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap K (AlgebraicClosure K))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))) :
    ∃ (e : ℕ), (l ^ e) • 𝟙 M = 0 := by
  let s := Spec.map (CommRingCat.ofHom
    (algebraMap K (AlgebraicClosure K)))
  let Φ := Scheme.pointSmallEtale s
  let : Finite ((Φ.sheafFiber (A := AddCommGrpCat.{u + 1})).obj M) := hfinite
  obtain ⟨e, he⟩ := isPGroup_iff_exists_pow_pow_eq_one.mp hprimary
  have hkill (x : (Φ.sheafFiber (A := AddCommGrpCat.{u + 1})).obj M) : (l ^ e) • x = 0 := by
    simpa using congrArg Multiplicative.toAdd (he (Multiplicative.ofAdd x))
  have hmap : Φ.sheafFiber.map ((l ^ e) • 𝟙 M) = Φ.sheafFiber.map (0 : M ⟶ M) := by
    rw [Φ.sheafFiber_map_smul, CategoryTheory.Functor.map_id]
    ext x
    simpa using hkill x
  refine ⟨e, ?_⟩
  have hs : ⋃ _ : PUnit.{u + 1}, Set.range s = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨PUnit.unit, default, Subsingleton.elim _ _⟩
  have hc := Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ
    (Spec (.of K)) (fun _ : PUnit.{u + 1} ↦ s) hs
  refine (hc.jointlyFaithful AddCommGrpCat.{u + 1}).map_injective ?_
  rintro ⟨-, ⟨i⟩⟩
  -- Compare with the universe-lifted point used by the conservative-family theorem.
  have iso := Φ.uliftSheafFiberIso.{u + 1} AddCommGrpCat.{u + 1}
  rw [← Iso.cancel_iso_hom_right _ _ (iso.app M), Iso.app_hom,
    iso.hom.naturality, iso.hom.naturality, hmap]

private theorem primary_vanishing (K : Type u) [Field K] [Finite K]
    (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (l : ℕ) (hl : l.Prime)
    (hfinite : Finite (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap K (AlgebraicClosure K))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))
    (hprimary : IsPGroup l (Multiplicative (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap K (AlgebraicClosure K))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M)))
    (q : ℕ) (hq : 1 < q) :
    IsZero ((DerivedCategory.singleFunctor _ 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} (Spec (.of K)) (q : ℤ)).obj M) := by
  obtain ⟨e, he⟩ := primary_annihilator K M l hl hfinite hprimary
  have htor := ell_torsion_of_annihilated l hl M e he
  have hnum := (cohomologicalDimension_baseField l hl K).2 inferInstance
  rw [cohomologicalDimension_eq_etaleCohomologicalDimension] at hnum
  by_contra hn
  have hmem : (q : WithTop ℕ) ∈ {q : WithTop ℕ |
      ∃ n : ℕ, q = n ∧ ∃ F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1},
        IsEllPowerTorsion l hl F ∧
          ¬ IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} (Spec (.of K)) (n : ℤ)).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))} := ⟨q, rfl, M, htor, hn⟩
  have hle : (q : WithTop ℕ) ≤ 1 := (le_sSup hmem).trans hnum
  exact (not_le_of_gt hq) (WithTop.coe_le_coe.mp hle)


private theorem finite_stalk_vanishing (K : Type u) [Field K] [Finite K]
    (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) (hM : M.IsTorsion)
    (hfinite : Finite (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap K (AlgebraicClosure K))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))
    (q : ℕ) (hq : 1 < q) :
    IsZero ((DerivedCategory.singleFunctor _ 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} (Spec (.of K)) (q : ℤ)).obj M) := by
  classical
  obtain ⟨r, p, N, hp, hfin, hprimary, a, b, hab⟩ :=
    Scheme.exists_finite_primary_sheaf_decomposition K M hM hfinite
  let T := DerivedCategory.singleFunctor _ 0 ⋙
    Etale.cohomology AddCommGrpCat.{u + 1} (Spec (.of K)) (q : ℤ)
  obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso (Spec (.of K)) q
  have : T.Additive := Functor.additive_of_iso e
  have hz (i : Fin r) : IsZero (T.obj (N i)) :=
    primary_vanishing K (N i) (p i) (hp i) (hfin i) (hprimary i) q hq
  apply (IsZero.iff_id_eq_zero _).mpr
  calc
    𝟙 (T.obj M) = T.map (∑ i, a i ≫ b i) := by rw [hab, T.map_id]
    _ = ∑ i, T.map (a i) ≫ T.map (b i) := by rw [T.map_sum]; simp
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [(hz i).eq_of_tgt (T.map (a i)) 0, zero_comp]

private theorem finite_fiber_sup
    {C : Type*} [Category C] [Abelian C]
    (Φ : C ⥤ AddCommGrpCat.{u + 1}) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    {M : C} (S T : Subobject M)
    (hS : Finite (Φ.obj (S : C))) (hT : Finite (Φ.obj (T : C))) :
    Finite (Φ.obj ((S ⊔ T : Subobject M) : C)) := by
  have : Epi (Subobject.supDesc S T) := Subobject.epi_supDesc S T
  have : PreservesBinaryBiproducts Φ :=
    preservesBinaryBiproducts_of_preservesBinaryProducts Φ
  let e := Φ.mapBiprod (S : C) (T : C) ≪≫
    AddCommGrpCat.biprodIsoProd (Φ.obj (S : C)) (Φ.obj (T : C))
  have : Finite (Φ.obj ((S : C) ⊞ (T : C))) :=
    Finite.of_injective e.hom (ConcreteCategory.bijective_of_isIso e.hom).1
  exact Finite.of_surjective (Φ.map (Subobject.supDesc S T))
    ((AddCommGrpCat.epi_iff_surjective _).mp inferInstance)

private theorem torsion_of_mono
    {X : Scheme.{u}} {N M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : N ⟶ M) [Mono f] (hM : M.IsTorsion) : N.IsTorsion := by
  intro U s
  obtain ⟨R, hR, hs⟩ := hM (f.hom.app U s)
  refine ⟨R, hR, ?_⟩
  intro V g hg
  obtain ⟨n, hn, he⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (hs hg)
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
  have hinj : Function.Injective (f.hom.app (Opposite.op V)) := by
    rw [← AddCommGrpCat.mono_iff_injective]
    exact ((sheafToPresheaf X.smallEtaleTopology _ ⋙
      (CategoryTheory.evaluation _ _).obj (Opposite.op V)).map_mono f :)
  apply hinj
  rw [map_nsmul, map_zero]
  have hw := ConcreteCategory.congr_hom (f.hom.naturality g.op) s
  change f.hom.app (Opposite.op V) (N.obj.map g.op s) =
    M.obj.map g.op (f.hom.app U s) at hw
  rw [hw]
  exact he

private theorem finite_stalk_colimit
    (K : Type u) [Field K]
    (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : M.IsTorsion) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (F : I ⥤ Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (ι : F ⟶ (Functor.const I).obj M),
      (∀ i, (F.obj i).IsTorsion) ∧
      (∀ i, Finite (((Scheme.pointSmallEtale
        (Spec.map (CommRingCat.ofHom
          (algebraMap K (AlgebraicClosure K))))).sheafFiber
            (A := AddCommGrpCat.{u + 1})).obj (F.obj i))) ∧
      Nonempty (IsColimit (Cocone.mk M ι)) := by
  classical
  let C := Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}
  have : HasColimitsOfSize.{u + 1, u + 1} C := IsGrothendieckAbelian.hasColimits C
  let : CompleteLattice (Subobject M) := Subobject.instCompleteLattice.{u + 1}
  let Φ := (Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom
      (algebraMap K (AlgebraicClosure K))))).sheafFiber
        (A := AddCommGrpCat.{u + 1})
  have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  have : Φ.Additive := Functor.additive_of_preserves_binary_products Φ
  let B := {N : Subobject M // Finite (Φ.obj (N : C))}
  have hbot : Finite (Φ.obj ((⊥ : Subobject M) : C)) := by
    have hz : IsZero ((⊥ : Subobject M) : C) :=
      (isZero_zero C).of_iso Subobject.botCoeIsoZero
    have : Subsingleton (Φ.obj ((⊥ : Subobject M) : C)) :=
      AddCommGrpCat.subsingleton_of_isZero (Φ.map_isZero hz)
    infer_instance
  have : Nonempty B := ⟨⟨⊥, hbot⟩⟩
  have : IsDirectedOrder B := ⟨fun a b ↦
    ⟨⟨a.val ⊔ b.val, finite_fiber_sup Φ a.val b.val a.property b.property⟩,
      (show a.val ≤ a.val ⊔ b.val from le_sup_left),
      (show b.val ≤ a.val ⊔ b.val from le_sup_right)⟩⟩
  have : IsFiltered B := inferInstance
  let I := Shrink.{u + 1} B
  let : SmallCategory I := inferInstanceAs (SmallCategory (Shrink.{u + 1} B))
  let e : B ≌ I := (orderIsoShrink.{u + 1} B).equivalence
  have : IsFiltered I := IsFiltered.of_equivalence e
  let j : B ⥤ Subobject M :=
    (show Monotone (fun b : B ↦ b.val) from fun _ _ h ↦ h).functor
  let D : I ⥤ MonoOver M := e.inverse ⋙ j ⋙ Subobject.representative
  let F : I ⥤ C := D ⋙ MonoOver.forget M ⋙ Over.forget M
  let c : Cocone (D ⋙ MonoOver.forget M) :=
    { pt := Over.mk (𝟙 M)
      ι :=
        { app := fun i ↦ Over.homMk (D.obj i).obj.hom (by simp)
          naturality := by
            intro i k f
            ext
            simp } }
  have hcover : (⨆ b : B, b.val) = ⊤ :=
    Scheme.torsion_finite_stalk_subobjects_iSup_eq_top K M hM
  have : Mono c.pt.hom := inferInstanceAs (Mono (𝟙 M))
  have htop : Subobject.mk c.pt.hom = ⊤ := (Subobject.top_eq_id M).symm
  have hsup : Subobject.mk c.pt.hom = ⨆ i, Subobject.mk (D.obj i).obj.hom := by
    apply le_antisymm
    · rw [htop, ← hcover]
      refine iSup_le fun b ↦ ?_
      simpa [D, j, e] using
        (le_iSup (fun i ↦ Subobject.mk (D.obj i).obj.hom) (e.functor.obj b))
    · rw [htop]
      exact le_top
  let hc := IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup D c hsup
  refine ⟨I, inferInstance, inferInstance, F, ((Over.forget M).mapCocone c).ι, ?_, ?_, ?_⟩
  · intro i
    exact torsion_of_mono (D.obj i).obj.hom hM
  · intro i
    exact (e.inverse.obj i).property
  · exact ⟨hc⟩

/-- Every locally torsion abelian sheaf on a finite field has no cohomology above degree one.
Source: main-20261015, det-pe-unbounded-classical-bounds, steps 1--3; Stacks 04JQ,
03SA and 03QQ, and sk-lem-base-field-cd-finite-field.proof.md.
(blueprint: lem-sfb-finite-field-all-torsion-cd)

Proof: Finite-stalk subobjects cover a torsion sheaf over a field. They form a directed
family, since the sum is an image of the product of the two finite stalks. Shrink this
family to the sheaf universe and use the Grothendieck-category supremum/colimit criterion
to express the sheaf as its filtered colimit. Each subobject remains torsion by injectivity
of its section maps. Decompose each finite-stalk sheaf into finitely many primary retracts.
A finite primary stalk has a common prime-power annihilator. The conservative geometric
point family detects the same annihilator on the sheaf. The prime-power kernel colimit is
then isomorphic to the sheaf: the kernel at that exponent provides an inverse, and passage
to a common larger exponent proves the other inverse identity on every colimit injection.
Thus the prime-power cohomological dimension bound for finite fields kills each primary
piece above degree one. Applying the additive cohomology functor to the finite sum of
projection-inclusion composites kills the original finite-stalk sheaf. Finally filtered
colimit continuity of etale cohomology on the affine field spectrum kills the arbitrary
torsion sheaf. The bottom subobject and an empty primary decomposition include the zero
sheaf; no uniform exponent for the original sheaf is assumed. -/
theorem hasTorsionEtaleCohomologicalDimensionLE_one_of_finite
    (K : Type u) [Field K] [Finite K] :
    HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) 1 := by
  intro M hM q hq
  obtain ⟨I, hI, hfiltered, D, ι, htor, hfin, hcolim⟩ := finite_stalk_colimit K M hM
  let _ := hI
  let _ := hfiltered
  let T := DerivedCategory.singleFunctor _ 0 ⋙
    Etale.cohomology AddCommGrpCat.{u + 1} (Spec (.of K)) (q : ℤ)
  have hH := (Scheme.etaleCohomology_isColimit_large_filtered
    (Spec (.of K)) hcolim.some q).some
  have hzero : IsZero (D ⋙ T) := (Functor.isZero_iff _).mpr fun i ↦
    finite_stalk_vanishing K (D.obj i) (htor i) (hfin i) q hq
  exact AddCommGrpCat.isZero_iff_subsingleton.mp (hH.isZero_pt hzero)

end AlgebraicGeometry.Scheme
