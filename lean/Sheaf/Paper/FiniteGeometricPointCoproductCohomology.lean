/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups J1, K6
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.GeometricPointCohomology
import Sheaf.Paper.FiniteCoproductCohomologyAssembly
import WeilConjectures.AlgebraicGeometry.AbelianStrictlyHenselianOpenGerm
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.Mathlib.RingTheory.Etale.QuasiFinite

/-! # Étale cohomology of a finite coproduct of geometric points

Source: literature/stacks-project/etale-cohomology.tex, Theorem 03QT, Lemma 03QU,
Section 03QQ and Lemma 0A5B (blueprint: lem-weil-pbc-finite-geometric-point-coproduct-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry

-- Keep the existing unused binder name inside the type of `c`.
set_option linter.unusedVariables false in
/-- Étale cohomology of a finite coproduct of geometric points.

Source: literature/stacks-project/etale-cohomology.tex, Theorem 03QT, Lemma 03QU,
Section 03QQ and Lemma 0A5B (blueprint: lem-weil-pbc-finite-geometric-point-coproduct-cohomology).

Proof: For positive degrees, compare derived global sections with the Ext definition
`Sheaf.H` through the right derived functors of evaluation at the terminal étale object.
Apply the single-point vanishing theorem to each inverse-image sheaf, then use the
injectivity in `finiteCoproductCohomologyAssembly` to deduce vanishing on the coproduct.
For degree zero, take the open images of the coprojections. They are pairwise disjoint
and cover the coproduct, so the sheaf condition identifies sections with the product of
sections on those opens. Each open is isomorphic to `Spec k`, a strictly henselian local
scheme. The canonical germ from its sections to the corresponding original stalk is an
isomorphism by `strictlyHenselianOpen_abelian_germ_isIso`. The stalk colimit relation
identifies restriction followed by this germ with the global germ. Their product is
therefore invertible. Finally, restriction from global sections to the terminal étale
object and both canonical degree-zero derived comparisons are isomorphisms. This also
handles the empty index set, using the empty disjoint cover and empty product.
-/
theorem finite_geometric_point_coproduct_cohomology
    (k : Type u) [Field k] [IsAlgClosed k]
    (I : Type u) [Finite I]
    (F : Sheaf (∐ fun _ : I => Spec (.of k)).smallEtaleTopology
      AddCommGrpCat.{u + 1})
    (c : ∀ i : I, Spec (.of k) ⟶ ∐ fun _ : I => Spec (.of k))
    (hc : ∀ i : I, c i = Sigma.ι (fun _ : I => Spec (.of k)) i) :
    (∀ q : ℕ, q > 0 →
      IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} (∐ fun _ : I => Spec (.of k)) (q : ℤ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) ∧
    IsIso
      ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso
          (Sheaf.Γ (∐ fun _ : I => Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})
          F 0).hom ≫
        (Functor.rightDerivedZeroIsoSelf
          (Sheaf.Γ (∐ fun _ : I => Spec (.of k)).smallEtaleTopology
            AddCommGrpCat.{u + 1})).hom.app F ≫
        F.ΓRes (op (Scheme.Etale.mk (𝟙 (∐ fun _ : I => Spec (.of k))))) ≫
        Pi.lift (fun i : I =>
          (pointSmallEtale (c i)).toPresheafFiber
            (Scheme.Etale.mk (𝟙 (∐ fun _ : I => Spec (.of k))))
            (Over.homMk (c i) (Category.comp_id (c i))) F.obj)) := by
  classical
  have hH (X : Scheme.{u}) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (q : ℕ) :
      IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj G)) ↔ Subsingleton (Sheaf.H G q) := by
    let hT := MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale) X
    let e : Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1} ≅
        Sheaf.sectionsFunctorAt X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) :=
      Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1} hT
    let e' := Functor.homologyRightDerivedFunctorObjSingleFunctorIso
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) G q
    change IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj G))) ↔ _
    rw [e'.isZero_iff, ((NatIso.rightDerived e q).app G).isZero_iff]
    exact (Sheaf.subsingleton_H_iff_isZero_rightDerived X.smallEtaleTopology hT q G).symm
  constructor
  · intro q hq
    apply (hH _ F q).2
    have hcomp (i : I) :
        Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (c i)).obj F) q) := by
      apply (hH _ _ q).1
      exact (geometricPoint_etaleCohomology k k (𝟙 _)).1 q (by omega) _
    let (i : I) := hcomp i
    have hb := Etale.finiteCoproductCohomologyAssembly
      (fun _ : I ↦ Spec (.of k)) _ c
      (by simpa only [show c = fun i ↦ Sigma.ι (fun _ : I ↦ Spec (.of k)) i from funext hc]
          using coproductIsCoproduct (fun _ : I ↦ Spec (.of k))) F q
    exact hb.1.subsingleton
  · have hi (i : I) : IsOpenImmersion (c i) := by rw [hc]; infer_instance
    let (i : I) := hi i
    let C := ∐ fun _ : I ↦ Spec (.of k)
    let U : I → C.Opens := fun i ↦ (c i).opensRange
    let e (i : I) : Spec (.of k) ≅ (U i).toScheme :=
      IsOpenImmersion.isoOfRangeEq (c i) (U i).ι (by
        rw [Scheme.Opens.range_ι]; rfl)
    have he (i : I) : (e i).hom ≫ (U i).ι = c i :=
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    let W : I → C.Etale := fun i ↦ Scheme.Etale.mk (U i).ι
    let π : ∀ i, W i ⟶ Scheme.Etale.mk (𝟙 C) := fun i ↦
      MorphismProperty.Over.homMk (U i).ι (Category.comp_id _)
    have (i : I) : Mono (π i) := by
      constructor
      intro Z a b hab
      apply MorphismProperty.Over.Hom.ext
      apply (cancel_mono (U i).ι).mp
      exact congrArg (fun f ↦ f.left) hab
    have hcov : Sieve.ofArrows W π ∈ C.smallEtaleTopology (Scheme.Etale.mk (𝟙 C)) := by
      rw [ofArrows_mem_smallEtaleTopology_iff]
      ext x
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk (fun _ : I ↦ Spec (.of k))).surjective x
      have hy' : c i y = x := by simpa only [sigmaMk_mk, hc] using hy
      refine ⟨i, ⟨x, ?_⟩, rfl⟩
      exact ⟨y, hy'⟩
    have hdisj : ∀ i j, i ≠ j →
        Disjoint (Set.range (π i).left.base) (Set.range (π j).left.base) := by
      intro i j hij
      change Disjoint (Set.range (U i).ι) (Set.range (U j).ι)
      rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      change Disjoint (Set.range (c i)) (Set.range (c j))
      rw [hc, hc]
      apply Set.disjoint_left.mpr
      rintro x ⟨y, hy⟩ ⟨z, hz⟩
      have h := (sigmaι_eq_iff (fun _ : I ↦ Spec (.of k)) i j y z).mp
        (hy.trans hz.symm)
      exact hij (congrArg Sigma.fst h)
    let : IsSepClosed (IsLocalRing.ResidueField k) :=
      IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing k
    let : IsStrictlyHenselianLocalRing k :=
      (isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed k).2
        ⟨inferInstance, inferInstance⟩
    let g := fun i ↦ (pointSmallEtale (c i)).toPresheafFiber (W i)
      (Over.homMk (e i).hom (he i)) F.obj
    have (i : I) : IsIso (g i) := by
      exact strictlyHenselianOpen_abelian_germ_isIso.{u, u} (U i) inferInstance (e i).symm
        (c i) (e i).hom (he i) (by exact Subsingleton.elim _ _) F
    have hr : IsIso (Pi.lift (fun i ↦ F.obj.map (π i).op)) :=
      Scheme.Etale.isIso_piLift_of_disjoint F W π hcov hdisj
    have hfactor : Pi.lift (fun i ↦ F.obj.map (π i).op) ≫ Limits.Pi.map g =
        Pi.lift (fun i : I ↦
          (pointSmallEtale (c i)).toPresheafFiber (Scheme.Etale.mk (𝟙 C))
            (Over.homMk (c i) (Category.comp_id (c i))) F.obj) := by
      apply Pi.hom_ext
      intro i
      simp only [Category.assoc, Pi.map_π, Pi.lift_π_assoc, Pi.lift_π]
      dsimp [g]
      rw [(pointSmallEtale (c i)).toPresheafFiber_w]
      congr 1
      apply Over.OverMorphism.ext
      exact he i
    have : IsIso (Pi.lift (fun i : I ↦
        (pointSmallEtale (c i)).toPresheafFiber (Scheme.Etale.mk (𝟙 C))
          (Over.homMk (c i) (Category.comp_id (c i))) F.obj)) := by
      rw [← hfactor]
      infer_instance
    have : IsIso (F.ΓRes (op (Scheme.Etale.mk (𝟙 C)))) :=
      F.isLimitConeΓ.isIso_π_app_of_isInitial _
        (MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale) C).op
    infer_instance

end AlgebraicGeometry
