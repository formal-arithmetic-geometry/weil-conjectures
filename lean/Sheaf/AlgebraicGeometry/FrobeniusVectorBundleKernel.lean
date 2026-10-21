/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.Grp.Ulift

import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import Sheaf.AlgebraicGeometry.FiniteEtaleYonedaLocalTrivializations
import WeilConjectures.AlgebraicGeometry.FiniteLocalAbelianForget
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import all WeilConjectures.AlgebraicGeometry.PullbackFiniteLocallyConstant
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Sheaf.AlgebraicGeometry.FrobeniusVectorBundleLocalLifts
import Sheaf.AlgebraicGeometry.FrobeniusVectorBundleAffineKernelModels

/-!
# Fixed points of Frobenius-semilinear vector-bundle endomorphisms

Source: Stacks Project, More on Étale Cohomology, Tag 0GKU,
lemma-frobenius-linear-on-vb, Noetherian specialization
(blueprint: lem-weil-pbc-frobenius-vector-bundle-kernel).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

private theorem finiteAbelianModels {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsLisseEtaleSheafOfSets
      ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G)) :
    ∃ V : Cover.{u} etalePrecoverage X, ∀ i : V.I₀,
      ∃ A : AddCommGrpCat.{u + 1}, Finite A ∧
        Nonempty ((Etale.upperStar AddCommGrpCat.{u + 1} (V.f i)).obj G ≅
          (constantSheaf (V.X i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) := by
  classical
  let : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  obtain ⟨hloc, hfin⟩ := (finite_local_abelian_forget_iff G).mp hG
  obtain ⟨⟨V₀, hV₀⟩⟩ := hloc.nonempty_locallyConstantDatum
  let V : Cover.{u} etalePrecoverage X :=
    { I₀ := { i : V₀.I₀ // Nonempty (V₀.X i) }
      X i := V₀.X i.1
      f i := V₀.f i.1
      mem₀ := by
        refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, fun i ↦ V₀.map_prop i.1⟩
        obtain ⟨i, y, hy⟩ := V₀.exists_eq x
        exact ⟨⟨i, ⟨y⟩⟩, y, hy⟩ }
  refine ⟨V, fun i ↦ ?_⟩
  have := hV₀ i.1
  obtain ⟨A, ⟨e⟩⟩ := (G.over (V₀.etalePrecoverageToEtale i.1)).mem_essImage_of_isConstant
  let U := V.etalePrecoverageToEtale i
  let e' : (Etale.upperStar AddCommGrpCat.{u + 1} U.hom).obj G ≅
      (constantSheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A :=
    (overSheafEquivFunctorObjOverIso AddCommGrpCat.{u + 1} U G).symm ≪≫
      (Etale.overSheafEquiv U AddCommGrpCat.{u + 1}).functor.mapIso e.symm ≪≫
      ((Etale.overEquiv U).constantSheafSheafCongrIso
        (X.smallEtaleTopology.over U) U.left.smallEtaleTopology
        AddCommGrpCat.{u + 1} Over.mkIdTerminal).app A
  have : Nonempty U.left := i.2
  let t := U.left.algClosurePoint (Classical.arbitrary U.left)
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let es := ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} U.hom t).app G).symm ≪≫
    (pointSmallEtale t).sheafFiber.mapIso e' ≪≫
    (pointSmallEtale t).sheafFiberConstantSheafIso A
  exact ⟨A, @Finite.of_equiv _ _ (hfin _ (t ≫ U.hom))
    es.addCommGroupIsoToAddEquiv.toEquiv, ⟨e'⟩⟩

private theorem lissePullbackOfRepresentable {X Y P : Scheme.{u}}
    (i : Y ⟶ X) (π : P ⟶ X) [Etale π]
    [IsFinite (pullback.snd π i)]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G ≅
      (X.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Etale.mk π)) :
    IsLisseEtaleSheafOfSets
      ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} i).obj G)) := by
  let ea := (AlgebraicGeometry.etaleInverseImageAlgebraicStructures Y X i).2.choose.app G
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    i.Etale (Type (u + 1)) X.smallEtaleTopology Y.smallEtaleTopology
  obtain ⟨er⟩ := AlgebraicGeometry.nonempty_inverseImage_representable_iso.{u, u + 1}
    i (etaleSetPullback i) adj
  let e' := ea ≪≫ (etaleSetPullback i).mapIso e ≪≫ er.app (Etale.mk π)
  obtain ⟨⟨V, hV⟩, hf⟩ :=
    finiteEtale_yoneda_local_trivializations Y (pullback π i) (pullback.snd π i)
  apply finiteLocallyConstant_of_iso e'.symm
  refine ⟨⟨V, fun j ↦ ?_⟩, hf⟩
  obtain ⟨A, _, ⟨eA⟩⟩ := hV j
  exact Sheaf.isConstant_of_iso _ eA

private theorem constructibleOfAffineRepresentations {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) (W : Fin n → X.Opens) (hW : ∀ a, IsAffineOpen (W a))
    (hcover : (⋃ a : Fin n, (W a : Set X)) = Set.univ)
    (P : Fin n → Scheme.{u}) (π : ∀ a, P a ⟶ (W a).toScheme)
    [∀ a, Etale (π a)] [∀ a, CompactSpace (P a)] [∀ a, QuasiSeparatedSpace (P a)]
    (e : ∀ a, Nonempty
      ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} (W a).ι).obj G) ≅
          ((W a).toScheme.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Etale.mk (π a)))) :
    IsConstructibleAbelianSheaf G := by
  classical
  have hstr (a : Fin n) := by
    have : IsAffine (W a).toScheme := hW a
    exact exists_etale_stratified_finite (π a)
  choose T hc hfinite using hstr
  have hlocal (a : Fin n) (b : Fin (T a).n) : IsLisseEtaleSheafOfSets
      ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} ((T a).immersion b ≫ (W a).ι)).obj G)) := by
    have := (hfinite a b).1
    have hi := lissePullbackOfRepresentable ((T a).immersion b) (π a)
      ((Etale.upperStar AddCommGrpCat.{u + 1} (W a).ι).obj G) (e a).some
    exact finiteLocallyConstant_of_iso
      ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso
      ((Etale.upperStarComp AddCommGrpCat.{u + 1} ((T a).immersion b) (W a).ι).app G).symm) hi
  obtain ⟨S, hS, hfac⟩ :=
    exists_global_stratification_factoring_local n W hW hcover T hc
  refine ⟨S, hS, fun j ↦ ?_⟩
  obtain ⟨a, b, q, hq⟩ := hfac j
  have h := (pullback_finite_locally_constant q ((T a).immersion b ≫ (W a).ι)
    G (hlocal a b)).2
  rw [hq] at h
  exact finiteAbelianModels _ h

/-- A Frobenius-semilinear endomorphism of a finite locally free module has zero
cokernel after subtracting the identity, and its fixed-point sheaf is constructible.
The sectionwise lift uses the transported additive structure; scalar multiplication
is written explicitly by lowering both sections and lifting their product.
Source: Stacks Project, Tag 0GKU (Noetherian specialization).
(blueprint: lem-weil-pbc-frobenius-vector-bundle-kernel)

Proof:
1. Choose finitely many affine trivializing charts, with independently varying finite
ranks. Local Noetherianness gives quasi-separatedness. On a chart, write F as a matrix
applied to p-th powers of the coordinates; tensor pullback preserves the free basis.
2. For a target vector b, adjoin solutions of b_i + x_i - sum_j c_ij x_j^p = 0.
The Jacobian is the identity, so the square-Jacobian criterion makes this cover étale.
3. Lang's semilinear surjectivity over algebraically closed residue fields makes every
geometric fibre nonempty. These solution covers prove local surjectivity, hence the
abelian sheaf cokernel vanishes. Lift the calculations sectionwise along ULift.
4. At b = 0 the same affine étale scheme represents the kernel: its coordinate tuples
are exactly fixed sections, naturally under restriction, and the affine identifications glue.
5. Stratify each chart into finitely many constructible locally closed subschemes over
which this representing scheme is finite étale. Inverse image of a represented sheaf
is represented by its base change, compatibly with the abelian underlying set sheaf.
6. Finite étale Yoneda trivializations and the finite-local-abelian-forget comparison
make the abelian kernel finite locally constant on each stratum.
7. Refine all chart stratifications to one finite global partition. Inverse-image
composition and base change of covering families transport the local trivializations;
inverse image preserves constant finite abelian sheaves. This is precisely the finite
abelian stratum definition of constructibility. The empty scheme uses the empty
partition; rank zero uses the identity solution cover and the zero kernel. -/
theorem frobenius_vectorBundle_kernel_constructible
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.Over (Spec (.of (ULift.{u} (ZMod p))))] [CompactSpace S] [IsLocallyNoetherian S]
    (E : S.Modules) [E.IsFiniteLocallyFree]
    (F : (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E) ⟶
      (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E))
    (hF : ∀ (U : S.Etaleᵒᵖ) (a : ULift.{u + 1} Γ(U.unop.left, ⊤))
        (e : ULift.{u + 1} Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)),
      F.hom.app U (ULift.up (a.down • e.down)) =
        ULift.up (a.down ^ p • (@id Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)
          (F.hom.app U e).down))) :
    IsZero (cokernel (F - 𝟙 _)) ∧
      IsConstructibleAbelianSheaf (kernel (F - 𝟙 _))  := by
  classical
  have hsurj := frobenius_vectorBundle_local_lifts p S E F hF
  have : Sheaf.IsLocallySurjective (F - 𝟙 _) := hsurj
  have : Epi (F - 𝟙 _) := inferInstance
  refine ⟨isZero_cokernel_of_epi _, ?_⟩
  obtain ⟨n, W, hW, hcover, hmodel⟩ :=
    frobenius_vectorBundle_affine_kernel_models p S E F hF
  choose P π hP hπ e using hmodel
  have : ∀ a, IsAffine (P a) := hP
  have : ∀ a, Etale (π a) := hπ
  exact constructibleOfAffineRepresentations (kernel (F - 𝟙 _)) n W hW hcover P π e

end AlgebraicGeometry.Scheme
