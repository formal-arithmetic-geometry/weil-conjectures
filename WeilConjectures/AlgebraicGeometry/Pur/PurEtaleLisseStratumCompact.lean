/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleClosedRightAdjointCoproducts
import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleLisseDualizable
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompact
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Module.ULift
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactInjective
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactSurjective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts

/-!
# Compactness of a lisse sheaf extended from a locally closed stratum

## References

* Bhatt--Scholze, *Pro-étale topology*, Section 6.4, Example 6.4.1, Lemmas 6.4.4 and 6.4.6, and the
  last paragraph of Proposition 6.4.8, printed pp. 48--49
* Bhatt--Scholze, *Pro-étale topology*, Section 6.4, Example 6.4.1, Lemmas 6.4.4 and 6.4.6, and the
  last paragraph of the proof of Proposition 6.4.8, printed pp. 48--49
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Etale

private theorem compact_of_homEquiv
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [HasCoproducts.{u + 1} A] [HasCoproducts.{u + 1} B]
    (G : B ⥤ A)
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G]
    (K : A) (P : B) (hK : IsCompactObject K)
    (e : ∀ M : B, (P ⟶ M) ≃+ (K ⟶ G.obj M))
    (he : ∀ {M N : B} (f : P ⟶ M) (g : M ⟶ N),
      e N (f ≫ g) = e M f ≫ G.map g) : IsCompactObject P := by
  classical
  intro I E
  let a := DirectSum.toAddMonoid
    (fun i : I ↦ Preadditive.rightComp P (Sigma.ι E i))
  let b := DirectSum.toAddMonoid
    (fun i : I ↦ Preadditive.rightComp K (Sigma.ι (fun i ↦ G.obj (E i)) i))
  let d := DirectSum.map (fun i ↦ (e (E i)).toAddMonoidHom)
  let t : (K ⟶ ∐ (fun i ↦ G.obj (E i))) ≃+ (K ⟶ G.obj (∐ E)) :=
    { (Iso.homCongr (Iso.refl K) (asIso (sigmaComparison G E))) with
      map_add' := by intros; simp }
  have hd : Function.Bijective d :=
    ⟨(DirectSum.map_injective _).2 (fun i ↦ (e (E i)).injective),
      (DirectSum.map_surjective _).2 (fun i ↦ (e (E i)).surjective)⟩
  have hb : Function.Bijective b := hK I (fun i ↦ G.obj (E i))
  have hcomm : (e (∐ E)).toAddMonoidHom.comp a =
      t.toAddMonoidHom.comp (b.comp d) := by
    apply DirectSum.addHom_ext
    intro i f
    dsimp [a, b, d]
    simp only [DirectSum.toAddMonoid_of, DirectSum.map_of]
    simpa [t, Iso.homCongr, Preadditive.rightComp, Category.assoc] using
      he f (Sigma.ι E i)
  have hbij : Function.Bijective ((e (∐ E)).toAddMonoidHom.comp a) := by
    rw [hcomm]
    exact t.bijective.comp (hb.comp hd)
  exact Function.Bijective.of_comp_left hbij (e (∐ E)).injective

private theorem compact_of_adjunction
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [HasCoproducts.{u + 1} A] [HasCoproducts.{u + 1} B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G]
    (adj : F ⊣ G) (K : A) (hK : IsCompactObject K) :
    IsCompactObject (F.obj K) := by
  apply compact_of_homEquiv G K (F.obj K) hK (fun M ↦ adj.homAddEquiv K M)
  intro M N f g
  exact adj.homEquiv_naturality_right f g

private theorem compact_of_iso
    {A : Type*} [Category A] [Preadditive A] [HasCoproducts.{u + 1} A]
    {K P : A} (e : K ≅ P) (hK : IsCompactObject K) : IsCompactObject P := by
  apply compact_of_homEquiv (𝟭 A) K P hK
    (fun M ↦ { Iso.homCongr e.symm (Iso.refl M) with map_add' := by intros; simp })
  intro M N f g
  simp [Iso.homCongr, Category.assoc]

attribute [local instance] Sheaf.monoidalCategory

private theorem compact_of_dualizable
    {A : Type*} [Category A] [Preadditive A] [HasCoproducts.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A]
    (K : A) (hK : IsDualizable K) (hunit : IsCompactObject (𝟙_ A)) :
    IsCompactObject K := by
  obtain ⟨d⟩ := hK
  let _ : ExactPairing d.rightDual K := BraidedCategory.exactPairing_swap K d.rightDual
  have : (tensorLeft d.rightDual).IsLeftAdjoint :=
    (tensorLeftAdjunction K d.rightDual).isLeftAdjoint
  exact compact_of_iso (ρ_ K)
    (compact_of_adjunction (tensorLeftAdjunction d.rightDual K) (𝟙_ A) hunit)

private theorem compact_unit
    {C : Type (u + 1)} [CommRing C] [Finite C]
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCoproducts.{u + 1} (DerivedCategoryModule C X)] :
    IsCompactObject (𝟙_ (DerivedCategoryModule C X)) := by
  let : HasCoproducts.{u + 1} (DerivedCategory (ModuleCat.{u + 1} C)) :=
    CategoryTheory.derived_hasCoproducts
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := ⟨⟩
  have (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I)
      R(Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} C)) :=
    preservesCoproducts_rightDerivedGlobalSections C X
      (hasFiniteCohomologicalDimension_of_isSepClosed C (isAddTorsion_of_finite) f) I
  let F := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)
  let adj := (constantSheafΓAdj X.smallEtaleTopology
    (ModuleCat.{u + 1} C)).mapDerivedCategoryRightDerivedAdjunction
  have h := compact_of_adjunction adj
    ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
      (ModuleCat.of C (ULift.{0} C))) (CategoryTheory.derivedModule_rankOne_compact (S := C))
  let e : ModuleCat.of C (ULift.{0} C) ≅ ModuleCat.of C C :=
    (ULift.moduleEquiv : ULift.{0} C ≃ₗ[C] C).toModuleIso
  let e' := (F.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of C (ULift.{0} C)) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (F.mapIso e) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Functor.Monoidal.εIso (constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} C))).symm ≪≫
    singleFunctorObjUnitIso (ModuleCat.{u + 1} C) X
  exact compact_of_iso e' h

set_option linter.unusedVariables false in
-- The statement retains the paper's coefficient hypotheses, although finite torsion suffices.
/-- A finite locally constant flat module sheaf, extended by zero from a locally closed
stratum and then pushed forward to the ambient finite-type scheme, is compact in the
unbounded ordinary étale derived category. No separatedness of `X` is assumed.

Proof, following the node (adjoint form of Bhatt--Scholze, Section 6.4):
1. Put `W = X \ g(Z)` with open inclusion `q: W ⟶ X`. A finite affine cover of `X` by
   finite-type `k`-algebras restricts to one of `Z`, so `Z` is finite type over `k`
. By `lem-weil-pbc-finite-type-over-noetherian` and
   `lem-weil-pbc-noetherian-open-subscheme-noetherian`, `X, Z, V, W` are Noetherian, hence
   quasi-separated.
   `lem-weil-pbc-qcqs-morphism-permanence` makes `j, q` quasi-compact, hence finite type
, and the structure map `a: V ⟶ Spec k`
   qcqs. No separatedness is used.
2. Module sheaves form Grothendieck abelian categories
, so derived coproducts are termwise
   and exact. Exact inverse image is a left
   adjoint (`situation-conventions`), so `g^*, j^*, q^*` and étale slice
   restrictions preserve derived coproducts.
3. `C` is torsion and `k` separably closed: `lem-etale-finite-type-sep-closed-derived-dimension`
   applied separately to `q` and `a`, with `lem-etale-qcqs-finite-dimension-derived-coproducts`,
   gives that `Rq_*` and `Ra_*` preserve coproducts. Sections on `(Spec k)_ét` are exact and
   preserve sums, so
   `RΓ(V, -)` preserves coproducts.
4. `g_*` is exact, so `Rg_* = g_*`
and the closed counit
 gives `g^* g_* ≅ id`. Compare the
   closed-support triangles `g_* Rg^! K → K → Rq_* q^* K`
 for `K_i`
   and for `⨁ K_i`; steps 2 and 3 make the last two comparisons isomorphisms, so the first is too,
   and applying `g^*` shows that `Rg^!`, hence `B = j^* Rg^!`, commutes with coproducts.
5. On each nonempty member of a trivializing étale cover, `L` is constant with value a finite
   `C`-module `P`, flat as a geometric stalk. `P` is finitely presented (finite kernel of
   `C^n → P`), hence projective,
   hence a retract of `C^n`; the constant sheaf is a retract of `C_V^n` there.
6. Put `H_L(N) = RHom_C(L, N)`. The comparison
   `⨁ H_L(N_i) → H_L(⨁ N_i)` may be tested after trivializing restrictions
   (`lem-weil-pbc-ringed-internal-hom-exact-restriction`, step 2). There
   `RHom_C(C^n, N) ≅ N^n` gives an isomorphism, and the retract `v u = id_L` gives the
   inverse `S(u) α_{C^n}⁻¹ T(v)` of `α_L`. Exact stalks
 and conservativity
 on cohomology sheaves conclude.
7. For `j: V ⟶ Z`, the adjunctions `g_* ⊣ Rg^!`, `j_! ⊣ j^*` and
   `lem-pur-rhom-global-sections` give, naturally in `K`,
   `Hom_X(g_* j_! L, K) ≅ Hom_V(L, j^* Rg^! K) ≅ H^0 RΓ(V, H_L(B K))`. `B`, `H_L` and
   `RΓ(V, -)` preserve coproducts by steps 4, 6 and 3, and `H^0` commutes with direct sums
   of complexes of `C`-modules. Hence the
   comparison of `def-pc-compact-object` is bijective, including for an empty family. -/
theorem isCompactObject_lowerStar_openImmersionLowerShriek_of_isFiniteLocallyConstantSheaf
    {k : Type u} [Field k] [IsAlgClosed k]
    (ell : ℕ) (hell : Nat.Prime ell) (hellk : IsUnit (ell : k))
    {C : Type (u + 1)} [CommRing C] [Finite C]
    (hC : ∃ r : ℕ, (ell : C) ^ r = 0)
    {X Z V : Scheme.{u}}
    (g : Z ⟶ X) [IsClosedImmersion g]
    (j : V ⟶ Z) [IsOpenImmersion j]
    (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} C))
    [Scheme.IsFiniteLocallyConstantSheaf L]
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ V),
      ObjectProperty.flat ((Scheme.pointSmallEtale s).sheafFiber.obj L)) :
    ∃ (hcoprod : HasCoproducts.{u + 1} (DerivedCategoryModule C X)),
      @IsCompactObject (DerivedCategoryModule C X) _ _ hcoprod
      ((DerivedCategory.singleFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} C) g).obj
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} C) j).obj L))) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian Z := ⟨⟩
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian j
  have : NoetherianSpace V :=
    j.isOpenEmbedding.isEmbedding.noetherianSpace
  have : QuasiCompact j := inferInstance
  let hcX : HasCoproducts.{u + 1} (DerivedCategoryModule C X) :=
    CategoryTheory.derived_hasCoproducts
  let hcZ : HasCoproducts.{u + 1} (DerivedCategoryModule C Z) :=
    CategoryTheory.derived_hasCoproducts
  let hcV : HasCoproducts.{u + 1} (DerivedCategoryModule C V) :=
    CategoryTheory.derived_hasCoproducts
  refine ⟨hcX, ?_⟩
  let K := (DerivedCategory.singleFunctor
    (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).obj L
  obtain ⟨braiding⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} C))
  let : BraidedCategory (DerivedCategoryModule C V) := braiding
  have hK : IsCompactObject K := compact_of_dualizable K
    (isDualizable_singleFunctor_lisseFlat L hL) (compact_unit (j ≫ g ≫ f))
  let J := openImmersionLowerShriek (ModuleCat.{u + 1} C) j
  let G := lowerStar (ModuleCat.{u + 1} C) g
  have : (upperStar (ModuleCat.{u + 1} C) j).mapDerivedCategory.IsLeftAdjoint :=
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} C) j).isLeftAdjoint
  have hJ := compact_of_adjunction
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} C) j) K hK
  have (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I)
      G.rightDerivedFunctor.rightAdjoint := preservesCoproducts_closedRightAdjoint C g f I
  have hG := compact_of_adjunction (Adjunction.ofIsLeftAdjoint G.rightDerivedFunctor)
    (J.mapDerivedCategory.obj K) hJ
  let e := (G.rightDerivedFunctorIsoMapDerivedCategory.app
      (J.mapDerivedCategory.obj K)) ≪≫
    G.mapDerivedCategory.mapIso ((J.mapDerivedCategorySingleFunctor 0).app L) ≪≫
    (G.mapDerivedCategorySingleFunctor 0).app (J.obj L)
  exact compact_of_iso e hG

end AlgebraicGeometry.Etale
