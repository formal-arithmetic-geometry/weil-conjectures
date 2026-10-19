/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible
import Sheaf.Paper.IntegralModelsTensorClosure
import Sheaf.Paper.ConstantModelImmersionImages
import Sheaf.Paper.ConstantModelOpenProjection
import Sheaf.Paper.ConstantModelClosedProjection
import Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Operations on bounded constructible integral coefficient complexes

Source: blueprint main-20261015, sec-six-functors-basics, sk-lem-integral-models,
sk-lem-integral-models-operations.md (blueprint: det-lem-integral-models-operations).

Constructibility uses finite constant scalar models, as in the recorded
sk-def-sfb-constructible. The tensors and the projection formula are ambient and uncompleted.
-/

@[expose] public section

set_option autoImplicit false

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Mod.extendScalars
  AlgebraicGeometry.ProEtale.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
  AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private lemma localModel_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰, fun a ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 a
  exact ⟨P, hP, ⟨(upperStar Λ (𝒰.f a)).mapIso e.symm ≪≫ eP⟩⟩

private lemma constantConstructible_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split_ifs at hM ⊢ with hX
  · obtain ⟨S, hS⟩ := hM
    exact ⟨S, fun a ↦ localModel_iso Λ ((upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  · intro U hU
    obtain ⟨S, hS⟩ := hM U hU
    exact ⟨S, fun a ↦ localModel_iso Λ
      ((upperStar Λ (S.immersion a)).mapIso ((upperStar Λ U.ι).mapIso e)) (hS a)⟩

private lemma constantBounded_map
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ M, IsConstantModelConstructible Λ X M →
      IsConstantModelConstructible Λ Y (F.obj M))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (hK : constantModelBoundedConstructible Λ X K) :
    constantModelBoundedConstructible Λ Y (F.mapDerivedCategory.obj K) := by
  exact ⟨F.bounded_mapDerivedCategory_obj hK.1,
    fun n ↦ constantConstructible_iso Λ ((F.mapDerivedCategoryHomologyFunctorIso n).app K)
      (hF _ (hK.2 n))⟩

private lemma constantBounded_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (e : K ≅ M)
    (hK : constantModelBoundedConstructible Λ X K) :
    constantModelBoundedConstructible Λ X M := by
  exact ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e hK.1,
    fun n ↦ constantConstructible_iso Λ ((DerivedCategory.homologyFunctor _ n).mapIso e)
      (hK.2 n)⟩

private lemma constantBounded_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : ConstantModelPullbackStatement Λ)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hK : constantModelBoundedConstructible Λ Y K) :
    constantModelBoundedConstructible Λ X
      ((upperStar Λ f).mapDerivedCategory.obj K) := by
  exact constantBounded_map Λ (upperStar Λ f) (fun N hN ↦ (hΛ f N hN).1) K hK

private lemma constantBounded_immersion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S Z X : Scheme.{u}}
    [IsNoetherian S] [IsNoetherian Z] [IsNoetherian X]
    (j : S ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S))) (hL : constantModelBoundedConstructible Λ S L) :
    constantModelBoundedConstructible Λ X
      ((lowerStar Λ i).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L)) := by
  apply constantBounded_iso Λ
    (((lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory).app _).symm
  apply constantBounded_map Λ (lowerStar Λ i) ((constantModel_immersion_images Λ).2 i)
  exact constantBounded_map Λ (openImmersionLowerShriek Λ j)
    ((constantModel_immersion_images Λ).1 j) L hL

private lemma constant_projection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S Z X : Scheme.{u}}
    [IsNoetherian S] [IsNoetherian Z] [IsNoetherian X]
    (j : S ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    Nonempty ((((derivedTensor Λ X).obj
      ((lowerStar Λ i).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))).obj M) ≅
      (lowerStar Λ i).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj
          (((derivedTensor Λ S).obj L).obj
            ((upperStar Λ (j ≫ i)).mapDerivedCategory.obj M)))) := by
  let A := (openImmersionLowerShriek Λ j).mapDerivedCategory.obj L
  let N := (upperStar Λ i).mapDerivedCategory.obj M
  let ec := (Functor.mapDerivedCategoryNatIso (upperStarComp Λ j i) ≪≫
    Functor.mapDerivedCategoryCompIso (upperStar Λ i) (upperStar Λ j)).app M
  obtain ⟨ep⟩ := constantModel_closed_projection Λ i A M
  obtain ⟨eo⟩ := constantModel_open_projection Λ j L N
  exact ⟨ep ≪≫ (lowerStar Λ i).rightDerivedFunctor.mapIso eo ≪≫
    (lowerStar Λ i).rightDerivedFunctor.mapIso
      ((openImmersionLowerShriek Λ j).mapDerivedCategory.mapIso
        (((derivedTensor Λ S).obj L).mapIso ec.symm))⟩

/-- Inverse image, uncompleted relative derived tensor and locally closed extension by zero
preserve bounded constructibility over the integral coefficient ring. The projection formula
holds for arbitrary unbounded complexes. The locally closed functor is written explicitly as
open extension by zero followed by derived closed direct image; the latter is ordinary direct
image on Noetherian schemes. Finite coefficient fields are represented inside the fixed
algebraic closure, with their induced valuation and ring of integers.

Source: blueprint main-20261015, sk-lem-integral-models-operations, clauses (1)--(4)
(blueprint: det-lem-integral-models-operations).

Proof: use the four preservation and projection statements proved by the imported
constituents. All tensors below are ambient and uncompleted.

1. Exact module pullback commutes with derived homology and preserves cohomological
bounds. The existing pullback_constantModelConstructible theorem preserves each
cohomology sheaf's finite constant scalar models. Its coefficient admissibility
hypothesis is witnessed by E itself, with its given finite-dimensional structure.
This proves clause (1) without any finite-type or field-base assumption on the schemes.

2. The degree-zero calculation integralModels_sheaf_tensor compares finite constant
models with stratified local finite presentation. On a common finite stratification,
exact monoidal restriction and the local tensor calculation give cohomology in
[-1,0] with finite local presentation. Exact homology comparisons and stratum zero
detection descend these assertions, and the integral coefficient comparison returns
finite constant models. The integral heart is a weak Serre class, so bounded objects
with such cohomology form a triangulated subcategory. The theorem
integralModels_tensor_closure applies two finite truncation inductions, first fixing
a constructible sheaf in the second variable and then fixing the bounded first
variable. This proves clause (2), including the zero and empty-interval cases.

3. The theorem constantModel_immersion_images extends a finite stratification across
an open or closed immersion by adjoining the complementary locus with the zero
scalar model. Recollement identifies restrictions on the original strata and proves
vanishing on the complement. Exactness gives the same bounds and cohomology models
for the termwise derived functors. For a closed immersion, the comparison with its
total right derived functor is an isomorphism. Apply these statements first to open
extension and then to closed direct image to prove clause (3).

4. The open projection theorem follows from the natural open internal-Hom formula:
tensor-Hom and immersion adjunctions give the same right adjoint, so uniqueness of
left adjoints gives the tensor projection isomorphism. The closed projection theorem
transports the existing closed formula along the exact derived comparisons. Apply
that closed formula to j!L and M, then apply the open formula inside the closed
direct image. Finally the derived inverse-image composition isomorphism identifies
j*i*M with (j followed by i)*M. This proves clause (4) for arbitrary unbounded L,M.
The two projection isomorphisms impose no boundedness or constructibility condition.
-/
theorem integralModelsOperations (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        (((upperStar (Profinite.padicIntegersRingObj ℓ E.val) f).mapDerivedCategory).obj K)) ∧
    (∀ (X : Scheme.{u}) [IsNoetherian X] (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X M →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).obj K).obj M)) ∧
    (∀ {S Z X : Scheme.{u}} [IsNoetherian S] [IsNoetherian Z] [IsNoetherian X]
      (j : S ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
      (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) S))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) S L →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        (((lowerStar (Profinite.padicIntegersRingObj ℓ E.val) i).rightDerivedFunctor).obj
          (((openImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E.val)
            j).mapDerivedCategory).obj L))) ∧
    (∀ {S Z X : Scheme.{u}} [IsNoetherian S] [IsNoetherian Z] [IsNoetherian X]
      (j : S ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
      (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) S)))
      (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X))),
      Nonempty
        ((((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).obj
          (((lowerStar (Profinite.padicIntegersRingObj ℓ E.val) i).rightDerivedFunctor).obj
            (((openImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E.val)
              j).mapDerivedCategory).obj L))).obj M) ≅
          ((lowerStar (Profinite.padicIntegersRingObj ℓ E.val) i).rightDerivedFunctor).obj
            (((openImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E.val)
              j).mapDerivedCategory).obj
              (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) S).obj L).obj
                (((upperStar (Profinite.padicIntegersRingObj ℓ E.val) (j ≫
                  i)).mapDerivedCategory).obj M))))) := by
  have hcoeff : ∃ F : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] F ∧
        (Profinite.padicIntegersCondensedRing ℓ E.val =
          Profinite.padicIntegersCondensedRing ℓ F ∨
        Profinite.padicIntegersCondensedRing ℓ E.val =
          Profinite.padicSubfieldCondensedRing ℓ F) :=
    ⟨E.val, inferInstance, Or.inl rfl⟩
  have hΛ : ConstantModelPullbackStatement (Profinite.padicIntegersRingObj ℓ E.val) :=
    @pullback_constantModelConstructible ℓ _
      (Profinite.padicIntegersCondensedRing ℓ E.val) _
      (Or.inr (Or.inr (Or.inr (Or.inl hcoeff))))
  exact ⟨constantBounded_pullback (Profinite.padicIntegersRingObj ℓ E.val) hΛ,
    integralModels_tensor_closure ℓ E,
    constantBounded_immersion (Profinite.padicIntegersRingObj ℓ E.val),
    constant_projection (Profinite.padicIntegersRingObj ℓ E.val)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
