/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
import Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.KInjectiveResolutions
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Unbounded evaluation on finitely many clopen geometric sections

Source: Stacks Project, Tags 070Y, 015F, 070H and 09T5; the finite-clopen calculation
in the geometric-fibre argument of blueprint main-20261015, prop-asd-smooth-base-change,
coherence (iii) (blueprint: lem-asd-clopen-geometric-sections-derived-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The exact inverse-image comparison along a section, descended with the canonical
composition and identity comparisons. Source: Stacks, Tag 09T5
(blueprint: lem-asd-clopen-geometric-sections-derived-evaluation). -/
noncomputable def clopenSectionPullbackIso (A : Type (u + 1)) [CommRing A]
    {P V : Scheme.{u}} (r : V ⟶ P) (s : P ⟶ V) (hs : s ≫ r = 𝟙 P) :
    D((r)^*[ModuleCat A]) ⋙ D((s)^*[ModuleCat A]) ≅
      𝟭 (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat A))) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat A) s r (𝟙 P) hs.symm).symm ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat A) P) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Restriction along a section of the total derived direct image: apply the section
comparison and restrict the canonical derived counit. Source: Stacks, Tags 070Y and 09T5
(blueprint: lem-asd-clopen-geometric-sections-derived-evaluation). -/
noncomputable def clopenSectionDerivedRestriction (A : Type (u + 1)) [CommRing A]
    {P V : Scheme.{u}} (r : V ⟶ P) (s : P ⟶ V) (hs : s ≫ r = 𝟙 P) :
    R((r)_*[ModuleCat A]) ⟶ D((s)^*[ModuleCat A]) :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (clopenSectionPullbackIso A r s hs).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (mapDerivedUpperStarLowerStarAdjunction (ModuleCat A) r).counit _ ≫
    (Functor.leftUnitor _).hom

/-- The canonical restriction to all section components, with values in their finite
product. Source: Stacks, Tags 070Y and 015F, finite-clopen calculation
(blueprint: lem-asd-clopen-geometric-sections-derived-evaluation). -/
noncomputable def clopenGeometricEvaluation (A : Type (u + 1)) [CommRing A]
    {P V : Scheme.{u}} (r : V ⟶ P) {I : Type u} [Finite I]
    (s : I → (P ⟶ V)) (hs : ∀ i, s i ≫ r = 𝟙 P)
    (M : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat A))) :
    (R((r)_*[ModuleCat A])).obj M ⟶ ∏ᶜ (fun i ↦ (D((s i)^*[ModuleCat A])).obj M) :=
  Pi.lift (fun i ↦ (clopenSectionDerivedRestriction A r (s i) (hs i)).app M)

/-- The union of pairwise disjoint clopen geometric sections is a clopen immersion, and
its structure map to the point is étale. Source: Stacks, finite-clopen geometric-fibre
calculation (blueprint: lem-asd-clopen-geometric-sections-derived-evaluation).
Proof: the coproduct injections identify the coproduct with the disjoint union of the
open images. Their finite union is closed. On each component the structure map is the
identity, so it is étale, also for the empty coproduct. -/
theorem clopenGeometricSections_union (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    {V : Scheme.{u}} (r : V ⟶ Spec (.of Ω)) {I : Type u} [Finite I]
    (s : I → (Spec (.of Ω) ⟶ V)) [∀ i, IsOpenImmersion (s i)]
    (hclosed : ∀ i, IsClosed (Set.range (s i)))
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (s i)) (Set.range (s k))))
    (hs : ∀ i, s i ≫ r = 𝟙 _) :
    IsOpenImmersion (Sigma.desc s) ∧ IsClosedImmersion (Sigma.desc s) ∧
      Etale (Sigma.desc s ≫ r) := by
  sorry

/-- Degreewise étale sum extension on the ordinary unbounded derived categories.
The instances are supplied by its recorded exact left adjunction, without choosing
another extension functor. Source: Stacks, Tags 03S3 and 03S5
(blueprint: lem-asd-clopen-geometric-sections-derived-evaluation). -/
noncomputable def clopenEtaleDerivedSum (A : Type (u + 1)) [CommRing A]
    {U P : Scheme.{u}} (v : U ⟶ P) (hv : Etale v) :
    DerivedCategory (Sheaf (U).smallEtaleTopology (ModuleCat A)) ⥤
      DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat A)) :=
  let F := etaleLowerShriek (ModuleCat A) v hv
  let adj := etaleLowerShriekUpperStarAdjunction (ModuleCat A) v hv
  letI : F.IsLeftAdjoint := adj.isLeftAdjoint
  letI : F.Additive := adj.left_adjoint_additive
  letI : F.PreservesHomology := {}
  F.mapDerivedCategory

/-- The canonical degreewise derived sum/restriction adjunction. Source: Stacks, Tags
03S5 and 015F (blueprint: lem-asd-clopen-geometric-sections-derived-evaluation). -/
noncomputable def clopenEtaleDerivedSumAdjunction (A : Type (u + 1)) [CommRing A]
    {U P : Scheme.{u}} (v : U ⟶ P) (hv : Etale v) :
    clopenEtaleDerivedSum A v hv ⊣ D((v)^*[ModuleCat A]) :=
  let F := etaleLowerShriek (ModuleCat A) v hv
  let adj := etaleLowerShriekUpperStarAdjunction (ModuleCat A) v hv
  letI : F.IsLeftAdjoint := adj.isLeftAdjoint
  letI : F.Additive := adj.left_adjoint_additive
  letI : F.PreservesHomology := {}
  adj.mapDerivedCategoryAdjunction

/-- Identify restriction of `K` to a coproduct component with restriction of `Dj_! K`
to the same section of the ambient scheme, using the actual open-adjunction unit.
Source: Stacks, Tag 03S4 (blueprint: lem-asd-clopen-geometric-sections-derived-evaluation). -/
noncomputable def clopenGeometricComponentIso (A : Type (u + 1)) [CommRing A]
    {P U V : Scheme.{u}} (t : P ⟶ U) (j : U ⟶ V) [IsOpenImmersion j]
    (s : P ⟶ V) (h : t ≫ j = s)
    (K : DerivedCategory (Sheaf (U).smallEtaleTopology (ModuleCat A))) :
    (D((t)^*[ModuleCat A])).obj K ≅
      (D((s)^*[ModuleCat A])).obj ((D((j)_!open[ModuleCat A])).obj K) :=
  (D((t)^*[ModuleCat A])).mapIso
      ((asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).unit).app K) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm.app _ ≪≫
    (Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat A) t j s h.symm).symm).app _

/-- The canonical injection of a component into the étale sum, defined by restricting
the unit of sum extension and applying the section identity comparison.
Source: Stacks, Tags 03S5 and 09T5
(blueprint: lem-asd-clopen-geometric-sections-derived-evaluation). -/
noncomputable def clopenGeometricSumInjection (A : Type (u + 1)) [CommRing A]
    {P U V : Scheme.{u}} (t : P ⟶ U) (j : U ⟶ V) [IsOpenImmersion j]
    (s : P ⟶ V) (h : t ≫ j = s) (v : U ⟶ P) (hv : Etale v)
    (ht : t ≫ v = 𝟙 P)
    (K : DerivedCategory (Sheaf (U).smallEtaleTopology (ModuleCat A))) :
    (D((s)^*[ModuleCat A])).obj ((D((j)_!open[ModuleCat A])).obj K) ⟶
      (clopenEtaleDerivedSum A v hv).obj K :=
  (clopenGeometricComponentIso A t j s h K).inv ≫
    (D((t)^*[ModuleCat A])).map
      ((clopenEtaleDerivedSumAdjunction A v hv).unit.app K) ≫
    (clopenSectionPullbackIso A v t ht).hom.app _

section Evaluation

variable (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (A : Type (u + 1)) [CommRing A]
  {V : Scheme.{u}} (r : V ⟶ Spec (.of Ω)) {I : Type u} [Finite I]
  (s : I → (Spec (.of Ω) ⟶ V)) [∀ i, IsOpenImmersion (s i)]
  (hclosed : ∀ i, IsClosed (Set.range (s i)))
  (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (s i)) (Set.range (s k))))
  (hs : ∀ i, s i ≫ r = 𝟙 _)

local notation "P" => Spec (CommRingCat.of Ω)
local notation "U" => ∐ (fun _ : I ↦ P)
local notation "j" => Sigma.desc s
local notation "v" => j ≫ r
local notation "t" => Sigma.ι (fun _ : I ↦ P)

/-- The derived finite-clopen calculation, its K-injective normalization, and the
specified finite-sum adjunct, including the empty family and unbounded complexes.
Source: Stacks, Tags 070H, 070I, 070K, 070Y, 015F, 03S3, 03S5 and 09T5; blueprint
main-20261015, prop-asd-smooth-base-change, coherence (iii)
(blueprint: lem-asd-clopen-geometric-sections-derived-evaluation).

Proof:
1. The disjoint open images and their open complement form a finite coproduct cover.
   Apply lem-weil-pbc-etale-sheaf-clopen-product. Module actions and their identities
   are recovered componentwise; the equivalence is exact and extends degreewise.
2. Inverse image is restriction (lem-weil-pbc-etale-inverse-image-restriction).
   By lem-weil-pbc-extension-by-zero-adjunction the open extension is the tuple of
   the component modules and zero on the complement. Exactness gives the same
   description for all complexes, without a boundedness assumption.
3. Hom complexes are finite products of the component Hom complexes. Finite products
   compute cycles and boundaries componentwise, so K-injectivity is detected on the
   pieces. Conversely test on complexes supported on just one piece.
4. Resolve the point components by prop-weil-pbc-kinjective-resolutions-exist and use
   zero on the complement. The assembled map is a quasi-isomorphism into a K-injective.
   By lem-weil-pbc-kinjective-total-derived this computes Rr_*; sectionwise direct
   image is the finite product, with restriction along the specified sections.
5. By lem-weil-pbc-kinjective-hom-derived, chain maps modulo homotopy compute all
   derived morphisms between these resolutions, proving naturality and independence
   of the resolutions. The exact global-sections equivalence of
   lem-weil-pbc-geometric-point-pullback-stalk and the canonical comparison of
   lem-weil-pbc-exact-functor-derived-functor preserve this normalization.
6. By lem-weil-pbc-etale-restriction-injectives, exact sum extension is left adjoint
   to diagonal restriction. Its unit gives exactly the component injections below,
   identifying its value with the finite biproduct. Glue the projections on the
   point components and zero on the complement to obtain delta.
7. The canonical derived adjunction of lem-pc-derived-adjoint-functors is computed
   degreewise on the resolutions, since inverse image is exact by
   prop-weil-pbc-inverse-image-modules-exact. Its adjunct has each projection equal
   to the indicated biproduct projection. It is thus the canonical finite
   sum-to-product map, hence invertible and the identity after the biproduct
   identification. For the empty family every object and map here is zero. -/
theorem clopenGeometricSections_derivedEvaluation :
    letI : IsOpenImmersion j := (clopenGeometricSections_union Ω r s hclosed hdisjoint hs).1
    letI : IsClosedImmersion j :=
      (clopenGeometricSections_union Ω r s hclosed hdisjoint hs).2.1
    let hv := (clopenGeometricSections_union Ω r s hclosed hdisjoint hs).2.2
    let Z := Scheme.openComplementOfIsClosedImmersion j
    let E := D((j)_!open[ModuleCat A])
    let B := clopenEtaleDerivedSum A v hv
    let Ki := fun K i ↦ (D((s i)^*[ModuleCat A])).obj (E.obj K)
    (∀ J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat A)) ℤ,
      J.IsKInjective ↔
        (∀ i, CochainComplex.IsKInjective
          ((((s i)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J)) ∧
        CochainComplex.IsKInjective
          ((((Z.ι)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J)) ∧
    (∀ C : CochainComplex (Sheaf (U).smallEtaleTopology (ModuleCat A)) ℤ,
      ∃ (J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat A)) ℤ)
        (q : (((j)_!open[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj C ⟶ J),
        QuasiIso q ∧ J.IsKInjective ∧
          IsZero ((((Z.ι)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J) ∧
          (∀ i, CochainComplex.IsKInjective
            ((((s i)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J))) ∧
    (∀ K, IsZero ((D((Z.ι)^*[ModuleCat A])).obj (E.obj K))) ∧
    (∀ K, IsIso (clopenGeometricEvaluation A r s hs (E.obj K))) ∧
    (∀ K L (f : K ⟶ L),
      (R((r)_*[ModuleCat A])).map (E.map f) ≫
          clopenGeometricEvaluation A r s hs (E.obj L) =
        clopenGeometricEvaluation A r s hs (E.obj K) ≫
          CategoryTheory.Limits.Pi.map (fun i ↦ (D((s i)^*[ModuleCat A])).map (E.map f))) ∧
    ((sheafSections (P).smallEtaleTopology (ModuleCat A)).obj
      (op (Scheme.Etale.mk (𝟙 P)))).IsEquivalence ∧
    ∃ (e : ∀ K, B.obj K ≅ ⨁ (Ki K))
      (δ : ∀ K, (D((r)^*[ModuleCat A])).obj (B.obj K) ⟶ E.obj K),
      (∀ K i, biproduct.ι (Ki K) i ≫ (e K).inv =
        clopenGeometricSumInjection A (t i) j (s i) (Sigma.ι_desc s i) v hv
          (by rw [← Category.assoc, Sigma.ι_desc]; exact hs i) K) ∧
      (∀ K L (f : K ⟶ L), B.map f ≫ (e L).hom =
        (e K).hom ≫ biproduct.map (fun i ↦ (D((s i)^*[ModuleCat A])).map (E.map f))) ∧
      (∀ K i, (D((s i)^*[ModuleCat A])).map (δ K) =
        (clopenSectionPullbackIso A r (s i) (hs i)).hom.app (B.obj K) ≫
          (e K).hom ≫ biproduct.π (Ki K) i) ∧
      (∀ K, (D((Z.ι)^*[ModuleCat A])).map (δ K) = 0) ∧
      (∀ K L (f : K ⟶ L),
        (D((r)^*[ModuleCat A])).map (B.map f) ≫ δ L = δ K ≫ E.map f) ∧
      (∀ K,
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat A) r).homEquiv _ _ (δ K) ≫
            clopenGeometricEvaluation A r s hs (E.obj K) =
          (e K).hom ≫ Pi.lift (fun i ↦ biproduct.π (Ki K) i)) ∧
      (∀ K, IsIso
        ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat A) r).homEquiv _ _ (δ K))) := by
  sorry

end Evaluation

end AlgebraicGeometry.Etale
