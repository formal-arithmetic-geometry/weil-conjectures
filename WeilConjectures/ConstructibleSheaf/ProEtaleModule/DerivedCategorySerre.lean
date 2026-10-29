/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-!

# Bounded constructible complexes: the weak Serre class criterion

If the constructible module objects over a commutative ring object `R` of the pro-étale topos are
closed under kernels, cokernels and extensions, the bounded constructible complexes
(`ProEtale.boundedConstructible R`) form a triangulated subcategory
(`ProEtale.isTriangulated_boundedConstructible_of_serre`). This is the general form of the
per-ring instances of `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`. The proof
uses the weak Serre class construction `DerivedCategory.homologyProperty_isTriangulated`.

-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory MonObj Limits ZeroObject

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}}
  (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R] [IsCommMonObj R]

omit [IsCommMonObj R] in
private lemma constructible_of_iso
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) A) R} (e : M ≅ N)
    (hM : IsConstructibleModuleObject R M) : IsConstructibleModuleObject R N := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  obtain ⟨𝒰, h𝒰⟩ := hS a
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨n, m, f, ⟨e'⟩⟩ := h𝒰 i
  exact ⟨n, m, f, ⟨(((ProEtale.upperStar A (S.immersion a)).mapMod R ⋙
    (ProEtale.upperStar A (𝒰.f i)).mapMod _).mapIso e).symm ≪≫ e'⟩⟩

omit [IsCommMonObj R] in
private lemma locallyFinitelyPresented_of_isZero
    {M : Mod (Sheaf (Scheme.ProEt.topology X) A) R} (hM : IsZero M) :
    IsLocallyFinitelyPresented R M := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, 0, 𝟙 _, ⟨?_⟩⟩
  exact (((ProEtale.upperStar A _).mapMod R).map_isZero hM).iso
    (isZero_cokernel_of_epi (𝟙 _))

omit [IsCommMonObj R] in
private lemma constructible_of_isZero
    {M : Mod (Sheaf (Scheme.ProEt.topology X) A) R} (hM : IsZero M) :
    IsConstructibleModuleObject R M := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  refine ⟨S, fun a ↦ ?_⟩
  exact locallyFinitelyPresented_of_isZero _
    (((ProEtale.upperStar A _).mapMod R).map_isZero hM)


/-- Bounded constructible complexes form a triangulated subcategory whenever constructible
module objects are closed under kernels, cokernels and extensions.

Source: the weak Serre class argument in the proof of blueprint
`prop-constructible-derived-subcategory`, implemented by
`DerivedCategory.homologyProperty_isTriangulated`.
(auxiliary; not a blueprint node)

Proof: transport the presentations on every stratum and covering member across an
isomorphism to obtain isomorphism invariance. A zero module has the presentation given by
the cokernel of the identity on the rank-zero free module; the identity cover and the
one-stratum stratification show it is constructible. The weak Serre class theorem now
makes the property of having constructible cohomology triangulated. Intersect this with
the bounded part of the canonical t-structure, which is also triangulated. -/
instance (priority := 2000) isTriangulated_boundedConstructible_of_serre
    [ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject R)]
    [ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R)]
    [ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R)] :
    (boundedConstructible R).IsTriangulated := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleModuleObject R) :=
    ⟨fun e hM ↦ constructible_of_iso R e hM⟩
  have : ObjectProperty.ContainsZero (IsConstructibleModuleObject R) :=
    ⟨0, isZero_zero _, constructible_of_isZero R (isZero_zero _)⟩
  change (DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty (IsConstructibleModuleObject R)).IsTriangulated
  infer_instance

end AlgebraicGeometry.ProEtale
