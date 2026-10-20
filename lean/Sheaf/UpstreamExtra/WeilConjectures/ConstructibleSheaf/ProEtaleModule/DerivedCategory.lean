module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible

/-! Declarations of ours that lived in the upstream file `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!

# Bounded constructible derived categories of sheaves of modules on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category, `X` a scheme, `R` a
commutative ring object of `Sheaf (Scheme.ProEt.topology X) A`. The derived category of
sheaves of `R`-modules is
```
D(X_proét, R) := DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R).
```
The *bounded constructible* derived category `ProEtale.BoundedConstructible R` is the full
subcategory of `D(X_proét, R)` (`ProEtale.boundedConstructible R`) consisting of the complexes
`K` such that

1. `K` is bounded, i.e. `Hⁱ(K) = 0` for `i` outside a finite interval (for the canonical
   t-structure, see `ProEtale.mem_boundedConstructible_iff`);
2. every cohomology sheaf `Hⁱ(K)` is constructible (`ProEtale.IsConstructibleModuleObject R`).

Morphisms are computed in `D(X_proét, R)`. For `R = 𝒪_{E,X}` this is `D_cons(X_proét, 𝒪_E)`;
for `R = E_X` it is `D_cons(X_proét, E)`.
No derived completeness condition is imposed.

## Triangulated structure

If the constructible `R`-modules are closed under kernels, cokernels and extensions, the
bounded constructible complexes form a triangulated subcategory
(`ProEtale.isTriangulated_boundedConstructible_of_serre`). These closure hypotheses concern the
coefficient ring as well as the scheme: noetherianity of the underlying space alone does
not imply them for an arbitrary `R`. The definition `ProEtale.boundedConstructible` makes
sense without them, on any scheme. Neither this definition nor its full subcategory is
changed by the closure hypotheses.

The proof uses the general weak Serre class construction of
`DerivedCategory.homologyProperty_isTriangulated`. Isomorphism invariance and the zero case
are proved directly from the finite presentation definition. The derived category itself
uses the instances of `WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`.

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

/- STATEMENT-DISPUTED: the original noetherian-only signature is false for arbitrary `R`.
Over a geometric point take the constant discrete ring k ⊕ V, with V an infinite-dimensional
k-vector space and V² = 0. Multiplication by a nonzero v ∈ V has kernel V, which is not
finitely generated, although its source and target are free of rank one. Its cone therefore
does not have locally finitely presented cohomology. The corrected instance below requires
the coefficient-dependent closure properties explicitly. -/

/-- Bounded constructible complexes form a triangulated subcategory whenever constructible
module objects are closed under kernels, cokernels and extensions.

Source: the weak Serre class argument in the proof of blueprint
`prop-constructible-derived-subcategory`, implemented by
`DerivedCategory.homologyProperty_isTriangulated`.
(blueprint: prop-weil-pbc-module-bounded-constructible-triangulated)

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
