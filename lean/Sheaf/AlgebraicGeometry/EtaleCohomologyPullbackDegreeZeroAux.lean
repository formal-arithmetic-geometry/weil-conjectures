module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Single

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace AlgebraicGeometry.Etale

/-- The augmentation induces an isomorphism on degree-zero sections cohomology.
Source: Stacks Project, Tag 05TD, proof of (3), and Tag 013K (injective resolutions).
(blueprint: lem-weil-pbc-cohomology-pullback-degree-zero-iso-factor)

Proof: Choose a nonnegative injective resolution s₀ : G[0] → I₀ and extend it by
zero to integer degrees. It is K-injective because it is bounded below with injective
terms. Global sections are additive and left exact: they are right adjoint to the
constant-sheaf functor. Thus Γ(G) identifies with the kernel of Γ(d₀⁰). There are no
boundaries in degree zero because I₀⁻¹ = 0. The cycle factor z₀ of Γ(s₀⁰) therefore
induces an isomorphism ε₀ : Γ(G) → H⁰(Γ(I₀)).

Since I is K-injective and s₀ is a quasi-isomorphism, lift s through s₀ to a chain map
a : I₀ → I with a homotopy s₀ ≫ a ∼ s. It is a quasi-isomorphism and a homotopy
equivalence between K-injective complexes: the localization functor from the homotopy
category is fully faithful on K-injective targets. Applying the additive functor Γ
preserves this homotopy equivalence, so H⁰(Γ(a)) is an isomorphism. The homotopy
s₀ ≫ a ∼ s says that their degree-zero components differ by d⁻¹h⁰ (the source is
concentrated in degree zero). After Γ this difference is a boundary. Hence
ε₀ ≫ H⁰(Γ(a)) = z ≫ homologyπ by the assumed equality hz. Both factors on the left
are isomorphisms, proving the assertion. This also covers complexes I with negative
terms: those terms contribute boundaries, rather than being assumed zero. The factor
z is uniquely determined by hz because iCycles is monic. -/
theorem isIso_degreeZeroCohomology_cycles_factor (T : Scheme.{u})
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (s : (CochainComplex.singleFunctor _ 0).obj G ⟶ I)
    [QuasiIso s] [I.IsKInjective]
    (z : (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G ⟶
      (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).cycles 0)
    (hz : z ≫ (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).iCycles 0 =
      (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ s.f 0)) :
    IsIso (z ≫ (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homologyπ 0) := by
  sorry

end AlgebraicGeometry.Etale
