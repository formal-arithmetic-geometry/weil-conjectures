/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction
public import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Retract
public import Sheaf.Paper.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.AlgebraicGeometry.ClosedSupportStratumHom
import Sheaf.Paper.FormalClosedSupportDerived

/-!
# Sections with support in a closed subscheme

Source: blueprint `sec-six-functors-basics/sk-lem-formal-closed-support`,
using the derived closed-support and stratum-Hom interfaces
(blueprint: sk-lem-formal-closed-support).

The support functors are the canonical kernel and coefficient-compatible inverse-image
constructions from `FormalClosedSupportAdjunction`. The stratum formula uses the actual
extension `i_*u_!L`, the internal dual `Hom(L, Λ_S)`, and derived global sections. Finite
local projectivity means a retract of a finite free module on a pro-étale cover.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
  CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Global sections of a coefficient module, with its underlying abelian group.
Source: blueprint `sk-lem-formal-closed-support`, clause (2), the functor Γ(S,-)
(blueprint: sk-lem-formal-closed-support). The right derived functor of this composite is
RΓ(S,-); the scalar action is retained by the input module before taking sections. -/
noncomputable def formalClosedSupportSections (X : Scheme.{u}) :
    FormalSupportModules Λ X ⥤ Ab.{u + 1} :=
  Mod.forget (condensedRingObj Λ X) ⋙ Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1}

/-- Sections are additive, since both forgetful and global-sections functors preserve
finite products. Source: blueprint `sk-lem-formal-closed-support`, clause (2)
(blueprint: sk-lem-formal-closed-support). -/
noncomputable instance formalClosedSupportSections_additive (X : Scheme.{u}) :
    (formalClosedSupportSections Λ X).Additive :=
  Functor.additive_of_preserves_binary_products
    (Mod.forget (condensedRingObj Λ X) ⋙ Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1})

/-- The closed-support adjunction, fiber triangle and stratum formula.
Source: blueprint `sec-six-functors-basics/sk-lem-formal-closed-support`, clauses (1)--(2)
(blueprint: sk-lem-formal-closed-support).

The ordinary adjunction is normalized by the existing support-kernel inclusion;
`rightAdjoint_eq` specifies its derived adjunction, rather than an arbitrary rescaling.
`globalRHom` specifies the K-injective Hom-complex comparison of clause (1).
In `stratum`, the explicit covering-and-retract predicate is finite local projectivity:
after restriction to each member, L is a direct summand of Λ^n. The dual is the ordinary
internal Hom from L to the tensor unit, namely Λ_S. The displayed natural isomorphism of
functors in K is RHom_X(i_*u_!L,K) ≅ RΓ(S,L^∨ ⊗ u^*RΓ_Z K). Finite local projectivity makes
the ordinary tensor product in the source equal to the derived tensor used here. -/
structure FormalClosedSupportAssertions {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) where
  ordinaryAdjunction : lowerStar Λ i ⊣ formalClosedSupport Λ i j
  counit_normalization :
    ∀ M : FormalSupportModules Λ X,
      (formalSupportKernelComparison Λ i j).app M ≫ ordinaryAdjunction.counit.app M =
        (formalSupportKernelInclusion Λ j).app M
  rightAdjoint :
    (lowerStar Λ i).mapDerivedCategory ⊣
      (formalClosedSupport Λ i j).rightDerivedFunctor
  rightAdjoint_eq :
    rightAdjoint = ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction
  fiber :
    ∃ δ : (formalSupportPullback Λ j).mapDerivedCategory ⋙
        (lowerStar Λ j).rightDerivedFunctor ⟶
        ((formalClosedSupport Λ i j).rightDerivedFunctor ⋙
          (lowerStar Λ i).mapDerivedCategory) ⋙
          shiftFunctor (DerivedCategory (FormalSupportModules Λ X)) (1 : ℤ),
      ∀ K : DerivedCategory (FormalSupportModules Λ X),
        Triangle.mk (rightAdjoint.counit.app K)
          (((formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction).unit.app
            K)
          (δ.app K) ∈
          Pretriangulated.distinguishedTriangles
  globalRHom :
    ∀ (A : CochainComplex (FormalSupportModules Λ Z) ℤ)
      (I : CochainComplex (FormalSupportModules Λ X) ℤ) [I.IsKInjective],
      ∃ e : CochainComplex.HomComplex
          (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I ≅
        CochainComplex.HomComplex A
          (((formalClosedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I),
        ∀ (n : ℤ)
          (a : CochainComplex.HomComplex.Cochain
            (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I n)
          (p q : ℤ) (hpq : p + n = q),
          (e.hom.f n a) ⟨p, q, hpq⟩ =
            ordinaryAdjunction.homEquiv (A.X p) (I.X q) (a ⟨p, q, hpq⟩)
  stratum :
    ∀ {S : Scheme.{u}} (u : S ⟶ Z) [IsOpenImmersion u]
      (L : FormalSupportModules Λ S),
      (∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S,
        ∀ c : 𝒰.I₀, ∃ n : ℕ,
          Nonempty (Retract ((formalSupportPullback Λ (𝒰.f c)).obj L)
            (Mod.finiteFree (condensedRingObj Λ (𝒰.X c)) n))) →
      Nonempty
        ((derivedHom Λ X).obj
            (op ((DerivedCategory.singleFunctor (FormalSupportModules Λ X) 0).obj
              ((lowerStar Λ i).obj ((openImmersionLowerShriek Λ u).obj L)))) ⋙
            (formalClosedSupportSections Λ X).rightDerivedFunctor ≅
          (formalClosedSupport Λ i j).rightDerivedFunctor ⋙
            (formalSupportPullback Λ u).mapDerivedCategory ⋙
            (derivedTensor Λ S).obj
              ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj
                ((ihom L).obj (𝟙_ (FormalSupportModules Λ S)))) ⋙
            (formalClosedSupportSections Λ S).rightDerivedFunctor)

/-- Sections with support in a closed subscheme: derived adjunction, fiber formula, and the
extension-by-zero stratum Hom formula.
Source: blueprint `sec-six-functors-basics/sk-lem-formal-closed-support`, clauses (1)--(2)
(blueprint: sk-lem-formal-closed-support).

Proof:
1. Apply det-lem-formal-closed-support-derived in the standing-scheme setting. Its derived
adjunction, normalized by the support-kernel inclusion in
`formal_closed_support_adjunction`, gives `ordinaryAdjunction`, `counit_normalization`,
`rightAdjoint`, `rightAdjoint_eq` and `globalRHom`. Its natural localization triangle gives
`fiber`. Applying exact i^* and i^*i_* = id identifies RΓ_Z K with i^* of the fiber of the
canonical unit K → Rj_*j^*K. These give every assertion of clause (1).
2. Apply det-lem-formal-closed-support-stratum to u and the finite locally projective L.
The identity a_! = i_*u_! and the closed-support adjunction first give
RHom_X(i_*u_!L,K) ≅ RHom_Z(u_!L,RΓ_Z K). The exact open extension adjunction gives
RHom_S(L,u^*RΓ_Z K). Locally L is a retract of a finite free module, so its dual is flat
and Hom(L,-) = L^∨ ⊗ - is exact. The internal Hom and global-section comparison therefore
identify the last expression with RΓ(S,L^∨ ⊗ u^*RΓ_Z K). All comparisons are natural in K,
which gives the functor isomorphism in `stratum`. -/
theorem formalClosedSupportAssertions (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    {Z U X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    Nonempty (FormalClosedSupportAssertions Λ i j hij) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
