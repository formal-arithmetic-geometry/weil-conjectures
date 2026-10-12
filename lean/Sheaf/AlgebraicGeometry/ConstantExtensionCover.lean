/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.ConstantEtaleSheafShortExact
import Sheaf.AlgebraicGeometry.EtaleShortExactLocalLift
import WeilConjectures.ConstructibleSheaf.Biproduct
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-!
# Local presentations of extensions with finite constant outer terms

Source: Stacks Project, Etale Cohomology Tag 03RX (3), via Modules on Sites Tag 093U.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- An extension with constant outer terms of finite stalks has a cover on which its middle
term is constant. Source: Stacks Project, Tags 03RX (3) and 093U.
(blueprint: lem-constructible-constant-extension-cover)

Proof: Discard empty members of covers. Write the outer terms as constant sheaves M and N.
Their values are finitely generated, since they identify with geometric stalks on a nonempty
scheme. Choose a finite free presentation Λ^m → N, with kernel K. The finite ring hypothesis
makes K and Λ^m finite. The epimorphism from the middle term to N admits simultaneous local
lifts of the finitely many generators by local surjectivity and intersection of their covering
sieves. These lifts give a morphism r from the constant sheaf Λ^m to the middle term. Its
restriction to K factors through M, defining g. Exactness of the constant sheaf functor makes
the middle term the cokernel of (-g, inclusion): K → M ⊞ Λ^m: the quotient map sends (a,v)
to a+r(v); it is epi, and its kernel consists of pairs (-g(k),k). On a further cover, the
morphism g between finite constant sheaves is induced by a module homomorphism, by the
constant morphism lemma. The displayed cokernel is then the constant sheaf of its module
cokernel. The composite covers give the asserted cover. Empty schemes admit the empty cover;
no splitting of the original extension is asserted. -/
theorem exists_constantExtension_cover {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]
    [Finite Λ] {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hS : S.ShortExact)
    [S.X₁.IsConstant X.smallEtaleTopology] [S.X₃.IsConstant X.smallEtaleTopology]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i,
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂).IsConstant
        (𝒰.X i).smallEtaleTopology := by sorry

end AlgebraicGeometry.Scheme
