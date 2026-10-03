/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Compactly supported cohomology of Weil complexes

Let `k₀` be a finite field with algebraic closure `k̄` and geometric Galois Frobenius
`σ : Spec k̄ ≅ Spec k̄`. A Weil complex `(M, φ : σ^* M ≅ M)` on `Spec k₀` has cohomology
groups `Hʳ(Spec k̄, M)`, and these carry a Frobenius

`Hʳ(Spec k̄, M) ≅ Hʳ(Spec k̄, σ^* M) ≅ Hʳ(Spec k̄, M)`,

whose first isomorphism is the invariance of derived global sections under the automorphism
`σ` and whose second one is induced by `φ`. The compactly supported cohomology of a Weil complex
`K` on a `k₀`-scheme `X` with structure morphism `a : X ⟶ Spec k₀` is the cohomology
`H_c^r(X ⊗ k̄, K) := Hʳ(Spec k̄, Ra_! K)` of its direct image with compact support
(`AlgebraicGeometry.WeilComplex.derivedLowerShriek`), with this Frobenius.

## Main declarations

- `AlgebraicGeometry.Etale.rightDerivedGlobalSectionsIsoOfIso`: `D(σ^*) ⋙ RΓ ≅ RΓ` for an
  automorphism `σ`.
- `AlgebraicGeometry.WeilComplex.cohomologyFrobeniusModule`: the cohomology of a Weil complex on
  `Spec k₀` as a Frobenius module.
- `AlgebraicGeometry.WeilComplex.compactlySupportedCohomology` and
  `AlgebraicGeometry.WeilSheaf.compactlySupportedCohomology`: compactly supported cohomology
  with its geometric Frobenius.
- `AlgebraicGeometry.WeilComplex.compactlySupportedCohomologyIso`: its comparison with the
  étale compactly supported cohomology `H_c(ā)[Λ](r)` of the underlying complex.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Etale

section GlobalSections

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- Global sections are invariant under pushforward along a morphism `g : X ⟶ Y`:
`Γ(Y, g_* F) = F(X ×_Y Y) ≅ F(X) = Γ(X, F)`. -/
noncomputable def lowerStarCompGlobalSectionsIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (g)_*[A] ⋙ Sheaf.Γ Y.smallEtaleTopology A ≅ Sheaf.Γ X.smallEtaleTopology A :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal) ≪≫
    NatIso.ofComponents
      (F := (g)_*[A] ⋙ (sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale)))
      (G := (sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale)))
      (fun H ↦ H.obj.mapIso (PreservesTerminal.iso g.Etale).op.symm)
      (fun α ↦ (α.hom.naturality _).symm) ≪≫
    (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).symm

variable {X : Scheme.{u}} (σ : X ≅ X)

/-- Global sections are invariant under pullback along an automorphism `σ`:
`Γ(X, σ^* F) ≅ Γ(X, σ⁻¹_* F) ≅ Γ(X, F)`. -/
noncomputable def upperStarCompGlobalSectionsIsoOfIso :
    (σ.hom)^*[A] ⋙ Sheaf.Γ X.smallEtaleTopology A ≅ Sheaf.Γ X.smallEtaleTopology A :=
  Functor.isoWhiskerRight (upperStarInvIsoLowerStarHom A σ.symm) _ ≪≫
    lowerStarCompGlobalSectionsIso A σ.inv

/-- Derived global sections are invariant under the derived pullback along an automorphism
`σ`: `RΓ ∘ D(σ^*) ≅ RΓ ∘ R(σ^*) ≅ R(Γ ∘ σ^*) ≅ RΓ`, the middle isomorphism being the
composition of right derived functors, which applies since the equivalence `σ^*` preserves
K-injective complexes. -/
noncomputable def rightDerivedGlobalSectionsIsoOfIso :
    ((σ.hom)^*[A]).mapDerivedCategory ⋙ rightDerivedGlobalSections A X ≅
      rightDerivedGlobalSections A X :=
  Functor.isoWhiskerRight ((σ.hom)^*[A]).rightDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
    Functor.rightDerivedFunctorCompIso' _ _ (upperStarCompGlobalSectionsIsoOfIso A σ)

end GlobalSections

end Etale

open Etale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

/-- The `r`-th cohomology `Hʳ(Spec k̄, M)` of a Weil complex `(M, φ)` on `Spec k₀`, as a
Frobenius module: the `r`-th cohomology of the derived global sections of `M` on the geometric
fiber `Spec k̄`, with the Frobenius

`Hʳ(Spec k̄, M) ≅ Hʳ(Spec k̄, σ^* M) --Hʳ(φ)--> Hʳ(Spec k̄, M)`,

where `σ` is the geometric Galois Frobenius of `Spec k̄` and the first isomorphism is
`Etale.rightDerivedGlobalSectionsIsoOfIso`. -/
noncomputable def cohomologyFrobeniusModule (r : ℤ)
    (M : WeilComplex k₀ l (Spec (CommRingCat.of k₀))) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  let H := rightDerivedGlobalSections (WeilCoefficients.{u} l) _ ⋙
    DerivedCategory.homologyFunctor (WeilCoefficients.{u} l) r
  have : FiniteDimensional (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj (H.obj M.obj.carrier)) := sorry
  { carrier := (WeilCoefficients.toModuleCat l).obj (H.obj M.obj.carrier)
    frobenius := WeilCoefficients.linearEquivOfIso
      ((DerivedCategory.homologyFunctor _ r).mapIso
          ((rightDerivedGlobalSectionsIsoOfIso _
            (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius).app
              M.obj.carrier).symm ≪≫
        H.mapIso M.obj.str) }

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

-- TODO(unify): sk-thm-sf-global-duality
/-- The compactly supported cohomology `H_c^r(X ⊗ k̄, K) := Hʳ(Spec k̄, Ra_! K)` of a Weil
complex `K` on a separated `k₀`-scheme `a : X ⟶ Spec k₀` of finite type, with its geometric
Frobenius: the cohomology of the direct image with compact support of `K` along `a`, a Weil
complex on `Spec k₀`. -/
noncomputable def compactlySupportedCohomology (r : ℤ) (K : WeilComplex k₀ l X) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  cohomologyFrobeniusModule r
    ((WeilComplex.derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj K)

/-- The underlying vector space of the compactly supported cohomology of a Weil complex `K` is
the étale compactly supported cohomology `H_c(ā)[Λ](r)` of the underlying complex on `X ⊗ k̄`
along the base change `ā : X ⊗ k̄ ⟶ Spec k̄` of the structure morphism. -/
theorem nonempty_compactlySupportedCohomology_linearEquiv (r : ℤ) (K : WeilComplex k₀ l X) :
    Nonempty ((compactlySupportedCohomology r K).carrier ≃ₗ[PadicAlgCl l]
      (WeilCoefficients.toModuleCat l).obj
        ((H_c(Scheme.Hom.geometricFiberMap (X ↘ Spec (CommRingCat.of k₀))
          (comp_over _ _))[WeilCoefficients.{u} l](r)).obj K.obj.carrier)) :=
  sorry

end WeilComplex

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The compactly supported cohomology `H_c^r(X ⊗ k̄, F)` of a Weil sheaf, with its geometric
Frobenius: that of the Weil complex `F` concentrated in degree zero. -/
noncomputable def compactlySupportedCohomology (r : ℤ) (F : WeilSheaf k₀ l X) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  (WeilSheaf.toComplex.obj F).compactlySupportedCohomology r

end WeilSheaf

end AlgebraicGeometry
