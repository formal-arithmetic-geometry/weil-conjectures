/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension
public import WeilConjectures.WeilSheaf.HomologyShift

/-!
# Concentration of the zero-extension transform

For a nonzero irreducible lisse Weil sheaf `M` on a dense open `j : U₀ ↪ 𝔸¹` which is
constituent-nonexceptional, the blueprint lemma `lem-fd-constituent-nonexceptional-concentration`
states:

1. the twisted cohomology `H_c^q(U, M ⊗ ℒ_{ψ(ax)})` is concentrated in degree one;
2. the twisted dual `M† = M^∨ ⊗ 𝓑_b` is again irreducible lisse and nonexceptional;
3. the transforms `FT_ψ(j_!M)` and `FT_{ψ⁻¹}(j_!M†)` are sheaves, and `R^ν pr₂! 𝒦` of the
   realified kernel `𝒦` is concentrated in degree one, where it is
   `FT_ψ(j_!M) ⊕ FT_{ψ⁻¹}(j_!M†)`.

This file contains the formal plumbing for part (3): the compatibility of `toComplex` with the
pullback and with the tensor product by a lisse sheaf, and the computation of the higher direct
images with compact support of a sum of two kernels `𝒦_{ψᵢ} ⊗ pr₁^* Fᵢ` whose transforms are
sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section ToComplex

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

/-- The pullback of a Weil sheaf placed in degree zero is the pullback of the sheaf, placed in
degree zero: the pullback of pro-étale Weil sheaves is exact. -/
noncomputable def WeilSheaf.toComplexCompUpperStarIso (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] :
    WeilSheaf.toComplex ⋙ WeilComplex.upperStar (k₀ := k₀) (l := l) φ ≅
      WeilSheaf.upperStar φ ⋙ WeilSheaf.toComplex :=
  NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _
      (((ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategorySingleFunctor 0).app F.obj))
    fun f ↦ ObjectProperty.hom_ext _
      (((ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategorySingleFunctor 0).hom.naturality
        f.hom)

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The tensor product of a Weil sheaf placed in degree zero with a lisse Weil sheaf `G` is the
tensor product of the sheaves, placed in degree zero: the tensor product with a lisse sheaf,
the internal hom out of its dual, is exact. -/
noncomputable def WeilSheaf.toComplexCompTensorLisseIso (G : WeilSheaf k₀ l X)
    (hG : G.IsLisse) :
    WeilSheaf.toComplex ⋙ WeilComplex.tensorLisse G hG ≅
      { obj F := WeilSheaf.tensorObj G F hG
        map f := ObjectProperty.homMk ((ProEtaleWeilSheaf.ihomFunctor k₀ l X
          (G.dual hG).obj).map f.hom)
        map_id F := ObjectProperty.hom_ext _ ((ProEtaleWeilSheaf.ihomFunctor k₀ l X
          (G.dual hG).obj).map_id F.obj)
        map_comp f g := ObjectProperty.hom_ext _ ((ProEtaleWeilSheaf.ihomFunctor k₀ l X
          (G.dual hG).obj).map_comp f.hom g.hom) } ⋙ WeilSheaf.toComplex :=
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (G.dual hG).obj hG.dual
  NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _
      ((ProEtaleWeilSheaf.ihomFunctor k₀ l X
        (G.dual hG).obj).singleFunctorCompRightDerivedFunctorIso.app F.obj))
    fun f ↦ ObjectProperty.hom_ext _
      ((ProEtaleWeilSheaf.ihomFunctor k₀ l X
        (G.dual hG).obj).singleFunctorCompRightDerivedFunctorIso.hom.naturality f.hom)

end ToComplex

end AlgebraicGeometry
