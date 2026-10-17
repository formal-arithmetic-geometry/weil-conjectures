/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierTateTwist
public import WeilConjectures.WeilSheaf.Stalk

/-!
# Stalks of the Fourier–Deligne transform at rational points

At a `k₀`-rational point `a` of the dual line, the stalk of the Fourier–Deligne transform of a
Weil complex `K` is the compactly supported cohomology of `K ⊗ ℒ_{ψ(a x)}`, shifted by one, with
its Frobenius: this is the stalk formula of the transform, a consequence of compact support base
change along `a : Spec k₀ ⟶ 𝔸¹`. At the origin the kernel `ℒ_{ψ(0 · x)}` is the constant sheaf,
and tensoring with it does nothing.

## Main declarations

- `AlgebraicGeometry.affineLine.rationalPoint`: the closed point `x = a` of `𝔸¹_{k₀}`.
- `AlgebraicGeometry.nonempty_equiv_stalk_homologySheaf_fourierTransform_rationalPoint`: the
  stalk formula at rational points, stated with `sorry` (blueprint `lem-fd-stalk-formula`).
- `AlgebraicGeometry.nonempty_iso_artinSchreier_zero`: `ℒ_{ψ(0 · x)} ≅ ℚ̄_ℓ`, stated with
  `sorry` (blueprint `lem-fd-as-characters`).
- `AlgebraicGeometry.WeilComplex.tensorLisseObjIsoOfIso`: tensoring with a Weil sheaf isomorphic
  to `ℚ̄_ℓ` is the identity.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable (k₀) in
/-- The `k₀`-rational point `x = a` of the affine line, as a closed point. -/
noncomputable def affineLine.rationalPoint (a : k₀) : (affineLine k₀).finitePoints :=
  ⟨(AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of k₀)))
      fun _ ↦ (Scheme.ΓSpecIso (.of k₀)).inv.hom a).base (IsLocalRing.closedPoint k₀),
    Scheme.Hom.mem_finitePoints_of_comp_eq_id (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) _
      (AffineSpace.homOfVector_over _ _) _⟩

namespace WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The derived internal hom `R𝓗om(F^∨, -)` out of the dual of a Weil sheaf `F ≅ ℚ̄_ℓ` is the
identity: `F^∨ ≅ 𝓗om(ℚ̄_ℓ, ℚ̄_ℓ) ≅ ℚ̄_ℓ`, the functor `𝓗om(ℚ̄_ℓ, -)` is the identity, and so is
its derived functor. -/
noncomputable def rightDerivedFunctorIhomFunctorDualIsoOfIso (F : WeilSheaf k₀ l X)
    (hF : F.IsLisse) (e : F ≅ WeilSheaf.adicConstant k₀ l X) :
    (ProEtaleWeilSheaf.ihomFunctor k₀ l X (F.dual hF).obj).rightDerivedFunctor ≅
      𝟭 (_root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :=
  have eD : (F.dual hF).obj ≅ ProEtaleWeilSheaf.adicConstant k₀ l X :=
    (ProEtaleWeilSheaf.ihomMapIsoLeft ((ObjectProperty.ι _).mapIso e).symm _) ≪≫
      ProEtaleWeilSheaf.ihomAdicConstantIso _
  Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.ihomFunctorMapIsoLeft eD.symm ≪≫
      ProEtaleWeilSheaf.ihomFunctorAdicConstantIso k₀ l X) ≪≫
    Functor.rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Tensoring with a lisse Weil sheaf `F ≅ ℚ̄_ℓ` does not change a Weil complex. -/
noncomputable def tensorLisseObjIsoOfIso (F : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (e : F ≅ WeilSheaf.adicConstant k₀ l X) (K : WeilComplex k₀ l X) :
    (tensorLisse F hF).obj K ≅ K :=
  ObjectProperty.isoMk _ ((rightDerivedFunctorIhomFunctorDualIsoOfIso F hF e).app K.obj)

end WeilComplex

/-- `ℒ_{ψ(0 · x)}`, the Artin–Schreier sheaf of the zero function, is the constant Weil sheaf
`ℚ̄_ℓ`: over the zero function the Artin–Schreier cover is split, `#k₀` copies of the line with
trivial Frobenius, so all the isotypic summands of the pushforward are constant. It is the unit
of the kernel family `ℒ_{ψ(a x)}`. (blueprint: `lem-fd-as-characters`, the case `f = 0`) -/
theorem nonempty_iso_artinSchreier_zero (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (artinSchreier ψ 0 ≅ WeilSheaf.adicConstant k₀ l (affineLine k₀)) :=
  sorry

/-- **Stalks of the Fourier transform are fibre integrals**, at the `k₀`-rational points of the
dual line: for a Weil complex `K` on `𝔸¹` and `a ∈ k₀`, the stalk of `𝓗ʳ FT_ψ(K)` at the point
`a` is `H_c^{r+1}(𝔸¹ ⊗ k̄, K ⊗ ℒ_{ψ(a x)})`, with its Frobenius. The fibre of the second
projection over `a` is the line `x ↦ (x, a)`, along which the kernel `μ^* ℒ_ψ` restricts to
`ℒ_{ψ(a x)}`, and compact support base change along `a : Spec k₀ ⟶ 𝔸¹` identifies the stalk of
`Rpr₂!` with the compactly supported cohomology of the fibre, compatibly with the Weil
structures; the shift `[1]` of the transform moves `r` to `r + 1`.
(blueprint: `lem-fd-stalk-formula`) -/
theorem nonempty_equiv_stalk_homologySheaf_fourierTransform_rationalPoint
    (ψ : AddChar k₀ (PadicAlgCl l)) (K : WeilComplex k₀ l (affineLine k₀)) (a : k₀) (r : ℤ) :
    Nonempty ((((WeilComplex.homologySheaf r).obj ((fourierTransform ψ).obj K)).stalk
      (affineLine.rationalPoint k₀ a)).Equiv
        (((WeilComplex.tensorLisse (artinSchreier ψ a) (isLisse_artinSchreier ψ a)).obj
          K).compactlySupportedCohomology (r + 1))) :=
  sorry

end AlgebraicGeometry
