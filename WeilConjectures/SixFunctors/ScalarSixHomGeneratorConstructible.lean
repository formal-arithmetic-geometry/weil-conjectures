/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open scoped CategoryTheory.Obj CategoryTheory.Functor
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The support-Hom formula for the native scalar Hom generator: the ambient Hom out of a
locally closed extension is the direct image of a local constructible finite-Tor object.
Source: blueprint det-prop-scalar-six-tensor-hom.proof.md, “The generator”, and
det-thm-sf-ctf-stability-internal-hom, proof Steps 6--10.
(blueprint: lem-sfb-native-scalar-hom-generator-constructible).
Proof: `X` is Noetherian, so `b` factors as `b = i ∘ u` with `u = b.toImage` open and
`i = b.imageι` closed, and `sfbLocallyClosedDerivedExtension Λ b hb = i_* u_!`. Take
`Q = RHom_S(P, b^!M)`. The open–closed internal-Hom formulas
[lem-sfb-open-closed-internal-hom-formulas] give
`RHom_X(i_* u_! P, M) ≅ i_* RHom_Z(u_! P, RΓ_Z M) ≅ i_* Ru_* RHom_S(P, u^* RΓ_Z M)`, and
`i_* Ru_* = Rb_*`; the support model identifies `u^* RΓ_Z M` with `b^!M` and puts it in
`Dctf(S, Λ)` (this is the sorried `locallyClosed_support_hom_model` of
det-thm-sf-ctf-stability-internal-hom, Steps 8--10). Since `P` is pro-étale locally a bounded
complex of finite projective scalar models, it is dualizable with dual `P^∨` of the same kind,
so `Q ≅ P^∨ ⊗ b^!M`; `P^∨` is constructible of Tor interval `[-h,-l]`
[lem-sfb-internal-hom-dual-tor-amplitude], and the tensor clause of
det-thm-sf-ctf-stability-direct-images (which uses no base-field cohomological dimension)
puts `Q` in `Dctf(S, Λ)`. If `S` is empty both sides are zero.
-/
theorem scalarSixHom_generator_constructible
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (M : ConstantModelConstructibleFiniteTor Λ.X X.left)
    (S : Scheme.{u}) (b : S ⟶ X.left) (hb : IsImmersion b)
    (P : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S))
    (hP : IsLocallyPerfectScalarModel Λ.X S P) :
    ∃ Q : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S),
      (constantModelBoundedConstructible Λ.X S Q ∧
          DerivedCategory.finiteTorAmplitude _ Q) ∧
        Nonempty
          ((((derivedHom Λ.X X.left).obj
              (.op ((sfbLocallyClosedDerivedExtension Λ b hb).obj P))).obj M.obj) ≅
            (R((b)_*⟦Λ.X⟧)).obj Q) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
