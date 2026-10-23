/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.TateTwist.RootsOfUnity

/-!

# Tate twists of `ℓ`-adic coefficient sheaves on the pro-étale site

Let `ℓ` be a prime, `X` a scheme and `Λ` a commutative condensed ring under the condensed ring
`ℤ̲_ℓ = C(-, ℤ_ℓ)`, through a ring map `φ : ℤ̲_ℓ ⟶ Λ`; the admissible `ℓ`-adic coefficient rings
`ℚ̲̄_ℓ`, `𝒪̲_E` and `E̲` are such, through `Profinite.padicIntRingObjToPadicAlgCl`,
`Profinite.padicIntRingObjToPadicIntegers` and `Profinite.padicIntRingObjToNormedExtension`.
This file constructs the Tate twists `Λ_X(d)`, `d ∈ ℤ`, as module objects over the coefficient
ring object `Λ_X = p_X^* Λ` (`AlgebraicGeometry.ProEtale.condensedRingObj Λ X`) of abelian
sheaves on `X_proét`, following Bhatt–Scholze, *The pro-étale topology for schemes*,
Section 6.8, and blueprint `sk-def-sp-tate-twist`:
```
ℤ_ℓ(1) := lim_n μ_{ℓ^n},     Λ(1) := Λ ⊗_{ℤ_ℓ} ℤ_ℓ(1),
```
where `ℤ_ℓ = ℤ_ℓ,X = p_X^* ℤ̲_ℓ` is the pullback of the condensed ring `ℤ̲_ℓ`.

## The construction

* The `ℤ_ℓ,X`-module `ℤ/ℓ^n(1)` is the free module `ℤ_ℓ,X ⊗ μ_{ℓ^n}` on the sheaf `μ_{ℓ^n}` of
  `ℓ^n`-th roots of unity (`AlgebraicGeometry.ProEtale.rootsOfUnitySheaf`), the tensor product
  being the sheafified tensor product of abelian sheaves. Since `μ_{ℓ^n}` is killed by `ℓ^n`, this
  is `ℤ/ℓ^n ⊗_{ℤ/ℓ^n} μ_{ℓ^n} = μ_{ℓ^n}` as an abelian sheaf, with its natural structure of a
  module over `ℤ_ℓ,X ⟶ ℤ/ℓ^n` (`AlgebraicGeometry.ProEtale.tateModuleLevel`). Taking the free
  module avoids defining the action of `ℤ_ℓ,X` on `μ_{ℓ^n}` by hand.
* `ℤ_ℓ(1)` is the limit, in the category of `ℤ_ℓ,X`-module objects, of the inverse system
  `ℤ_ℓ ⊗ μ_{ℓ^{n+1}} ⟶ ℤ_ℓ ⊗ μ_{ℓ^n}` induced by the `ℓ`-th power maps
  (`AlgebraicGeometry.ProEtale.tateModule`).
* `Λ(1)` is the extension of scalars of `ℤ_ℓ(1)` along the coefficient change
  `φ_X : ℤ_ℓ,X ⟶ Λ_X` (`AlgebraicGeometry.ProEtale.coefficientMap`), i.e. the relative tensor
  product `Λ_X ⊗_{ℤ_ℓ,X} ℤ_ℓ(1)` (`AlgebraicGeometry.ProEtale.tateTwistOne`). The tensor product
  has to be taken over `ℤ_ℓ,X` and not over `ℤ`: `ℚ̄_ℓ ⊗_ℤ μ_{ℓ^n} = 0`, and `ℚ̄_ℓ ⊗_ℤ ℤ_ℓ(1)` is
  much larger than `ℚ̄_ℓ(1)`.
* For `d ≥ 0`, `Λ(d)` is the `d`-th tensor power of `Λ(1)` over `Λ_X`, and for `d < 0` it is the
  dual `Hom_{Λ}(Λ(-d), Λ)` (`AlgebraicGeometry.ProEtale.tateTwist`).

Finally `Λ_X(d)` is placed in degree `0` of the derived category `D(Mod_{Λ_X})`
(`AlgebraicGeometry.ProEtale.tateTwistDerived`), and the twist functor `K ↦ K(d)` on
`D(Mod_{Λ_X})` is the derived tensor product with it
(`AlgebraicGeometry.ProEtale.tateTwistFunctor`).

## Implementation notes

* The construction is functorial in nothing: the comparisons `f^* Λ_Y(d) ≅ Λ_X(d)` and the
  invertibility `Λ(d) ⊗ Λ(e) ≅ Λ(d + e)` are not stated here. The local triviality of `Λ(d)`
  when `ℓ` is invertible on `X`, and the resulting constructibility, are in
  `WeilConjectures.TateTwist.ProEtaleConstructible`.
* The Galois (Frobenius) action on `ℚ̄_ℓ(1)` for `X` over a finite field, which is what
  distinguishes `ℚ̄_ℓ(d)` from `ℚ̄_ℓ` over a separably closed field, is part of the Weil sheaf
  formalism and is not considered.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory MonObj Limits

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` -/

/-- The inclusion `ℤ_ℓ ⊆ ℚ_ℓ`, as a ring homomorphism into the bottom finite subextension
`ℚ_ℓ ⊆ ℚ̄_ℓ`. -/
noncomputable def padicIntToBotFiniteIntermediateField :
    ℤ_[ℓ] →+* (⟨⊥, inferInstance⟩ : PadicAlgCl.FiniteIntermediateField ℓ) :=
  (algebraMap ℚ_[ℓ] (⊥ : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))).comp PadicInt.Coe.ringHom

lemma continuous_padicIntToBotFiniteIntermediateField :
    Continuous (padicIntToBotFiniteIntermediateField ℓ) :=
  continuous_induced_rng.2
    ((continuous_algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp continuous_subtype_val)

/-- The inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` of condensed rings: a continuous map `S → ℤ_ℓ` is a section of
`ℚ̲̄_ℓ` over `S`, with values in the finite subextension `ℚ_ℓ`. -/
noncomputable def padicIntCondensedRingToPadicAlgCl :
    padicIntCondensedRing.{u} ℓ ⟶ padicAlgClCondensedRing ℓ :=
  continuousMapRingSheafMap (padicIntToBotFiniteIntermediateField ℓ)
      (continuous_padicIntToBotFiniteIntermediateField ℓ) ≫
    padicSubfieldCondensedRingToPadicAlgCl ℓ ⟨⊥, inferInstance⟩

/-- The inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` of ring objects of condensed abelian groups: the abelian sheaf
morphism underlying `Profinite.padicIntCondensedRingToPadicAlgCl`. -/
noncomputable def padicIntRingObjToPadicAlgCl :
    continuousMapRingObj.{u} ℤ_[ℓ] ⟶ padicAlgClRingObj ℓ :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicIntCondensedRingToPadicAlgCl ℓ)

instance : IsMonHom (padicIntRingObjToPadicAlgCl.{u} ℓ) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicIntCondensedRingToPadicAlgCl ℓ)))

/-! ### The inclusions `ℤ̲_ℓ ⟶ 𝒪̲_E` and `ℤ̲_ℓ ⟶ E̲` -/

/-- The inclusion `ℤ̲_ℓ ⟶ 𝒪̲_E` of ring objects of condensed abelian groups, for a finite
subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`: the abelian sheaf morphism underlying
`Profinite.padicIntCondensedRingToPadicIntegersCondensedRing`. -/
noncomputable def padicIntRingObjToPadicIntegers (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] :
    continuousMapRingObj.{u} ℤ_[ℓ] ⟶ padicIntegersRingObj ℓ E :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicIntCondensedRingToPadicIntegersCondensedRing ℓ E)

instance (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] :
    IsMonHom (padicIntRingObjToPadicIntegers.{u} ℓ E) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (padicIntCondensedRingToPadicIntegersCondensedRing ℓ E)))

/-- The inclusion `ℤ_ℓ ⊆ E` into a finite normed extension `E` of `ℚ_ℓ`. -/
noncomputable def padicIntToNormedExtension (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] :
    ℤ_[ℓ] →+* E :=
  (algebraMap ℚ_[ℓ] E).comp PadicInt.Coe.ringHom

lemma continuous_padicIntToNormedExtension (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] :
    Continuous (padicIntToNormedExtension ℓ E) :=
  (continuous_algebraMap ℚ_[ℓ] E).comp continuous_subtype_val

/-- The inclusion `ℤ̲_ℓ ⟶ E̲` of ring objects of condensed abelian groups, for a normed extension
`E` of `ℚ_ℓ`: postcomposition with the inclusion `ℤ_ℓ ⊆ E`. -/
noncomputable def padicIntRingObjToNormedExtension (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] :
    continuousMapRingObj.{u} ℤ_[ℓ] ⟶ continuousMapRingObj E :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap (padicIntToNormedExtension ℓ E)
      (continuous_padicIntToNormedExtension ℓ E))

instance (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] :
    IsMonHom (padicIntRingObjToNormedExtension.{u} ℓ E) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (continuousMapRingSheafMap (padicIntToNormedExtension ℓ E)
        (continuous_padicIntToNormedExtension ℓ E))))

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The Tate module `ℤ_ℓ(1)` -/

/-- The `ℤ_ℓ,X`-module `ℤ/ℓ^n(1) = ℤ_ℓ,X ⊗ μ_{ℓ^n}`: the free `ℤ_ℓ,X`-module on the sheaf of
`ℓ^n`-th roots of unity, where `ℤ_ℓ,X = p_X^* ℤ̲_ℓ`. As an abelian sheaf it is `μ_{ℓ^n}`, since
`μ_{ℓ^n}` is killed by `ℓ^n`. -/
noncomputable def tateModuleLevel (n : ℕ) :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) :=
  (Mod.freeFunctor _).obj (rootsOfUnitySheaf X (ℓ ^ n))

/-- The transition map `ℤ/ℓ^{n+1}(1) ⟶ ℤ/ℓ^n(1)` of the Tate module, induced by the `ℓ`-th
power map `μ_{ℓ^{n+1}} ⟶ μ_{ℓ^n}`. -/
noncomputable def tateModuleTransition (n : ℕ) :
    tateModuleLevel X ℓ (n + 1) ⟶ tateModuleLevel X ℓ n :=
  (Mod.freeFunctor _).map (eqToHom (by rw [pow_succ']) ≫ rootsOfUnitySheafPow X (ℓ ^ n) ℓ)

/-- The inverse system `n ↦ ℤ/ℓ^n(1)` of `ℤ_ℓ,X`-modules. -/
noncomputable def tateModuleSystem :
    ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) :=
  Functor.ofOpSequence (tateModuleTransition X ℓ)

/-- The Tate module `ℤ_ℓ(1) = lim_n μ_{ℓ^n}` on `X_proét`, as a module object over `ℤ_ℓ,X`: the
limit of the inverse system `n ↦ ℤ/ℓ^n(1)`. -/
noncomputable def tateModule :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) :=
  limit (tateModuleSystem X ℓ)

/-! ### The Tate twists `Λ(d)` -/

section Twist

variable {ℓ} {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  (φ : Profinite.continuousMapRingObj.{u} ℤ_[ℓ] ⟶ Λ) [IsMonHom φ]

/-- The Tate twist `Λ_X(1) = Λ_X ⊗_{ℤ_ℓ,X} ℤ_ℓ(1)` of a condensed coefficient ring `Λ` under
`ℤ̲_ℓ`, through `φ : ℤ̲_ℓ ⟶ Λ`: the extension of scalars of the Tate module along the coefficient
change `φ_X : ℤ_ℓ,X ⟶ Λ_X`. For `Λ = ℚ̲̄_ℓ` and `φ = Profinite.padicIntRingObjToPadicAlgCl ℓ` this
is `ℚ̄_ℓ,X(1) = ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} ℤ_ℓ(1)`. -/
noncomputable def tateTwistOne :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  (Mod.extendScalars (coefficientMap φ X)).obj (tateModule X ℓ)

/-- The non-negative Tate twists `Λ_X(d) = Λ_X(1)^{⊗ d}`, the tensor powers over `Λ_X`, with
`Λ_X(0) = Λ_X`. -/
noncomputable def tateTwistNat :
    ℕ → Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  | 0 => 𝟙_ _
  | d + 1 => tateTwistNat d ⊗ tateTwistOne X φ

/-- The Tate twist `Λ_X(d)` for `d ∈ ℤ`: the tensor power `Λ_X(1)^{⊗ d}` for `d ≥ 0`, and the
dual `Hom_{Λ_X}(Λ_X(-d), Λ_X)` for `d < 0`. -/
noncomputable def tateTwist :
    ℤ → Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  | (d : ℕ) => tateTwistNat X φ d
  | .negSucc d => (ihom (tateTwistNat X φ (d + 1))).obj (𝟙_ _)

lemma tateTwist_natCast (d : ℕ) : tateTwist X φ d = tateTwistNat X φ d := rfl

/-- The Tate twist `Λ_X(d)`, placed in degree `0` of the derived category `D(Mod_{Λ_X})`. -/
noncomputable def tateTwistDerived (d : ℤ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  (DerivedCategory.singleFunctor _ 0).obj (tateTwist X φ d)

/-- The Tate twist functor `K ↦ K(d) = K ⊗ᴸ_{Λ_X} Λ_X(d)` on `D(Mod_{Λ_X})`. -/
noncomputable def tateTwistFunctor (d : ℤ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  tensorRight (tateTwistDerived X φ d)

/-- The Tate twist `Λ_X(0)`, placed in degree `0`, is the unit of `D(Mod_{Λ_X})`. -/
noncomputable def tateTwistDerivedZeroIso :
    tateTwistDerived X φ 0 ≅ 𝟙_ _ :=
  DerivedCategory.singleFunctorObjUnitIso _

end Twist

end AlgebraicGeometry.ProEtale
