/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory
public import WeilConjectures.Compactification.Over
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek

/-!

# The six functors on bounded constructible module objects over `Λ`

Let `Λ` be a commutative condensed ring. For a scheme `X`, the bounded constructible derived
category `D_cons(X_proét, Λ_X)` of module objects over the coefficient ring object
`Λ_X = p_X^* Λ` is the full subcategory
`ProEtale.BoundedConstructible (condensedRingObj Λ X)` of `D(Mod_{Λ_X})`
(`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`), with scoped notation
`Dᵇc(X)⟦Λ⟧`. This file restricts the six functors on `D(Mod_{Λ_X})` of the folder
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived` to these full subcategories.

## The setting

Following Bhatt–Scholze, Section 6.8, in the simplified setting of schemes over a field: fix a
prime `ℓ` and a field `k` of characteristic `p > 0` with `p ≠ ℓ`
(`[Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`). All schemes are separated and of finite
type over `Spec k`: they are objects `X : Over (Spec (.of k))` of the category of schemes over
`Spec k`, with structure morphism `X.hom` locally of finite type, quasi-compact and separated.
All morphisms are morphisms `f : X ⟶ Y` of `Over (Spec (.of k))`, and the functors are those of
the underlying morphism of schemes `f.left`. In the documentation, `X` also stands for the
underlying scheme `X.left`, so that for instance `Dᵇc(X)⟦Λ⟧` is `Dᵇc(X.left)⟦Λ⟧` in the code.
No further hypothesis is imposed on the schemes or morphisms. In particular every such morphism
has a compactification, by Nagata's theorem (`AlgebraicGeometry.HasCompactification.of_over`),
with the choice `compactificationOverField f`. A compactification
`c = (X.left ⟶[i] Z ⟶[p] Y.left)` of `f.left` is a factorization in `Over (Spec (.of k))`,
through the object `c.overObj` and the morphisms `c.overI` and `c.overG` of
`WeilConjectures.Compactification.Over`.

| functor | restriction |
| --- | --- |
| `Lf^* = L((f)^*⟦Λ⟧)` | `boundedConstructibleUpperStar` |
| `Rf_* = R((f)_*⟦Λ⟧)` | `boundedConstructibleLowerStar` |
| `j_! = D((j)_!open⟦Λ⟧)`, `j` an open immersion | `boundedConstructibleOpenImmersionLowerShriek` |
| `- ⊗ᴸ -` | `boundedConstructibleTensor` |
| `RHom(-, -)` | `boundedConstructibleHom` |

The pullback, the pushforward and the extension by zero are the `ObjectProperty.lift` of the
composite of the inclusion with the functor on the ambient derived category, so they are
compatible with the inclusions by construction (`ObjectProperty.liftCompιIso`). The derived
tensor product and the derived hom are instead the monoidal closed structure of the full
subcategory `Dᵇc(X)⟦Λ⟧` (`ObjectProperty.fullMonoidalSubcategory`,
`ObjectProperty.fullMonoidalClosedSubcategory`), given by the instances
`isMonoidal_boundedConstructible` and `isMonoidalClosed_boundedConstructible`; they are again
compatible with the inclusions, the inclusion being strict monoidal (`ObjectProperty.monoidalι`).
The restricted pullback `Lf^*` is strong monoidal, with the comparison isomorphisms of the
strong monoidal derived pullback `ProEtale.CondensedRing.monoidal_leftDerivedUpperStar`
(`monoidal_boundedConstructibleUpperStar`, by `ObjectProperty.monoidalLift`).

The derived lower shriek is not a restriction: it is assembled on bounded constructible
complexes out of the functors above. For a compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`,
`Rf_!^c := i_! ⋙ Rp_*` (`boundedConstructibleLowerShriekOfCompactification`), and `Rf_!` is
`Rf_!^c` for the chosen compactification `compactificationOverField f`
(`boundedConstructibleLowerShriek`). Both are compatible with the derived lower shrieks
`Rf_!(c)⟦Λ⟧` and `R(f)_!⟦Λ⟧` on the ambient derived categories
(`boundedConstructibleLowerShriekOfCompactificationCompatibility`,
`boundedConstructibleLowerShriekCompatibility`).

The adjunctions `Lf^* ⊣ Rf_*` and `j_! ⊣ j^*` restrict along the fully faithful inclusions
(`Adjunction.restrictFullyFaithful`), and so does the composition isomorphism
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` (`boundedConstructibleUpperStarComp`). Its conjugates under these
adjunctions are the composition isomorphisms `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`
(`boundedConstructibleLowerStarComp`) and `(j ≫ j')_! ≅ j_! ⋙ j'_!` for open immersions
(`boundedConstructibleOpenImmersionLowerShriekComp`). The adjunction
`- ⊗ᴸ - ⊣₂ RHom(-, -)` is the tensor-hom adjunction of the monoidal closed category
`Dᵇc(X)⟦Λ⟧` (`boundedConstructibleTensorHomAdjunction₂`).

The exceptional inverse image `Rf^!` is not the restriction of a functor on the ambient derived
category: it is constructed on bounded constructible complexes directly, for the `ℓ`-adic
coefficient rings `E̲` and `ℚ̲̄_ℓ`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek`.

## The finiteness theorems

That `Lf^*` and `j_!` preserve bounded constructible complexes holds for every `Λ`; it is
`sorry`ed (`boundedConstructible_leftDerivedUpperStar_obj`,
`boundedConstructible_openImmersionLowerShriek_obj`).

That `Rf_*` preserves bounded constructible complexes, and that `Dᵇc(X)⟦Λ⟧` contains `Λ_X` and
is stable under `- ⊗ᴸ -` and `RHom(-, -)`, are the finiteness theorems. They are false for a
general condensed ring `Λ` (Artin–Schreier for `Λ = 𝔽_p` in characteristic `p`, unbounded
`Tor` and `Ext` for `Λ = ℤ/ℓ²`). They are stated (`sorry`ed, with citations to
SGA 4½ [Th. finitude], SGA 4 XVII and Bhatt–Scholze, Section 6.8) separately for each
coefficient ring, for morphisms of separated `k`-schemes of finite type:
* `Rf_*` preserves bounded constructible complexes (`RightDerivedLowerStarFiniteness Λ k`) for a
  finite discrete ring `Λ = T̲` whose exponent is invertible in `k`
  (`rightDerivedLowerStarFiniteness_of_finite`), and for the `ℓ`-adic rings `E̲`, `𝒪̲_E` and
  `ℚ̲̄_ℓ` with `ℓ` invertible in `k` (`rightDerivedLowerStarFiniteness_continuousMapRingObj`,
  `…_padicIntegersRingObj`, `…_padicAlgClRingObj`);
* `Dᵇc(X)⟦Λ⟧` is monoidal and monoidal closed (`ObjectProperty.IsMonoidal`,
  `ObjectProperty.IsMonoidalClosed`) for the `ℓ`-adic rings `E̲`, `𝒪̲_E` and `ℚ̲̄_ℓ` with `ℓ`
  invertible in `k`.

The constructions involving `Rf_*` (`Rf_*`, `Rf_!` and those built on them in the following
files) are shared between the coefficient rings: each takes the finiteness theorem `hΛ` for `Λ`
as an explicit argument, whose default value `right_derived_lower_star_finiteness` is the
theorem above for the coefficient ring at hand. So for these coefficient rings they need no
hypothesis. The derived tensor product and the derived hom are those of `ℚ̲̄_ℓ`, the coefficient
ring used downstream.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The finiteness theorems

The derived pushforward `Rf_*` along a morphism of separated `k`-schemes of finite type preserves
bounded constructible complexes, and the bounded constructible complexes are stable under
`- ⊗ᴸ -` and `RHom(-, -)`, only for suitable coefficient rings (Deligne's finiteness theorems,
SGA 4½, [Th. finitude]; Bhatt–Scholze, Section 6.8). They are stated here separately for each
coefficient ring. They fail for a general condensed ring `Λ`:
* for `Λ = 𝔽_p` with `p` the characteristic of `k`, `k` separably closed and
  `f : 𝔸¹_k ⟶ Spec k`, the Artin–Schreier sequence gives `R¹f_* 𝔽_p = k[t] / (F - 1) k[t]`, an
  infinite dimensional `𝔽_p`-vector space, so `Rf_* 𝔽_p` is not constructible;
* for `Λ = ℤ/ℓ²`, the constructible sheaf `ℤ/ℓ` has `ℤ/ℓ ⊗ᴸ ℤ/ℓ` and `RHom(ℤ/ℓ, ℤ/ℓ)` with
  nonzero cohomology in infinitely many degrees, so these are not bounded.
-/

section Finiteness

/-- The *finiteness theorem for the derived pushforward* with coefficients in `Λ` over the field
`k`: for every morphism `f : X ⟶ Y` of separated `k`-schemes of finite type, `Rf_*` sends bounded
constructible complexes of `Λ`-modules to bounded constructible complexes. It holds for the
coefficient rings of the theorems below, and is false for a general `Λ` (see above). It is the
input of the constructions on bounded constructible complexes below that involve `Rf_*`; for
these coefficient rings, it is supplied automatically by the tactic
`right_derived_lower_star_finiteness`. -/
def RightDerivedLowerStarFiniteness (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] : Prop :=
  ∀ {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))),
    boundedConstructible (condensedRingObj Λ X.left) K →
      boundedConstructible (condensedRingObj Λ Y.left) ((R((f.left)_*⟦Λ⟧)).obj K)

/-- **Finiteness of `Rf_*` for finite coefficients** [SGA 4½, Th. finitude, 1.1; SGA 4, XVII]: for
a finite discrete ring `T` whose exponent is invertible in `k`, `Rf_*` along a morphism of
separated `k`-schemes of finite type preserves bounded constructible complexes of `T̲`-modules. -/
theorem rightDerivedLowerStarFiniteness_of_finite (T : Type) [TopologicalSpace T] [CommRing T]
    [IsTopologicalRing T] [DiscreteTopology T] [Finite T] (k : Type u) [Field k]
    [Invertible (AddMonoid.exponent T : k)] :
    RightDerivedLowerStarFiniteness (Profinite.continuousMapRingObj T) k :=
  sorry

/-- **Finiteness of `Rf_*` for `E`-coefficients** [SGA 4½, Th. finitude, 1.1; Bhatt–Scholze,
Section 6.8]: for a finite extension `E` of `ℚ_ℓ` with `ℓ` invertible in `k`, `Rf_*` along a
morphism of separated `k`-schemes of finite type preserves bounded constructible complexes of
`E̲`-modules. -/
theorem rightDerivedLowerStarFiniteness_continuousMapRingObj {ℓ : ℕ} [Fact ℓ.Prime] (E : Type)
    [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (k : Type u) [Field k]
    [Fact (ringChar k ≠ ℓ)] :
    RightDerivedLowerStarFiniteness (Profinite.continuousMapRingObj E) k :=
  sorry

/-- **Finiteness of `Rf_*` for `𝒪_E`-coefficients** [SGA 4½, Th. finitude, 1.1; Bhatt–Scholze,
Section 6.8]: for a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` with `ℓ` invertible in `k`, `Rf_*` along
a morphism of separated `k`-schemes of finite type preserves bounded constructible complexes of
`𝒪̲_E`-modules. -/
theorem rightDerivedLowerStarFiniteness_padicIntegersRingObj (ℓ : ℕ) [Fact ℓ.Prime] (E : Type)
    [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)] :
    RightDerivedLowerStarFiniteness (Profinite.padicIntegersRingObj ℓ E) k :=
  sorry

/-- **Finiteness of `Rf_*` for `ℚ̄_ℓ`-coefficients** [SGA 4½, Th. finitude, 1.1; Bhatt–Scholze,
Section 6.8]: for `ℓ` invertible in `k`, `Rf_*` along a morphism of separated `k`-schemes of
finite type preserves bounded constructible complexes of `ℚ̲̄_ℓ`-modules. -/
theorem rightDerivedLowerStarFiniteness_padicAlgClRingObj (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u)
    [Field k] [Fact (ringChar k ≠ ℓ)] :
    RightDerivedLowerStarFiniteness (Profinite.padicAlgClRingObj ℓ) k :=
  sorry

instance fact_rightDerivedLowerStarFiniteness_of_finite (T : Type) [TopologicalSpace T]
    [CommRing T] [IsTopologicalRing T] [DiscreteTopology T] [Finite T] (k : Type u) [Field k]
    [Invertible (AddMonoid.exponent T : k)] :
    Fact (RightDerivedLowerStarFiniteness (Profinite.continuousMapRingObj T) k) :=
  ⟨rightDerivedLowerStarFiniteness_of_finite T k⟩

-- The prime `ℓ` occurs only in the instances `NormedAlgebra ℚ_[ℓ] E` and `Fact (ringChar k ≠ ℓ)`;
-- it is found from the local instances.
set_option synthInstance.checkSynthOrder false in
instance fact_rightDerivedLowerStarFiniteness_continuousMapRingObj {ℓ : ℕ} [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (k : Type u)
    [Field k] [Fact (ringChar k ≠ ℓ)] :
    Fact (RightDerivedLowerStarFiniteness (Profinite.continuousMapRingObj E) k) :=
  ⟨rightDerivedLowerStarFiniteness_continuousMapRingObj (ℓ := ℓ) E k⟩

instance fact_rightDerivedLowerStarFiniteness_padicIntegersRingObj (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (k : Type u) [Field k]
    [Fact (ringChar k ≠ ℓ)] :
    Fact (RightDerivedLowerStarFiniteness (Profinite.padicIntegersRingObj ℓ E) k) :=
  ⟨rightDerivedLowerStarFiniteness_padicIntegersRingObj ℓ E k⟩

instance fact_rightDerivedLowerStarFiniteness_padicAlgClRingObj (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k ≠ ℓ)] :
    Fact (RightDerivedLowerStarFiniteness (Profinite.padicAlgClRingObj ℓ) k) :=
  ⟨rightDerivedLowerStarFiniteness_padicAlgClRingObj ℓ k⟩

/-- `RightDerivedLowerStarFiniteness Λ k` from the `Fact` instance for the coefficient ring `Λ`. -/
theorem RightDerivedLowerStarFiniteness.of_fact
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {k : Type u} [Field k]
    [h : Fact (RightDerivedLowerStarFiniteness Λ k)] : RightDerivedLowerStarFiniteness Λ k :=
  h.out

/-- Prove `RightDerivedLowerStarFiniteness Λ k`: from a hypothesis, or by the finiteness theorem
for the coefficient ring `Λ` (`ℚ̲̄_ℓ`, `𝒪̲_E`, `E̲`, or a finite ring), through the `Fact`
instances above. It is the default value of the finiteness argument of the constructions
below. -/
macro "right_derived_lower_star_finiteness" : tactic =>
  `(tactic| first | done | assumption | exact RightDerivedLowerStarFiniteness.of_fact)

variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

variable (X)

set_option synthInstance.checkSynthOrder false in
/-- [SGA 4½, Th. finitude, 1.6, 2.2; Bhatt–Scholze, Section 6.8]
For a finite extension `E` of `ℚ_ℓ` with `ℓ` invertible in `k`, the bounded constructible
complexes of `E̲`-modules on a separated `k`-scheme of finite type contain the unit and are stable
under `- ⊗ᴸ -`. -/
instance isMonoidal_boundedConstructible_continuousMapRingObj {ℓ : ℕ} [Fact ℓ.Prime] (E : Type)
    [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left)).IsMonoidal :=
  sorry

/-- [SGA 4½, Th. finitude, 1.6, 2.2; Bhatt–Scholze, Section 6.8]
For a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` with `ℓ` invertible in `k`, the bounded
constructible complexes of `𝒪̲_E`-modules on a separated `k`-scheme of finite type contain the
unit and are stable under `- ⊗ᴸ -`. -/
instance isMonoidal_boundedConstructible_padicIntegersRingObj (ℓ : ℕ) [Fact ℓ.Prime] (E : Type)
    [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)).IsMonoidal :=
  sorry

/-- [SGA 4½, Th. finitude, 1.6, 2.2; Bhatt–Scholze, Section 6.8]
For `ℓ` invertible in `k`, the bounded constructible complexes of `ℚ̲̄_ℓ`-modules on a
separated `k`-scheme of finite type contain the unit and are stable under `- ⊗ᴸ -`. -/
instance isMonoidal_boundedConstructible_padicAlgClRingObj (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).IsMonoidal :=
  sorry

set_option synthInstance.checkSynthOrder false in
/-- [SGA 4½, Th. finitude, 1.6, 2.2; Bhatt–Scholze, Section 6.8]
For a finite extension `E` of `ℚ_ℓ` with `ℓ` invertible in `k`, the bounded constructible
complexes of `E̲`-modules on a separated `k`-scheme of finite type are stable under
`RHom(-, -)`. -/
instance isMonoidalClosed_boundedConstructible_continuousMapRingObj {ℓ : ℕ} [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left)).IsMonoidalClosed :=
  sorry

/-- [SGA 4½, Th. finitude, 1.6, 2.2; Bhatt–Scholze, Section 6.8]
For a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` with `ℓ` invertible in `k`, the bounded
constructible complexes of `𝒪̲_E`-modules on a separated `k`-scheme of finite type are stable
under `RHom(-, -)`. -/
instance isMonoidalClosed_boundedConstructible_padicIntegersRingObj (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)).IsMonoidalClosed :=
  sorry

/-- [SGA 4½, Th. finitude, 1.6, 2.2; Bhatt–Scholze, Section 6.8]
For `ℓ` invertible in `k`, the bounded constructible complexes of `ℚ̲̄_ℓ`-modules on a
separated `k`-scheme of finite type are stable under `RHom(-, -)`. -/
instance isMonoidalClosed_boundedConstructible_padicAlgClRingObj (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).IsMonoidalClosed :=
  sorry

end Finiteness

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- The bounded constructible derived category `D_cons(X_proét, Λ_X)` of module objects over
`Λ_X = p_X^* Λ`. -/
scoped notation "Dᵇc(" X ")⟦" Λ "⟧" =>
  AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj Λ X)

/-! ### The pullback and the pushforward -/

section UpperLowerStar

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The derived pullback `Lf^*` on module objects over `Λ` preserves bounded constructible
complexes. -/
lemma boundedConstructible_leftDerivedUpperStar_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left)))
    (hK : boundedConstructible (condensedRingObj Λ Y.left) K) :
    boundedConstructible (condensedRingObj Λ X.left) ((L((f.left)^*⟦Λ⟧)).obj K) :=
  sorry

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible complexes: the
restriction of `L((f)^*⟦Λ⟧)`. -/
noncomputable def boundedConstructibleUpperStar : Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((f.left)^*⟦Λ⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f K.obj K.property

/-- The restricted derived pullback is compatible with the inclusions. -/
noncomputable def boundedConstructibleUpperStarCompatibility :
    boundedConstructibleUpperStar Λ ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ L((f.left)^*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` on bounded constructible complexes:
the restriction of `ProEtale.CondensedRing.leftDerivedUpperStarComp` along the fully
faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (g : Y ⟶ Z) :
    boundedConstructibleUpperStar Λ ℓ (f ≫ g) ≅
      boundedConstructibleUpperStar Λ ℓ g ⋙ boundedConstructibleUpperStar Λ ℓ f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (boundedConstructibleUpperStarCompatibility Λ ℓ (f ≫ g) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp Λ f.left g.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility Λ ℓ g).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm ≪≫
      (Functor.associator _ _ _).symm)

-- The prime `ℓ` of the setting is a parameter of all the functors of this file, although the
-- statement does not depend on it.
set_option linter.unusedSectionVars false in
/-- The derived pushforward `Rf_*` on module objects over `Λ` preserves bounded constructible
complexes, given the finiteness theorem `hΛ` for `Λ`. -/
lemma boundedConstructible_rightDerivedLowerStar_obj (hΛ : RightDerivedLowerStarFiniteness Λ k)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hK : boundedConstructible (condensedRingObj Λ X.left) K) :
    boundedConstructible (condensedRingObj Λ Y.left) ((R((f.left)_*⟦Λ⟧)).obj K) :=
  hΛ f K hK

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible complexes:
the restriction of `R((f)_*⟦Λ⟧)`, for coefficients satisfying the finiteness theorem `hΛ`. -/
noncomputable def boundedConstructibleLowerStar
    (hΛ : RightDerivedLowerStarFiniteness Λ k := by right_derived_lower_star_finiteness) :
    Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(Y.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Λ⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj Λ ℓ f hΛ K.obj K.property

/-- The restricted derived pushforward is compatible with the inclusions. -/
noncomputable def boundedConstructibleLowerStarCompatibility
    (hΛ : RightDerivedLowerStarFiniteness Λ k := by right_derived_lower_star_finiteness) :
    boundedConstructibleLowerStar Λ ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f.left)_*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes: the restriction of
`ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction
    (hΛ : RightDerivedLowerStarFiniteness Λ k := by right_derived_lower_star_finiteness) :
    boundedConstructibleUpperStar Λ ℓ f ⊣ boundedConstructibleLowerStar Λ ℓ f :=
  Adjunction.restrictFullyFaithful (derivedUpperStarLowerStarAdjunction Λ f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
    (boundedConstructibleLowerStarCompatibility Λ ℓ f).symm

/-- The derived pullback `Lf^*` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleLowerStar`. -/
lemma isLeftAdjoint_boundedConstructibleUpperStar
    (hΛ : RightDerivedLowerStarFiniteness Λ k := by right_derived_lower_star_finiteness) :
    (boundedConstructibleUpperStar Λ ℓ f).IsLeftAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).isLeftAdjoint

/-- The derived pushforward `Rf_*` on bounded constructible complexes is a right adjoint, its
left adjoint being `boundedConstructibleUpperStar`. -/
instance isRightAdjoint_boundedConstructibleLowerStar
    (hΛ : RightDerivedLowerStarFiniteness Λ k := by right_derived_lower_star_finiteness) :
    (boundedConstructibleLowerStar Λ ℓ f hΛ).IsRightAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).isRightAdjoint

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` on bounded constructible complexes:
the conjugate of `boundedConstructibleUpperStarComp` under the adjunctions
`L(f ≫ g)^* ⊣ R(f ≫ g)_*` and `Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*`. -/
noncomputable def boundedConstructibleLowerStarComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (g : Y ⟶ Z)
    (hΛ : RightDerivedLowerStarFiniteness Λ k := by right_derived_lower_star_finiteness) :
    boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleLowerStar Λ ℓ g ≅
      boundedConstructibleLowerStar Λ ℓ (f ≫ g) :=
  (conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ (f ≫ g))
    ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ g).comp
      (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f))
    (boundedConstructibleUpperStarComp Λ ℓ f g).symm).symm

end UpperLowerStar

/-! ### The extension by zero along an open immersion -/

section OpenImmersion

include ℓ k

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The extension by zero `j_!` along an open immersion, applied levelwise to complexes of
module objects over `Λ`, preserves bounded constructible complexes. -/
lemma boundedConstructible_openImmersionLowerShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
      (condensedRingObj Λ U.left)))
    (hK : boundedConstructible (condensedRingObj Λ U.left) K) :
    boundedConstructible (condensedRingObj Λ X.left) ((D((j.left)_!open⟦Λ⟧)).obj K) :=
  sorry

/-- The extension by zero `j_! : Dᵇc(U)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` along an open immersion on bounded
constructible complexes: the restriction of the levelwise functor `D((j)_!open⟦Λ⟧)`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriek : Dᵇc(U.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ D((j.left)_!open⟦Λ⟧))
    fun K ↦ boundedConstructible_openImmersionLowerShriek_obj Λ ℓ j K.obj K.property

/-- The restricted extension by zero is compatible with the inclusions. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekCompatibility :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ D((j.left)_!open⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `j_! ⊣ j^*` along an open immersion on bounded constructible complexes: the
restriction of `ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction`
along the fully faithful inclusions, the levelwise `D((j)^*⟦Λ⟧)` being identified with the
derived pullback `L((j)^*⟦Λ⟧)` that `boundedConstructibleUpperStar` restricts. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⊣ boundedConstructibleUpperStar Λ ℓ j :=
  Adjunction.restrictFullyFaithful
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j.left).symm)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).symm
    (boundedConstructibleUpperStarCompatibility Λ ℓ j).symm

/-- The extension by zero `j_!` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleUpperStar`. -/
instance isLeftAdjoint_boundedConstructibleOpenImmersionLowerShriek :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).IsLeftAdjoint :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).isLeftAdjoint

/-- The derived pullback `j^*` along an open immersion on bounded constructible complexes is a
right adjoint, its left adjoint being `boundedConstructibleOpenImmersionLowerShriek`. -/
instance isRightAdjoint_boundedConstructibleUpperStar_of_isOpenImmersion :
    (boundedConstructibleUpperStar Λ ℓ j).IsRightAdjoint :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).isRightAdjoint

/-- The composition isomorphism `(j ≫ j')_! ≅ j_! ⋙ j'_!` of the extensions by zero along open
immersions on bounded constructible complexes: the conjugate of
`boundedConstructibleUpperStarComp` under the adjunctions `(j ≫ j')_! ⊣ L(j ≫ j')^*` and
`j_! ⋙ j'_! ⊣ Lj'^* ⋙ Lj^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekComp {V : Over (Spec (.of k))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom] (j' : X ⟶ V)
    [IsOpenImmersion j'.left] [IsOpenImmersion (j ≫ j').left] :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ (j ≫ j') ≅
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' :=
  ((conjugateIsoEquiv (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ (j ≫ j'))
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).comp
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j'))).symm
    (boundedConstructibleUpperStarComp Λ ℓ j j')).symm

end OpenImmersion

/-! ### The derived lower shriek -/

/-- The compactification of the underlying morphism of schemes `f.left` of a morphism `f` of
separated `k`-schemes of finite type chosen by Nagata's theorem
(`AlgebraicGeometry.HasCompactification.of_over`): the compactification
`HasCompactification.compactification f.left` for the instance it provides. It is the
compactification defining `boundedConstructibleLowerShriek`. -/
noncomputable abbrev compactificationOverField {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y) : Compactification f.left :=
  haveI := HasCompactification.of_over f
  HasCompactification.compactification f.left

section Shriek

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded
constructible complexes attached to a compactification `c = (X.left ⟶[i] Z ⟶[p] Y.left)` of
`f.left`: the extension by zero along the open immersion `i` followed by the derived pushforward
along the proper morphism `p`, both on bounded constructible complexes, for `i` and `p` the
morphisms `c.overI` and `c.overG` of `Over (Spec (.of k))`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification
    (hΛ : RightDerivedLowerStarFiniteness Λ k := by right_derived_lower_star_finiteness) :
    Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(Y.left)⟦Λ⟧ :=
  boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.overI ⋙
    boundedConstructibleLowerStar Λ ℓ c.overG

/-- `Rf_!^c` on bounded constructible complexes is the restriction of the derived lower shriek
`Rf_!(c)⟦Λ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationCompatibility
    (hΛ : RightDerivedLowerStarFiniteness Λ k := by right_derived_lower_star_finiteness) :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ c ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ Rf_!(c)⟦Λ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarCompatibility Λ ℓ c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ c.overI) _ ≪≫
    Functor.associator _ _ _

end OfCompactification

variable (f : X ⟶ Y)

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible complexes:
the functor `boundedConstructibleLowerShriekOfCompactification` attached to the compactification
`compactificationOverField f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek
    (hΛ : RightDerivedLowerStarFiniteness Λ k := by right_derived_lower_star_finiteness) :
    Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(Y.left)⟦Λ⟧ :=
  boundedConstructibleLowerShriekOfCompactification Λ ℓ (compactificationOverField f)

lemma boundedConstructibleLowerShriek_eq
    (hΛ : RightDerivedLowerStarFiniteness Λ k := by right_derived_lower_star_finiteness) :
    boundedConstructibleLowerShriek Λ ℓ f =
      boundedConstructibleLowerShriekOfCompactification Λ ℓ (compactificationOverField f) :=
  rfl

/-- The derived lower shriek on bounded constructible complexes is the restriction of the
derived lower shriek `R(f)_!⟦Λ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekCompatibility
    (hΛ : RightDerivedLowerStarFiniteness Λ k := by right_derived_lower_star_finiteness) :
    haveI := HasCompactification.of_over f
    boundedConstructibleLowerShriek Λ ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f.left)_!⟦Λ⟧ :=
  boundedConstructibleLowerShriekOfCompactificationCompatibility Λ ℓ
    (compactificationOverField f)

end Shriek


/-! ### The derived tensor product and the derived hom of `ℚ̄_ℓ`-sheaves

The bounded constructible complexes are stable under `- ⊗ᴸ -` and `RHom(-, -)` only for suitable
coefficient rings (see above). The tensor product and the internal hom on bounded constructible
complexes are those of the coefficient ring `ℚ̲̄_ℓ`, the one used downstream. -/

section TensorHom

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- The derived tensor product `- ⊗ᴸ - : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` on bounded
constructible `ℚ̄_ℓ`-sheaves: the tensor product of the monoidal structure on the full
subcategory `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` (`ObjectProperty.fullMonoidalSubcategory`), the restriction of
`-⊗ᴸ-(X)⟦ℚ̲̄_ℓ⟧` in both variables. -/
noncomputable def boundedConstructibleTensor :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  curriedTensor _

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ᵒᵖ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` on bounded
constructible `ℚ̄_ℓ`-sheaves: the internal hom of the monoidal closed structure on the full
subcategory `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` (`ObjectProperty.fullMonoidalClosedSubcategory`), the restriction of
`RHom(X)⟦ℚ̲̄_ℓ⟧` in both variables. -/
noncomputable def boundedConstructibleHom :
    (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)ᵒᵖ ⥤ Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  MonoidalClosed.internalHom

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, the restricted functor `K ⊗ᴸ -` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleTensorObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleTensor ℓ X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleTensor, derivedTensor]

/-- For a fixed `K ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleHom ℓ X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙
        (RHom(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧).obj (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- The adjunction with a parameter `- ⊗ᴸ - ⊣₂ RHom(-, -)` on bounded constructible
`ℚ̄_ℓ`-sheaves: the tensor-hom adjunction of the monoidal closed structure on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction₂ :
    boundedConstructibleTensor ℓ X ⊣₂ boundedConstructibleHom ℓ X :=
  MonoidalClosed.internalHomAdjunction₂

/-- For a fixed `K ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
`ℚ̄_ℓ`-sheaves: the tensor-hom adjunction `ihom.adjunction K` of the monoidal closed structure on
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleTensor ℓ X).obj K ⊣ (boundedConstructibleHom ℓ X).obj (op K) :=
  (boundedConstructibleTensorHomAdjunction₂ ℓ).adj K

end TensorHom

section MonoidalUpperStar

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` on bounded constructible
`ℚ̄_ℓ`-sheaves is strong monoidal, with the comparison isomorphisms of
`L((f)^*⟦ℚ̲̄_ℓ⟧)`. -/
noncomputable instance monoidal_boundedConstructibleUpperStar_padicAlgCl :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).Monoidal := by
  unfold boundedConstructibleUpperStar
  exact ObjectProperty.monoidalLift _ _

end MonoidalUpperStar

end AlgebraicGeometry.ProEtale.CondensedRing
