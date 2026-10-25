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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

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
| `Rf_* = R((f)_*⟦Λ⟧)` | `boundedConstructibleLowerStar` (`ℓ`-adic `Λ`) |
| `j_! = D((j)_!open⟦Λ⟧)`, `j` an open immersion | `boundedConstructibleOpenImmersionLowerShriek` |
| `- ⊗ᴸ -` | `boundedConstructibleTensor` (`ℓ`-adic `Λ`) |
| `RHom(-, -)` | `boundedConstructibleHom` (`ℓ`-adic `Λ`) |

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
coefficient rings, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek`.

## Sorried input

That the derived pushforward and extension by zero preserve bounded constructible complexes is
`sorry`ed (the pullback is `boundedConstructible_leftDerivedUpperStar_obj_of_scheme`):
`boundedConstructible_rightDerivedLowerStar_obj`
and `boundedConstructible_openImmersionLowerShriek_obj`, and the instances
`isMonoidal_boundedConstructible` (`Dᵇc(X)⟦Λ⟧` contains `Λ_X` and is stable under `- ⊗ᴸ -`) and
`isMonoidalClosed_boundedConstructible` (`Dᵇc(X)⟦Λ⟧` is stable under `RHom(-, -)`).

The pullback and the extension by zero preserve bounded constructible complexes for every `Λ`,
and are defined for a general condensed ring `Λ`. The other three statements are false for a
general `Λ`: for the constant discrete ring `𝔽_p` and the affine line over an algebraically
closed field of characteristic `p`, Artin–Schreier gives `H¹(𝔸¹, 𝔽_p) = k[t] / (F - 1) k[t]`,
which is infinite; for `Λ = ℤ/4` on a geometric point of characteristic `3`, `Tor_i` and
`Ext^i` of `ℤ/2` over `ℤ/4` are `ℤ/2` in every degree `i ≥ 0`. They are theorems for the
`ℓ`-adic coefficients with `ℓ` invertible in `k` (Deligne's finiteness theorems, SGA 4½
[Th. finitude]; Bhatt–Scholze, Section 6.8).

## The `ℓ`-adic coefficient rings

The pushforward, the lower shriek, the derived tensor product and the derived hom on bounded
constructible complexes, and the statements above, are made for each of the three `ℓ`-adic
coefficient rings separately, with the same declaration names:

* `ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ`, in the namespace `ProEtale.CondensedRing`
  (`boundedConstructibleLowerStar ℓ f`);
* `E̲ = Profinite.continuousMapRingObj E` for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
  (`E : PadicAlgCl.FiniteIntermediateField ℓ`, with category `Dᵇc(X)⟦E̲⟧`),
  in the namespace `ProEtale.CondensedRing.ContinuousMapRingObj`
  (`ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E f`);
* `𝒪̲_E = Profinite.padicIntegersRingObj ℓ E` for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, in
  the namespace `ProEtale.CondensedRing.PadicIntegersRingObj`
  (`PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E f`).

The pullback and the extension by zero are stated once, for a general `Λ`.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### The pullback and the pushforward -/

section UpperLowerStar

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

set_option linter.unusedSectionVars false in
/-- The derived pullback `Lf^*` on module objects over `Λ` preserves bounded constructible
complexes (SGA 4 XVII, 5.1.16; Bhatt–Scholze, Section 6.8). -/
lemma boundedConstructible_leftDerivedUpperStar_obj (K : Dᵇc(Y.left)⟦Λ⟧) :
    boundedConstructible (condensedRingObj Λ X.left) ((L((f.left)^*⟦Λ⟧)).obj K.obj) :=
  boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ f.left K.obj K.property

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible complexes:
the restriction of `L((f)^*⟦Λ⟧)`. -/
noncomputable def boundedConstructibleUpperStar : Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((f.left)^*⟦Λ⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f K

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

end UpperLowerStar

/-! ### The pushforward -/

section LowerStar

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- **Deligne's finiteness theorem** for `Rf_*`: for `ℓ` invertible in `k`, the
derived pushforward along a morphism of separated `k`-schemes of finite type carries bounded
constructible complexes of `ℚ̄_ℓ`-sheaves to bounded constructible complexes (SGA 4½ [Th. finitude]
for torsion coefficients; Bhatt–Scholze, Section 6.8, for `ℚ̲̄_ℓ`). It is false for a general
condensed ring: for the constant discrete ring `𝔽_p` and the affine line over an algebraically
closed field of characteristic `p`, Artin–Schreier gives `H¹(𝔸¹, 𝔽_p) = k[t] / (F - 1) k[t]`, which
is infinite. -/
lemma boundedConstructible_rightDerivedLowerStar_obj
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)
      ((R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K.obj) :=
  sorry

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` on bounded constructible
complexes: the restriction of `R((f)_*⟦ℚ̲̄_ℓ⟧)`. -/
noncomputable def boundedConstructibleLowerStar :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f K

/-- The restricted derived pushforward is compatible with the inclusions (`ℚ̄_ℓ`-coefficient). -/
noncomputable def boundedConstructibleLowerStarCompatibility :
    boundedConstructibleLowerStar ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes (`ℚ̄_ℓ`-coefficient):
the restriction of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` along the fully
faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⊣
      boundedConstructibleLowerStar ℓ f :=
  Adjunction.restrictFullyFaithful
    (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ f).symm
    (boundedConstructibleLowerStarCompatibility ℓ f).symm

/-- The derived pullback `Lf^*` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleLowerStar` (`ℚ̄_ℓ`-coefficient). -/
instance isLeftAdjoint_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).IsLeftAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).isLeftAdjoint

/-- The derived pushforward `Rf_*` on bounded constructible complexes is a right adjoint, its
left adjoint being `boundedConstructibleUpperStar` (`ℚ̄_ℓ`-coefficient). -/
instance isRightAdjoint_boundedConstructibleLowerStar :
    (boundedConstructibleLowerStar ℓ f).IsRightAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).isRightAdjoint

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` on bounded constructible complexes
(`ℚ̄_ℓ`-coefficient): the conjugate of `boundedConstructibleUpperStarComp` under the adjunctions
`L(f ≫ g)^* ⊣ R(f ≫ g)_*` and `Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*`. -/
noncomputable def boundedConstructibleLowerStarComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (g : Y ⟶ Z) :
    boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleLowerStar ℓ g ≅
      boundedConstructibleLowerStar ℓ (f ≫ g) :=
  (conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ (f ≫ g))
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).comp
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ f))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).symm).symm

end LowerStar

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj


section LowerStar

include ℓ k

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- **Deligne's finiteness theorem** for `Rf_*`: for `ℓ` invertible in `k`, the
derived pushforward along a morphism of separated `k`-schemes of finite type carries bounded
constructible complexes of `E`-sheaves to bounded constructible complexes (SGA 4½ [Th. finitude] for
torsion coefficients; Bhatt–Scholze, Section 6.8, for `E̲`). It is false for a general condensed
ring: for the constant discrete ring `𝔽_p` and the affine line over an algebraically closed field of
characteristic `p`, Artin–Schreier gives `H¹(𝔸¹, 𝔽_p) = k[t] / (F - 1) k[t]`, which is
infinite. -/
lemma boundedConstructible_rightDerivedLowerStar_obj
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Y.left)
      ((R((f.left)_*⟦Profinite.continuousMapRingObj E⟧)).obj K.obj) :=
  sorry

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` on bounded constructible
complexes: the restriction of `R((f)_*⟦E̲⟧)`. -/
noncomputable def boundedConstructibleLowerStar :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.continuousMapRingObj E⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ E f K

/-- The restricted derived pushforward is compatible with the inclusions (`E`-coefficient). -/
noncomputable def boundedConstructibleLowerStarCompatibility :
    boundedConstructibleLowerStar ℓ E f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.continuousMapRingObj E⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes (`E`-coefficient): the
restriction of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction :
    boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f ⊣
      boundedConstructibleLowerStar ℓ E f :=
  Adjunction.restrictFullyFaithful
    (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility (Profinite.continuousMapRingObj E) ℓ f).symm
    (boundedConstructibleLowerStarCompatibility ℓ E f).symm

/-- The derived pullback `Lf^*` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleLowerStar` (`E`-coefficient). -/
instance isLeftAdjoint_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f).IsLeftAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f).isLeftAdjoint

/-- The derived pushforward `Rf_*` on bounded constructible complexes is a right adjoint, its
left adjoint being `boundedConstructibleUpperStar` (`E`-coefficient). -/
instance isRightAdjoint_boundedConstructibleLowerStar :
    (boundedConstructibleLowerStar ℓ E f).IsRightAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f).isRightAdjoint

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` on bounded constructible complexes
(`E`-coefficient): the conjugate of `boundedConstructibleUpperStarComp` under the adjunctions
`L(f ≫ g)^* ⊣ R(f ≫ g)_*` and `Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*`. -/
noncomputable def boundedConstructibleLowerStarComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (g : Y ⟶ Z) :
    boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleLowerStar ℓ E g ≅
      boundedConstructibleLowerStar ℓ E (f ≫ g) :=
  (conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ E (f ≫ g))
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ E g).comp
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f))
    (boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E) ℓ f g).symm).symm

end LowerStar

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj


section LowerStar

include ℓ k

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- **Deligne's finiteness theorem** for `Rf_*`: for `ℓ` invertible in `k`, the
derived pushforward along a morphism of separated `k`-schemes of finite type carries bounded
constructible complexes of `𝒪_E`-sheaves to bounded constructible complexes (SGA 4½ [Th. finitude]
for torsion coefficients; Bhatt–Scholze, Section 6.8, for `𝒪̲_E`). It is false for a general
condensed ring: for the constant discrete ring `𝔽_p` and the affine line over an algebraically
closed field of characteristic `p`, Artin–Schreier gives `H¹(𝔸¹, 𝔽_p) = k[t] / (F - 1) k[t]`, which
is infinite. -/
lemma boundedConstructible_rightDerivedLowerStar_obj
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left)
      ((R((f.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K.obj) :=
  sorry

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` on bounded constructible
complexes: the restriction of `R((f)_*⟦𝒪̲_E⟧)`. -/
noncomputable def boundedConstructibleLowerStar :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ
      E⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ E f K

/-- The restricted derived pushforward is compatible with the inclusions (`𝒪_E`-coefficient). -/
noncomputable def boundedConstructibleLowerStarCompatibility :
    boundedConstructibleLowerStar ℓ E f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes (`𝒪_E`-coefficient): the
restriction of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction :
    boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f ⊣
      boundedConstructibleLowerStar ℓ E f :=
  Adjunction.restrictFullyFaithful
    (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility (Profinite.padicIntegersRingObj ℓ E) ℓ f).symm
    (boundedConstructibleLowerStarCompatibility ℓ E f).symm

/-- The derived pullback `Lf^*` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleLowerStar` (`𝒪_E`-coefficient). -/
instance isLeftAdjoint_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).IsLeftAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f).isLeftAdjoint

/-- The derived pushforward `Rf_*` on bounded constructible complexes is a right adjoint, its
left adjoint being `boundedConstructibleUpperStar` (`𝒪_E`-coefficient). -/
instance isRightAdjoint_boundedConstructibleLowerStar :
    (boundedConstructibleLowerStar ℓ E f).IsRightAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f).isRightAdjoint

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` on bounded constructible complexes
(`𝒪_E`-coefficient): the conjugate of `boundedConstructibleUpperStarComp` under the adjunctions
`L(f ≫ g)^* ⊣ R(f ≫ g)_*` and `Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*`. -/
noncomputable def boundedConstructibleLowerStarComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (g : Y ⟶ Z) :
    boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleLowerStar ℓ E g ≅
      boundedConstructibleLowerStar ℓ E (f ≫ g) :=
  (conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ E (f ≫ g))
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ E g).comp
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f))
    (boundedConstructibleUpperStarComp (Profinite.padicIntegersRingObj ℓ E) ℓ f g).symm).symm

end LowerStar

end PadicIntegersRingObj

/-! ### The extension by zero along an open immersion -/

section OpenImmersion

include ℓ k

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The extension by zero `j_!` along an open immersion, applied levelwise to complexes of
module objects over `Λ`, preserves bounded constructible complexes (SGA 4 XVII, 5.1.16;
Bhatt–Scholze, Section 6.8). -/
lemma boundedConstructible_openImmersionLowerShriek_obj (K : Dᵇc(U.left)⟦Λ⟧) :
    boundedConstructible (condensedRingObj Λ X.left) ((D((j.left)_!open⟦Λ⟧)).obj K.obj) :=
  sorry

/-- The extension by zero `j_! : Dᵇc(U)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` along an open immersion on bounded
constructible complexes: the restriction of the levelwise functor
`D((j)_!open⟦Λ⟧)`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriek : Dᵇc(U.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ D((j.left)_!open⟦Λ⟧))
    fun K ↦ boundedConstructible_openImmersionLowerShriek_obj Λ ℓ j K

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

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` on bounded
constructible complexes attached to a compactification `c = (X.left ⟶[i] Z ⟶[p] Y.left)` of
`f.left`: the extension by zero along the open immersion `i` followed by the
derived pushforward along the proper morphism `p`, both on bounded constructible complexes, for `i`
and `p` the morphisms `c.overI` and `c.overG` of `Over (Spec (.of k))`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ c.overI ⋙
    boundedConstructibleLowerStar ℓ c.overG

/-- `Rf_!^c` on bounded constructible complexes is the restriction of the derived lower shriek
`Rf_!(c)⟦ℚ̲̄_ℓ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationCompatibility :
    boundedConstructibleLowerShriekOfCompactification ℓ c ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ Rf_!(c)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarCompatibility ℓ c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ
        c.overI) _ ≪≫
    Functor.associator _ _ _

end OfCompactification

variable (f : X ⟶ Y)

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` on bounded constructible
complexes: the functor `boundedConstructibleLowerShriekOfCompactification`
attached to the compactification `compactificationOverField f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleLowerShriekOfCompactification ℓ (compactificationOverField f)

/-- The defining equation of `boundedConstructibleLowerShriek` (`ℚ̄_ℓ`-coefficient). -/
lemma boundedConstructibleLowerShriek_eq :
    boundedConstructibleLowerShriek ℓ f =
      boundedConstructibleLowerShriekOfCompactification ℓ (compactificationOverField f) :=
  rfl

/-- The derived lower shriek on bounded constructible complexes is the restriction of the
derived lower shriek `R(f)_!⟦ℚ̲̄_ℓ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    haveI := HasCompactification.of_over f
    boundedConstructibleLowerShriek ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f.left)_!⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ
    (compactificationOverField f)

end Shriek

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj


section Shriek

include ℓ k

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` on bounded
constructible complexes attached to a compactification `c = (X.left ⟶[i] Z ⟶[p] Y.left)` of
`f.left`: the extension by zero along the open immersion `i` followed by the
derived pushforward along the proper morphism `p`, both on bounded constructible complexes, for `i`
and `p` the morphisms `c.overI` and `c.overG` of `Over (Spec (.of k))`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧ :=
  boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ c.overI ⋙
    boundedConstructibleLowerStar ℓ E c.overG

/-- `Rf_!^c` on bounded constructible complexes is the restriction of the derived lower shriek
`Rf_!(c)⟦E̲⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationCompatibility :
    boundedConstructibleLowerShriekOfCompactification ℓ E c ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ Rf_!(c)⟦Profinite.continuousMapRingObj E⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarCompatibility ℓ E c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekCompatibility (Profinite.continuousMapRingObj E)
        ℓ
        c.overI) _ ≪≫
    Functor.associator _ _ _

end OfCompactification

variable (f : X ⟶ Y)

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` on bounded constructible
complexes: the functor `boundedConstructibleLowerShriekOfCompactification`
attached to the compactification `compactificationOverField f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧ :=
  boundedConstructibleLowerShriekOfCompactification ℓ E (compactificationOverField f)

/-- The defining equation of `boundedConstructibleLowerShriek` (`E`-coefficient). -/
lemma boundedConstructibleLowerShriek_eq :
    boundedConstructibleLowerShriek ℓ E f =
      boundedConstructibleLowerShriekOfCompactification ℓ E (compactificationOverField f) :=
  rfl

/-- The derived lower shriek on bounded constructible complexes is the restriction of the
derived lower shriek `R(f)_!⟦E̲⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    haveI := HasCompactification.of_over f
    boundedConstructibleLowerShriek ℓ E f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f.left)_!⟦Profinite.continuousMapRingObj E⟧ :=
  boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ E
    (compactificationOverField f)

end Shriek

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj


section Shriek

include ℓ k

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` on bounded
constructible complexes attached to a compactification `c = (X.left ⟶[i] Z ⟶[p] Y.left)` of
`f.left`: the extension by zero along the open immersion `i` followed by the
derived pushforward along the proper morphism `p`, both on bounded constructible complexes, for `i`
and `p` the morphisms `c.overI` and `c.overG` of `Over (Spec (.of k))`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ
      E⟧ :=
  boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ c.overI ⋙
    boundedConstructibleLowerStar ℓ E c.overG

/-- `Rf_!^c` on bounded constructible complexes is the restriction of the derived lower shriek
`Rf_!(c)⟦𝒪̲_E⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationCompatibility :
    boundedConstructibleLowerShriekOfCompactification ℓ E c ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ Rf_!(c)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarCompatibility ℓ E c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekCompatibility
        (Profinite.padicIntegersRingObj ℓ E) ℓ
        c.overI) _ ≪≫
    Functor.associator _ _ _

end OfCompactification

variable (f : X ⟶ Y)

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` on bounded constructible
complexes: the functor `boundedConstructibleLowerShriekOfCompactification`
attached to the compactification `compactificationOverField f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ
      E⟧ :=
  boundedConstructibleLowerShriekOfCompactification ℓ E (compactificationOverField f)

/-- The defining equation of `boundedConstructibleLowerShriek` (`𝒪_E`-coefficient). -/
lemma boundedConstructibleLowerShriek_eq :
    boundedConstructibleLowerShriek ℓ E f =
      boundedConstructibleLowerShriekOfCompactification ℓ E (compactificationOverField f) :=
  rfl

/-- The derived lower shriek on bounded constructible complexes is the restriction of the
derived lower shriek `R(f)_!⟦𝒪̲_E⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    haveI := HasCompactification.of_over f
    boundedConstructibleLowerShriek ℓ E f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f.left)_!⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ E
    (compactificationOverField f)

end Shriek

end PadicIntegersRingObj


/-! ### The derived tensor product and the derived hom -/

section TensorHom

include ℓ k

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

-- An instance proved by `sorry` keeps only the section variables its statement mentions, so its
-- hypotheses are restated as binders; they repeat section variables.
set_option linter.overlappingInstances false in
/-- The bounded constructible complexes of `ℚ̄_ℓ`-sheaves form a monoidal subcategory of
`D(Mod_{ℚ̄_ℓ,X})` for the derived tensor product: they contain the unit
`ℚ̄_ℓ,X` and are stable under `- ⊗ᴸ -` (SGA 4½ [Th. finitude], 1.6; Bhatt–Scholze, Section 6.8). It
is false for a general condensed ring: for `Λ = ℤ/4` on a geometric point of characteristic `3`,
`Tor_i^{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
instance isMonoidal_boundedConstructible [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).IsMonoidal :=
  sorry

-- An instance proved by `sorry` keeps only the section variables its statement mentions, so its
-- hypotheses are restated as binders; they repeat section variables.
set_option linter.overlappingInstances false in
/-- The bounded constructible complexes of `ℚ̄_ℓ`-sheaves are stable under the derived hom
`RHom(-, -)`, the internal hom of `D(Mod_{ℚ̄_ℓ,X})` (SGA 4½ [Th. finitude],
1.6; Bhatt–Scholze, Section 6.8). It is false for a general condensed ring: for `Λ = ℤ/4` on a
geometric point of characteristic `3`, `Ext^i_{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
instance isMonoidalClosed_boundedConstructible [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).IsMonoidalClosed :=
  sorry

/-- The derived tensor product `- ⊗ᴸ - : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` on bounded
constructible complexes: the tensor product of the monoidal structure on the
full subcategory `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` (`ObjectProperty.fullMonoidalSubcategory`), the restriction of
`-⊗ᴸ-(X)⟦ℚ̲̄_ℓ⟧` in both variables. -/
noncomputable def boundedConstructibleTensor :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  curriedTensor _

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ᵒᵖ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` on bounded
constructible complexes: the internal hom of the monoidal closed structure on
the full subcategory `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` (`ObjectProperty.fullMonoidalClosedSubcategory`), the
restriction of `RHom(X)⟦ℚ̲̄_ℓ⟧` in both variables. -/
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
      (boundedConstructible _).ι ⋙ (RHom(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧).obj (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- The adjunction with a parameter `- ⊗ᴸ - ⊣₂ RHom(-, -)` on bounded constructible complexes:
the tensor-hom adjunction of the monoidal closed structure on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`.
-/
noncomputable def boundedConstructibleTensorHomAdjunction₂ :
    boundedConstructibleTensor ℓ X ⊣₂ boundedConstructibleHom ℓ X :=
  MonoidalClosed.internalHomAdjunction₂

/-- For a fixed `K ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the tensor-hom adjunction `ihom.adjunction K` of the monoidal closed
structure on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleTensor ℓ X).obj K ⊣ (boundedConstructibleHom ℓ X).obj (op K) :=
  (boundedConstructibleTensorHomAdjunction₂ ℓ).adj K

end TensorHom

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj


section TensorHom

include ℓ k

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

-- An instance proved by `sorry` keeps only the section variables its statement mentions, so its
-- hypotheses are restated as binders; they repeat section variables.
set_option linter.overlappingInstances false in
/-- The bounded constructible complexes of `E`-sheaves form a monoidal subcategory of
`D(Mod_{E_X})` for the derived tensor product: they contain the unit `E_X` and are
stable under `- ⊗ᴸ -` (SGA 4½ [Th. finitude], 1.6; Bhatt–Scholze, Section 6.8). It is false for a
general condensed ring: for `Λ = ℤ/4` on a geometric point of characteristic `3`,
`Tor_i^{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
instance isMonoidal_boundedConstructible
    [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left)).IsMonoidal :=
  sorry

-- An instance proved by `sorry` keeps only the section variables its statement mentions, so its
-- hypotheses are restated as binders; they repeat section variables.
set_option linter.overlappingInstances false in
/-- The bounded constructible complexes of `E`-sheaves are stable under the derived hom
`RHom(-, -)`, the internal hom of `D(Mod_{E_X})` (SGA 4½ [Th. finitude], 1.6;
Bhatt–Scholze, Section 6.8). It is false for a general condensed ring: for `Λ = ℤ/4` on a geometric
point of characteristic `3`, `Ext^i_{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
instance isMonoidalClosed_boundedConstructible
    [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left)).IsMonoidalClosed :=
  sorry

/-- The derived tensor product `- ⊗ᴸ - : Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(X)⟦E̲⟧` on bounded
constructible complexes: the tensor product of the monoidal structure on the full
subcategory `Dᵇc(X)⟦E̲⟧` (`ObjectProperty.fullMonoidalSubcategory`), the restriction of
`-⊗ᴸ-(X)⟦E̲⟧` in both variables. -/
noncomputable def boundedConstructibleTensor :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤
      Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ :=
  curriedTensor _

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦E̲⟧ᵒᵖ ⥤ Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(X)⟦E̲⟧` on bounded
constructible complexes: the internal hom of the monoidal closed structure on the
full subcategory `Dᵇc(X)⟦E̲⟧` (`ObjectProperty.fullMonoidalClosedSubcategory`), the restriction
of `RHom(X)⟦E̲⟧` in both variables. -/
noncomputable def boundedConstructibleHom :
    (Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧)ᵒᵖ ⥤
      Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤
        Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ :=
  MonoidalClosed.internalHom

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦E̲⟧`, the restricted functor `K ⊗ᴸ -` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleTensorObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleTensor ℓ E X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X.left)⟦Profinite.continuousMapRingObj E⟧).obj K.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleTensor, derivedTensor]

/-- For a fixed `K ∈ Dᵇc(X)⟦E̲⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleHom ℓ E X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X.left)⟦Profinite.continuousMapRingObj E⟧).obj
        (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- The adjunction with a parameter `- ⊗ᴸ - ⊣₂ RHom(-, -)` on bounded constructible complexes:
the tensor-hom adjunction of the monoidal closed structure on `Dᵇc(X)⟦E̲⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction₂ :
    boundedConstructibleTensor ℓ E X ⊣₂ boundedConstructibleHom ℓ E X :=
  MonoidalClosed.internalHomAdjunction₂

/-- For a fixed `K ∈ Dᵇc(X)⟦E̲⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the tensor-hom adjunction `ihom.adjunction K` of the monoidal closed
structure on `Dᵇc(X)⟦E̲⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleTensor ℓ E X).obj K ⊣ (boundedConstructibleHom ℓ E X).obj (op K) :=
  (boundedConstructibleTensorHomAdjunction₂ ℓ E).adj K

end TensorHom

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj


section TensorHom

include ℓ k

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

-- An instance proved by `sorry` keeps only the section variables its statement mentions, so its
-- hypotheses are restated as binders; they repeat section variables.
set_option linter.overlappingInstances false in
/-- The bounded constructible complexes of `𝒪_E`-sheaves form a monoidal subcategory of
`D(Mod_{𝒪_{E,X}})` for the derived tensor product: they contain the unit
`𝒪_{E,X}` and are stable under `- ⊗ᴸ -` (SGA 4½ [Th. finitude], 1.6; Bhatt–Scholze, Section 6.8). It
is false for a general condensed ring: for `Λ = ℤ/4` on a geometric point of characteristic `3`,
`Tor_i^{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
instance isMonoidal_boundedConstructible
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)).IsMonoidal :=
  sorry

-- An instance proved by `sorry` keeps only the section variables its statement mentions, so its
-- hypotheses are restated as binders; they repeat section variables.
set_option linter.overlappingInstances false in
/-- The bounded constructible complexes of `𝒪_E`-sheaves are stable under the derived hom
`RHom(-, -)`, the internal hom of `D(Mod_{𝒪_{E,X}})` (SGA 4½ [Th. finitude],
1.6; Bhatt–Scholze, Section 6.8). It is false for a general condensed ring: for `Λ = ℤ/4` on a
geometric point of characteristic `3`, `Ext^i_{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
instance isMonoidalClosed_boundedConstructible
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)).IsMonoidalClosed :=
  sorry

/-- The derived tensor product `- ⊗ᴸ - : Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(X)⟦𝒪̲_E⟧` on bounded
constructible complexes: the tensor product of the monoidal structure on the
full subcategory `Dᵇc(X)⟦𝒪̲_E⟧` (`ObjectProperty.fullMonoidalSubcategory`), the restriction of
`-⊗ᴸ-(X)⟦𝒪̲_E⟧` in both variables. -/
noncomputable def boundedConstructibleTensor :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤ Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ
      E⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  curriedTensor _

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦𝒪̲_E⟧ᵒᵖ ⥤ Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(X)⟦𝒪̲_E⟧` on bounded
constructible complexes: the internal hom of the monoidal closed structure on
the full subcategory `Dᵇc(X)⟦𝒪̲_E⟧` (`ObjectProperty.fullMonoidalClosedSubcategory`), the
restriction of `RHom(X)⟦𝒪̲_E⟧` in both variables. -/
noncomputable def boundedConstructibleHom :
    (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)ᵒᵖ ⥤ Dᵇc(X.left)⟦Profinite.padicIntegersRingObj
      ℓ E⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  MonoidalClosed.internalHom

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦𝒪̲_E⟧`, the restricted functor `K ⊗ᴸ -` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleTensorObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (boundedConstructibleTensor ℓ E X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧).obj K.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleTensor, derivedTensor]

/-- For a fixed `K ∈ Dᵇc(X)⟦𝒪̲_E⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (boundedConstructibleHom ℓ E X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧).obj
        (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- The adjunction with a parameter `- ⊗ᴸ - ⊣₂ RHom(-, -)` on bounded constructible complexes:
the tensor-hom adjunction of the monoidal closed structure on `Dᵇc(X)⟦𝒪̲_E⟧`.
-/
noncomputable def boundedConstructibleTensorHomAdjunction₂ :
    boundedConstructibleTensor ℓ E X ⊣₂ boundedConstructibleHom ℓ E X :=
  MonoidalClosed.internalHomAdjunction₂

/-- For a fixed `K ∈ Dᵇc(X)⟦𝒪̲_E⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the tensor-hom adjunction `ihom.adjunction K` of the monoidal closed
structure on `Dᵇc(X)⟦𝒪̲_E⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (boundedConstructibleTensor ℓ E X).obj K ⊣ (boundedConstructibleHom ℓ E X).obj (op K) :=
  (boundedConstructibleTensorHomAdjunction₂ ℓ E).adj K

end TensorHom

end PadicIntegersRingObj

section MonoidalUpperStar

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` on bounded constructible complexes
is strong monoidal, with the comparison isomorphisms of `L((f)^*⟦ℚ̲̄_ℓ⟧)`. -/
noncomputable instance monoidal_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).Monoidal := by
  unfold boundedConstructibleUpperStar
  exact ObjectProperty.monoidalLift _ _

end MonoidalUpperStar

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj


section MonoidalUpperStar

include ℓ k

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦E̲⟧ ⥤ Dᵇc(X)⟦E̲⟧` on bounded constructible complexes
is strong monoidal, with the comparison isomorphisms of `L((f)^*⟦E̲⟧)`. -/
noncomputable instance monoidal_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f).Monoidal := by
  unfold boundedConstructibleUpperStar
  exact ObjectProperty.monoidalLift _ _

end MonoidalUpperStar

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj


section MonoidalUpperStar

include ℓ k

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦𝒪̲_E⟧ ⥤ Dᵇc(X)⟦𝒪̲_E⟧` on bounded constructible complexes
is strong monoidal, with the comparison isomorphisms of `L((f)^*⟦𝒪̲_E⟧)`. -/
noncomputable instance monoidal_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).Monoidal := by
  unfold boundedConstructibleUpperStar
  exact ObjectProperty.monoidalLift _ _

end MonoidalUpperStar

end PadicIntegersRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
