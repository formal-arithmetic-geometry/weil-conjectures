/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Compactification.Over
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

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
type over `Spec k` (`[X.Over (Spec (.of k))]` with `X ↘ Spec k` locally of finite type,
quasi-compact and separated), and all morphisms are morphisms over `Spec k`
(`[f.IsOver (Spec (.of k))]`). No further hypothesis is imposed on the schemes or morphisms. In
particular every such morphism has a compactification, by Nagata's theorem
(`AlgebraicGeometry.HasCompactification.of_isOver`), with the choice
`compactificationOverField k f`.

| functor | restriction |
| --- | --- |
| `Lf^* = L((f)^*⟦Λ⟧)` | `boundedConstructibleUpperStar` |
| `Rf_* = R((f)_*⟦Λ⟧)` | `boundedConstructibleLowerStar` |
| `j_! = D((j)_!open⟦Λ⟧)`, `j` an open immersion | `boundedConstructibleOpenImmersionLowerShriek` |

Each restriction is the `ObjectProperty.lift` of the composite of the inclusion with the functor
on the ambient derived category, so it is compatible with the inclusions by construction
(`ObjectProperty.liftCompιIso`).

The derived lower shriek is not a restriction: it is assembled on bounded constructible
complexes out of the functors above. For a compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`,
`Rf_!^c := i_! ⋙ Rp_*` (`boundedConstructibleLowerShriekOfCompactification`), and `Rf_!` is
`Rf_!^c` for the chosen compactification `compactificationOverField k f`
(`boundedConstructibleLowerShriek`). Both are compatible with the derived lower shrieks
`Rf_!(c)⟦Λ⟧` and `R(f)_!⟦Λ⟧` on the ambient derived categories
(`boundedConstructibleLowerShriekOfCompactificationCompatibility`,
`boundedConstructibleLowerShriekCompatibility`).

The adjunctions `Lf^* ⊣ Rf_*` and `j_! ⊣ j^*` restrict along the fully faithful
inclusions (`Adjunction.restrictFullyFaithful`), and so does the composition isomorphism
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` (`boundedConstructibleUpperStarComp`).

The exceptional inverse image `Rf^!` is not the restriction of a functor on the ambient derived
category: it is constructed on bounded constructible complexes directly, for the `ℓ`-adic
coefficient rings `E̲` and `ℚ̲̄_ℓ`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek`.

## Preservation results and disputed input

Pullback and extension by zero preserve bounded constructibility for the stated arbitrary
commutative condensed coefficient ring. Their proofs use finite presentations on strata and
exactness of the underlying functors.

The pushforward preservation statement remains `sorry` and is disputed below: its present
signature imposes no coefficient finiteness or homological dimension hypothesis. The geometric
hypotheses on `k` and `ℓ` do not constrain `Λ`.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

-- Compatibility: the upstream Nagata helper is absent from the live dependency.
namespace AlgebraicGeometry

/-- A morphism `f : X ⟶ Y` over a quasi-compact and quasi-separated scheme `S`, between `S`-schemes
that are separated and of finite type over `S`, has a compactification: it is separated, locally
of finite type and quasi-compact, and `Y` is quasi-compact and quasi-separated, so Nagata's
compactification theorem applies. This is not an instance, since `S` cannot be inferred from `f`;
it can be used as a local instance. -/
theorem HasCompactification.of_isOver {S X Y : Scheme.{u}} [X.Over S] [Y.Over S] (f : X ⟶ Y)
    [f.IsOver S] [IsSeparated (X ↘ S)] [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [IsSeparated (Y ↘ S)] [QuasiCompact (Y ↘ S)] [CompactSpace S] [QuasiSeparatedSpace S] :
    HasCompactification f := by
  have e := comp_over f S
  have : IsSeparated (f ≫ (Y ↘ S)) := by rw [e]; infer_instance
  have : LocallyOfFiniteType (f ≫ (Y ↘ S)) := by rw [e]; infer_instance
  have : QuasiCompact (f ≫ (Y ↘ S)) := by rw [e]; infer_instance
  have := IsSeparated.of_comp f (Y ↘ S)
  have := locallyOfFiniteType_of_comp f (Y ↘ S)
  have := QuasiCompact.of_comp f (Y ↘ S)
  have := QuasiCompact.compactSpace_of_compactSpace (Y ↘ S)
  have := quasiSeparatedSpace_of_quasiSeparated (Y ↘ S)
  infer_instance

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- The bounded constructible derived category `D_cons(X_proét, Λ_X)` of module objects over
`Λ_X = p_X^* Λ`. -/
scoped notation "Dᵇc(" X ")⟦" Λ "⟧" =>
  AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj Λ X)

private lemma boundedConstructible_of_iso {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)}
    (e : K ≅ L) (hK : boundedConstructible R K) : boundedConstructible R L := by
  refine ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e hK.1, fun n ↦ ?_⟩
  exact _root_.constructible_of_iso (R := R)
    ((DerivedCategory.homologyFunctor _ n).mapIso e) (hK.2 n)

/-! ### The pullback and the pushforward -/

section UpperLowerStar

include ℓ k

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]

set_option linter.unusedSectionVars false in
/-- The derived pullback `Lf^*` on module objects over `Λ` preserves bounded constructible
complexes. Identify the derived pullback with the functor induced by the exact module
pullback. Its cohomology is the pullback of the original cohomology, which is constructible
by finite presentations on the pulled-back stratification. Exactness also preserves the
cohomological bounds. -/
lemma boundedConstructible_leftDerivedUpperStar_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hK : boundedConstructible (condensedRingObj Λ Y) K) :
    boundedConstructible (condensedRingObj Λ X) ((L((f)^*⟦Λ⟧)).obj K) := by
  apply boundedConstructible_of_iso _
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ f).app K).symm
  refine ⟨(f)^*⟦Λ⟧.bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  exact _root_.constructible_of_iso (((f)^*⟦Λ⟧.mapDerivedCategoryHomologyFunctorIso n).app K)
    (isConstructibleModuleObject_upperStar Λ f _ (hK.2 n))

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible complexes: the
restriction of `L((f)^*⟦Λ⟧)`. -/
noncomputable def boundedConstructibleUpperStar : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((f)^*⟦Λ⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ k f K.obj K.property

/-- The restricted derived pullback is compatible with the inclusions. -/
noncomputable def boundedConstructibleUpperStarCompatibility :
    boundedConstructibleUpperStar Λ ℓ k f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ L((f)^*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` on bounded constructible complexes:
the restriction of `ProEtale.CondensedRing.leftDerivedUpperStarComp` along the fully
faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarComp {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] (g : Y ⟶ Z) [g.IsOver (Spec (.of k))] :
    boundedConstructibleUpperStar Λ ℓ k (f ≫ g) ≅
      boundedConstructibleUpperStar Λ ℓ k g ⋙ boundedConstructibleUpperStar Λ ℓ k f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (boundedConstructibleUpperStarCompatibility Λ ℓ k (f ≫ g) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp Λ f g) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility Λ ℓ k g).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility Λ ℓ k f).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The derived pushforward `Rf_*` on module objects over `Λ` preserves bounded constructible
complexes. -/
/- STATEMENT-DISPUTED: the hypotheses do not constrain Λ. Take k algebraically closed of
characteristic p, ℓ ≠ p, Λ the discrete condensed ring F_p, f : A¹_k ⟶ Spec k and the
constant rank-one module in degree zero. Artin–Schreier gives H¹(A¹_k, F_p) =
k[t] / {a^p - a}, an infinite-dimensional F_p-space, so Rf_* is not constructible. -/
lemma boundedConstructible_rightDerivedLowerStar_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hK : boundedConstructible (condensedRingObj Λ X) K) :
    boundedConstructible (condensedRingObj Λ Y) ((R((f)_*⟦Λ⟧)).obj K) :=
  sorry

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible complexes:
the restriction of `R((f)_*⟦Λ⟧)`. -/
noncomputable def boundedConstructibleLowerStar : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R((f)_*⟦Λ⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj Λ ℓ k f K.obj K.property

/-- The restricted derived pushforward is compatible with the inclusions. -/
noncomputable def boundedConstructibleLowerStarCompatibility :
    boundedConstructibleLowerStar Λ ℓ k f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f)_*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes: the restriction of
`ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction :
    boundedConstructibleUpperStar Λ ℓ k f ⊣ boundedConstructibleLowerStar Λ ℓ k f :=
  Adjunction.restrictFullyFaithful (derivedUpperStarLowerStarAdjunction Λ f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ k f).symm
    (boundedConstructibleLowerStarCompatibility Λ ℓ k f).symm

end UpperLowerStar

/-! ### The extension by zero along an open immersion -/

section OpenImmersion

include ℓ k

variable {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
  (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]

set_option linter.unusedSectionVars false in
/-- The extension by zero `j_!` along an open immersion, applied levelwise to complexes of
module objects over `Λ`, preserves bounded constructible complexes. Quasi-compactness of `j`
follows from that of its composite with the structure morphism. The exact induced derived
functor preserves cohomological bounds, and its cohomology sheaves are the extensions by zero
of the original cohomology sheaves. These are constructible by the open–closed stratification
argument. -/
lemma boundedConstructible_openImmersionLowerShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)))
    (hK : boundedConstructible (condensedRingObj Λ U) K) :
    boundedConstructible (condensedRingObj Λ X) ((D((j)_!open⟦Λ⟧)).obj K) := by
  have : QuasiCompact (j ≫ (X ↘ Spec (.of k))) := by
    rw [comp_over j (Spec (.of k))]
    infer_instance
  have := QuasiCompact.of_comp j (X ↘ Spec (.of k))
  refine ⟨(j)_!open⟦Λ⟧.bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  exact _root_.constructible_of_iso
    (((j)_!open⟦Λ⟧.mapDerivedCategoryHomologyFunctorIso n).app K)
    (isConstructibleModuleObject_openImmersionLowerShriek Λ j _ (hK.2 n))

/-- The extension by zero `j_! : Dᵇc(U)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` along an open immersion on bounded
constructible complexes: the restriction of the levelwise functor `D((j)_!open⟦Λ⟧)`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriek : Dᵇc(U)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ D((j)_!open⟦Λ⟧))
    fun K ↦ boundedConstructible_openImmersionLowerShriek_obj Λ ℓ k j K.obj K.property

/-- The restricted extension by zero is compatible with the inclusions. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekCompatibility :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ D((j)_!open⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `j_! ⊣ j^*` along an open immersion on bounded constructible complexes: the
restriction of `ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction`
along the fully faithful inclusions, the levelwise `D((j)^*⟦Λ⟧)` being identified with the
derived pullback `L((j)^*⟦Λ⟧)` that `boundedConstructibleUpperStar` restricts. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j ⊣ boundedConstructibleUpperStar Λ ℓ k j :=
  Adjunction.restrictFullyFaithful
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ k j).symm
    (boundedConstructibleUpperStarCompatibility Λ ℓ k j).symm

end OpenImmersion

/-! ### The derived lower shriek -/

/-- The compactification of a morphism `f` of separated `k`-schemes of finite type chosen by
Nagata's theorem (`AlgebraicGeometry.HasCompactification.of_isOver`): the compactification
`HasCompactification.compactification f` for the instance it provides. It is the
compactification defining `boundedConstructibleLowerShriek`. -/
noncomputable abbrev compactificationOverField (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] : Compactification f :=
  haveI := HasCompactification.of_isOver (S := Spec (.of k)) f
  HasCompactification.compactification f

section Shriek

include ℓ k

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]

section OfCompactification

variable {f : X ⟶ Y} [f.IsOver (Spec (.of k))] (c : Compactification f)

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible
complexes attached to a compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`: the extension by zero
along the open immersion `i` followed by the derived pushforward along the proper morphism `p`,
both on bounded constructible complexes. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧ :=
  boundedConstructibleOpenImmersionLowerShriek Λ ℓ k c.i ⋙ boundedConstructibleLowerStar Λ ℓ k c.g

/-- `Rf_!^c` on bounded constructible complexes is the restriction of the derived lower shriek
`Rf_!(c)⟦Λ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationCompatibility :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ k c ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ Rf_!(c)⟦Λ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarCompatibility Λ ℓ k c.g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ k c.i)
      _ ≪≫
    Functor.associator _ _ _

end OfCompactification

variable (f : X ⟶ Y) [f.IsOver (Spec (.of k))]

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible complexes:
the functor `boundedConstructibleLowerShriekOfCompactification` attached to the compactification
`compactificationOverField k f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧ :=
  boundedConstructibleLowerShriekOfCompactification Λ ℓ k (compactificationOverField k f)

lemma boundedConstructibleLowerShriek_eq :
    boundedConstructibleLowerShriek Λ ℓ k f =
      boundedConstructibleLowerShriekOfCompactification Λ ℓ k (compactificationOverField k f) :=
  rfl

/-- The derived lower shriek on bounded constructible complexes is the restriction of the
derived lower shriek `R(f)_!⟦Λ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    haveI := HasCompactification.of_isOver (S := Spec (.of k)) f
    boundedConstructibleLowerShriek Λ ℓ k f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f)_!⟦Λ⟧ :=
  boundedConstructibleLowerShriekOfCompactificationCompatibility Λ ℓ k
    (compactificationOverField k f)

end Shriek


end AlgebraicGeometry.ProEtale.CondensedRing
