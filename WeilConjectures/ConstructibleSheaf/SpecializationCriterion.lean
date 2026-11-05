/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Cospecialization
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.ConstructibleSheaf.StalkZeroLocus
public import WeilConjectures.Algebra.Category.ModuleCat.FinitePresentationColimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.SixFunctors.Finite.Stalk
public import WeilConjectures.Topology.SpectralSpace.Constructible

/-!
# A specialization criterion for local constancy

Let `Y` be a locally noetherian scheme, `Λ` a noetherian ring and `G` a constructible sheaf of
`Λ`-modules on the small étale site of `Y`. Suppose that for every geometric point `s` of `Y`
and every geometric point `t` of the strict localization `Y_(s)` the cospecialization map
`G_s ⟶ G_t` (`AlgebraicGeometry.Scheme.cospecializationMap`) is bijective. Then `G` is finite
locally constant
(`AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_of_bijective_cospecializationMap`,
[SGA 4, Exp. IX, 2.11], [Stacks, Tag 0GJ2]).

The proof follows the classical argument. Fix a point `y` of `Y` and the geometric point `s`
over it with values in an algebraic closure of `κ(y)`. The stalk `M = G_s` is finitely
presented, so the identity of `M` spreads out to a linear map `α : M ⟶ G(V)` for a pointed
étale neighbourhood `(V, v)` of `s`, which we may take affine
(`ModuleCat.exists_lift_of_isColimit_of_finitePresentation`). Through the pullback `g^* G`
along `g : V ⟶ Y`, `α` is adjoint to a morphism `φ : M_V ⟶ g^* G` from the constant sheaf at
`M` (`AlgebraicGeometry.Scheme.constantSheafSpread`). Its stalk at a geometric point `r` of `V`
is, through `(g^* G)_r ≅ G_{r ≫ g}`, the germ of `α` at `(V, r)`
(`AlgebraicGeometry.Scheme.isIso_sheafFiber_map_constantSheafSpread`). A point `w` of
`V` generizing the image of `v` is the image of a point of `Y_(s)`
(`AlgebraicGeometry.Scheme.exists_strictLocalizationConeAll_π_app_base_eq`); at the
corresponding geometric point the stalk of `φ` is the cospecialization map, which is bijective.
So the kernel and cokernel of `φ`, constructible sheaves on the noetherian scheme `V`, have
vanishing stalks at all generizations of the image of `v`; since their vanishing loci are open
in the constructible topology, they contain an open neighbourhood `W` of that point
(`exists_specializes_of_isClosed_constructibleTopology_of_mem_closure`). On `W` the morphism
`φ` is an isomorphism, so `G` is constant on `W`, an étale neighbourhood of `y`.

## Main results

- `AlgebraicGeometry.Scheme.exists_etale_isConstant_upperStar_of_bijective_cospecializationMap`:
  every point of `Y` has an étale neighbourhood on which `G` is constant.
- `AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_of_bijective_cospecializationMap`:
  the criterion.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite Topology

noncomputable section

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Germ

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {R T : Scheme.{u}} (t : T ⟶ R) (G : Sheaf R.smallEtaleTopology A)
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

end Germ

section ConstantStalk

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

end ConstantStalk

end Etale

namespace Scheme

section Spread

variable {Λ : Type (u + 1)} [CommRing Λ] {S : Scheme.{u}}

end Spread

section Spread

open _root_.AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {Y : Scheme.{u}}
  (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale) (M : ModuleCat.{u + 1} Λ)
  (α : M ⟶ G.obj.obj (op V))

end Spread

section Criterion

open _root_.AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Blueprint `lem-kun-constant-constructible`: a constant sheaf of finitely generated modules is
constructible. -/
lemma isConstructibleSheaf_constantSheaf {X : Scheme.{u}} (M : ModuleCat.{u + 1} Λ)
    [Module.Finite Λ M] :
    IsConstructibleSheaf ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hlc : IsLocallyConstantSheaf
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
    Sheaf.IsConstant.isLocallyConstantSheaf (Sheaf.isConstant_of_iso _ (Iso.refl _))
  have hfin : IsFiniteSheaf
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
    ⟨fun _ _ _ r ↦ ((ModuleCat.isFinitelyGenerated_iff M).2 inferInstance).of_iso
      ((pointSmallEtale r).sheafFiberConstantSheafIso M).symm⟩
  have : IsFiniteLocallyConstantSheaf
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := ⟨⟩
  exact ⟨Stratification.trivial X, fun _ ↦ IsFiniteLocallyConstantSheaf.upperStar (𝟙 X) _⟩

end Criterion

end Scheme

end AlgebraicGeometry
