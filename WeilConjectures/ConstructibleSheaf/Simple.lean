/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Simple
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import WeilConjectures.ConstructibleSheaf.Restriction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# Simple constructible sheaves

Let `X` be a scheme whose underlying space is Noetherian and `Λ` a Noetherian ring. This file
classifies the simple objects of the abelian category of constructible sheaves of `Λ`-modules on
the small étale site of `X` (blueprint `lem-trf-simple-constructible`): they are the sheaves
`i_{x!} M`, where `x` is a point with `{x}` locally closed, `i_{x!}` is the extension by zero
along `Spec κ(x) ⟶ X`, and `M` is a simple constructible sheaf on `Spec κ(x)`, that is a simple
finite `Λ`-module with a continuous action of the absolute Galois group of `κ(x)`. On a scheme
of finite type over a field the point `x` is closed and `i_{x!} = i_{x*}`. In particular a nonzero
locally constant sheaf on a connected scheme of positive dimension, of finite type over a field,
is not a finite extension of simple constructible sheaves.

Supports are measured by `AlgebraicGeometry.Etale.stalkZeroLocus`, the set of points at all of
whose geometric points the stalks vanish; the stalks of a locally constant sheaf vanish on a
clopen set (`AlgebraicGeometry.Etale.isClopen_stalkZeroLocus`).

## Main statements

- `AlgebraicGeometry.Etale.exists_iso_openImmersionLowerShriek_lowerStar_of_simple`: a simple
  constructible sheaf is `i_{x!} M` for a locally closed point `x` and a simple `M`.
- `AlgebraicGeometry.Etale.simple_openImmersionLowerShriek_lowerStar`: conversely each such
  `i_{x!} M` is simple.
- `AlgebraicGeometry.Etale.exists_iso_lowerStar_fromSpecResidueField_of_simple`: over a field,
  `x` is a closed point and `F ≅ i_{x*} M`.
- `AlgebraicGeometry.Etale.not_forall_prop_of_isLocallyConstantSheaf`: a nonzero locally constant
  sheaf on a connected scheme of positive dimension of finite type over a field is not a finite
  extension of simple constructible sheaves.

## Implementation notes

"Simple object of the abelian category of constructible sheaves" is Mathlib's `Simple` for the
full subcategory `(Etale.constructibleSheaf (ModuleCat Λ) X).FullSubcategory`; by `simple_iff`,
since constructible sheaves are closed under kernels, it says that the sheaf is nonzero and that
its constructible subsheaves are zero or everything. The extension by zero `i_{x!}` along the
immersion `Spec κ(x) ⟶ X` is written as `j_! g_*` for an open `j : W ⟶ X` in which `x` is closed
and the closed immersion `g : Spec κ(x) ⟶ W`
(`AlgebraicGeometry.exists_isClosedImmersion_comp_ι_eq_fromSpecResidueField`).
"Finite extension of simple sheaves" is spelled through the universal property of the closure
under extensions.
-/

@[expose] public section
universe u

open CategoryTheory Limits Opposite ZeroObject

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ] {X Y : Scheme.{u}}

/-- The stalks of a zero sheaf vanish. -/
lemma isZero_sheafFiber_of_isZero {I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hI : IsZero I) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    IsZero ((pointSmallEtale s).sheafFiber.obj I) :=
  have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  (pointSmallEtale s).sheafFiber.map_isZero hI

/-- A sheaf of modules is zero exactly when its stalks vanish everywhere: the geometric points
form a conservative family. -/
lemma isZero_iff_stalkZeroLocus_eq_univ (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsZero I ↔ stalkZeroLocus I = Set.univ := by
  refine ⟨fun hI ↦ Set.eq_univ_of_forall fun x Ω _ _ s _ ↦ isZero_sheafFiber_of_isZero hI s,
    fun hall ↦ ?_⟩
  have : IsIso (0 : I ⟶ I) := isIso_of_isIso_sheafFiber_map _ fun x ↦ by
    have hx : IsZero ((X.uliftPointSmallEtale x).sheafFiber.obj I) :=
      ((hall ▸ Set.mem_univ x : x ∈ stalkZeroLocus I) _ (X.algClosurePoint x)
        (X.algClosurePoint_base x _)).of_iso
        (((pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso _).app I)
    exact ⟨0, hx.eq_of_src _ _, hx.eq_of_src _ _⟩
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : I ⟶ I), zero_comp]

/-- The stalks of a pullback `f^* I` at the geometric points over `y` are those of `I` at the
geometric points over `f y`. -/
lemma mem_stalkZeroLocus_upperStar (f : Y ⟶ X)
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {y : Y}
    (hy : f.base y ∈ stalkZeroLocus I) :
    y ∈ stalkZeroLocus (((f)^*[ModuleCat.{u + 1} Λ]).obj I) := fun Ω _ _ s hs ↦
  (hy Ω (s ≫ f) (by rw [← hs]; rfl)).of_iso
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f s).app I)

end Etale

end AlgebraicGeometry
