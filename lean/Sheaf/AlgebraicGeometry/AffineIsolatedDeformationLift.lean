/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import WeilConjectures.Algebra.FiniteTypeLiftNilpotent
import WeilConjectures.AlgebraicGeometry.ArtinianIdealLengthOneFiltration
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness

/-! # Lifting prescribed isolated local deformations of an affine scheme

Source: Stacks Project, Tag 0DZF, `lemma-isolated`, first smooth arrow, unpacked
using Tag 0DYX, `lemma-affine`, and `example-rings`
(blueprint: lem-sfb-affine-isolated-deformation-lift).

A special-fibre marking is given by a pullback square with upper-left vertex `V`.
The conclusion uses the same representation for the reduction marking: a map
`l : Y ⟶ Y'` exhibiting `Y` as the pullback over `A`. Such a square is equivalently
a specified isomorphism from the chosen fibre product to `Y`, over `Spec A`.
Algebra isomorphisms of stalks are ring isomorphisms together with their scalar
equations; this avoids introducing additional choices of stalk algebra instances.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Prescribed marked local lifts at the isolated nonsmooth points of an affine
scheme extend to an affine flat lift.
Source: Stacks Project, Tags 0DZF and 0DYX, and `example-rings`
(blueprint: lem-sfb-affine-isolated-deformation-lift).

Proof plan:
1. `lem-weil-pbc-finite-dim-algebra-artinian` and
`lem-weil-pbc-artinian-local-noetherian-nilpotent` make the coefficient rings
Artinian Noetherian with nilpotent maximal ideals. The reduction kernel is
nilpotent. Every prime of any algebra over a coefficient ring contains the
extended maximal ideal. Thus the special-fibre maps identify points uniquely;
localization always uses the inverse image of the same multiplicative subset.
2. Write `Y = Spec B` by `lem-weil-pbc-affine-open-spec-points`. The one-summand
case of `lem-sbc-finite-affine-tensor-base-change` identifies its special fibre
`P = B ⊗[A] k` with the coordinate algebra of `V`.
`lem-pc-affine-finite-type-algebra` and `lem-weil-pbc-finite-type-lift-nilpotent`
make `B` finite type over `A`. Flatness is
`lem-weil-pbc-flat-morphism-affine-criterion`. The stalk dictionary
`lem-weil-pbc-affine-open-stalk-localization` interprets the given markings.
3. Filter the reduction kernel using
`lem-weil-pbc-artinian-ideal-length-one-filtration`. Its simple quotients are
annihilated by the maximal ideal (nilpotence rules out surjective multiplication),
so the intermediate coefficient reductions are small square-zero extensions.
Base change each `D i` to these rings; tensor associativity retains the markings,
flatness follows from `def-weil-pbc-flat-ring-map`, and nilpotent quotients remain
local. Start the induction with the inverse of the supplied local marking.
4. At a small extension with kernel `I`, put `N = P ⊗[k] I`. For degrees one and
two, `lem-sfb-cotangent-ext-smooth-support` makes the cotangent Ext modules finite,
compatible with localization, and supported at the listed maximal ideals.
The ring `P` is Noetherian by `lem-weil-pbc-finite-type-algebra-noetherian`.
`lem-sfb-finite-maximal-support-localization` identifies each Ext module with
the product of its localizations at those ideals.
5. By `lem-sfb-flat-algebra-small-extension-control`, the obstruction lies in
this degree-two Ext module. Each prescribed local lift kills its localization.
Injectivity of the product map kills the global obstruction. Choose a marked
flat lift; it is finite type by nilpotent lifting. Its localizations are flat by
`lem-pc-affine-flat-module-localization-preserves-flatness`.
6. The same small-extension control identifies marked lifts as a torsor under
degree-one Ext. The differences from the prescribed local marked lifts form a
tuple of local torsor elements. Surjectivity of the product map lifts this tuple
to a global element. Adjust the lift by that element. Compatibility of the
torsor action with localization supplies local isomorphisms commuting with the
previous reduction markings. Repeat, preserving these equations at each step.
For an empty list the two Ext modules vanish and no adjustment is required.
7. Take the spectrum of the final lifted algebra. The affine tensor base-change
formula gives the pullback square in the conclusion. The localization flatness
lemma gives stalkwise flatness, hence `def-weil-flat-morphism`. Translate the
marked algebra isomorphisms using the stalk dictionary. Composing the induction
equations gives exactly the final equation with `δ`. The construction includes
the identity reduction, the empty scheme, and `r = 0`. -/
theorem exists_affine_isolated_deformation_lift
    (k A' A : Type u) [Field k] [CommRing A'] [CommRing A]
    [Algebra k A'] [Algebra k A] [Algebra A' A] [IsScalarTower k A' A]
    [FiniteDimensional k A'] [FiniteDimensional k A]
    [IsLocalRing A'] [IsLocalRing A]
    (ε' : A' →ₐ[k] k) (ε : A →ₐ[k] k)
    (hε' : RingHom.ker ε'.toRingHom = IsLocalRing.maximalIdeal A')
    (hε : RingHom.ker ε.toRingHom = IsLocalRing.maximalIdeal A)
    (hsurj : Function.Surjective (algebraMap A' A))
    (haug : ε.toRingHom.comp (algebraMap A' A) = ε'.toRingHom)
    (V : Scheme.{u}) [IsAffine V] (f : V ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (r : ℕ) (p : Fin r → V) (hp : Function.Injective p)
    (hclosed : ∀ i : Fin r, IsClosed ({p i} : Set V))
    (hsmooth : ∀ x : V, x ∉ Set.range p →
      ∃ U : V.Opens, x ∈ U ∧ Smooth (U.ι ≫ f))
    (Y : Scheme.{u}) [IsAffine Y] (g : Y ⟶ Spec (.of A)) [Flat g]
    (j : V ⟶ Y)
    (hspecial : IsPullback j f g (Spec.map (CommRingCat.ofHom ε.toRingHom)))
    (D : Fin r → Type v) [∀ i : Fin r, CommRing (D i)]
    [∀ i : Fin r, IsLocalRing (D i)] [∀ i : Fin r, Algebra A' (D i)]
    [∀ i : Fin r, Module.Flat A' (D i)]
    [∀ i : Fin r, Algebra.EssFiniteType A' (D i)]
    (δ : ∀ i : Fin r, (D i ⊗[A'] A) ≃+* Y.presheaf.stalk (j (p i)))
    (hδ : ∀ (i : Fin r) (a : A), δ i (1 ⊗ₜ[A'] a) =
      (StructureSheaf.toStalk A (g (j (p i))) ≫ g.stalkMap (j (p i))).hom a) :
    ∃ (Y' : Scheme.{u}) (g' : Y' ⟶ Spec (.of A')) (l : Y ⟶ Y'),
      IsAffine Y' ∧ Flat g' ∧
      IsPullback l g g' (Spec.map (CommRingCat.ofHom (algebraMap A' A))) ∧
      ∃ β : ∀ i : Fin r, Y'.presheaf.stalk (l (j (p i))) ≃+* D i,
        (∀ (i : Fin r) (a : A'),
          β i ((StructureSheaf.toStalk A' (g' (l (j (p i)))) ≫
            g'.stalkMap (l (j (p i)))).hom a) = algebraMap A' (D i) a) ∧
        (∀ (i : Fin r) (z : Y'.presheaf.stalk (l (j (p i)))),
          δ i (β i z ⊗ₜ[A'] (1 : A)) = l.stalkMap (j (p i)) z) := by
  sorry

end AlgebraicGeometry
