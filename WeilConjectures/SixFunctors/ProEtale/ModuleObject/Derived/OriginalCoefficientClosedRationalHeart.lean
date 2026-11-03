/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientDerivedFunctorAPI
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalCoefficientClosedRationalHeartFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalCoefficientClosedRationalHeartQbar

/-! # Rational coefficient proper closed exchange in degree zero

Source: `def-exchange-projection`, original-coefficient proper closed-exchange
step of the compactification-independence calculation.
(blueprint: lem-sp-original-coefficient-closed-rational-heart)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open AlgebraicGeometry Scheme

/-- Rational coefficient proper closed exchange in degree zero.

Source: `def-exchange-projection`, compactification-independence calculation,
original-coefficient proper closed-exchange step, reduced to the heart.

Proof: Work on affine opens V of Z₂ and their proper preimages. These are
qcqs, and hc makes the induced closed immersion constructible. For a finite
extension E, descend the finite constructible presentation data to integral
lattices after clearing the finitely many denominators on each presentation
chart. On overlaps enlarge the lattices to contain the finitely many gluing
maps, and use finite stratification induction to glue the integral models.
Inverting ell is the filtered union of multiplication by its powers on those
lattices. The integral closed-exchange calculation gives the comparison before
inversion. Proper direct image commutes with these filtered colimits, since
the complexes are bounded below uniformly; inverse image is exact and preserves
colimits. Consequently extension of scalars gives the E-exchange isomorphism.
For Qbar_ell, use exactly the finite-subextension-valued condensed ring: every
finite set of presentation coefficients and relations lies in one finite E.
Refine a finite cover of each qcqs stratum so that the presentation, relations
and gluing maps all descend, and take the directed union over finite extensions.
Apply the same bounded-below direct-image continuity to the finite-extension
exchanges. The scalar comparison is constructed through tensor and evaluation.
Its unit rectangle, canonical pullback-compositor rectangle and counit rectangle
identify the scalar and filtered maps with the literal ambient mate. This
compatibility is retained under restriction to the affine charts; restrictions
on their inverse-image cover of C detect isomorphisms. Empty strata and zero
modules satisfy the same identities. No completion of Qbar_ell or enlargement
to all valuation-continuous functions is used.
References: Hemo--Richarz--Scholbach Propositions 5.2 and 5.5, Lemma 5.3,
Theorem 7.7 and Lemma 7.9, with the tensor/unit/counit comparison of the
blueprint proper-base-change proof.
(blueprint: lem-sp-original-coefficient-closed-rational-heart) -/
theorem originalCoefficientClosedRationalHeart
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    (Λ : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hΛ : Λ = ⟨Profinite.continuousMapRingObj E⟩ ∨
      Λ = ⟨Profinite.padicAlgClRingObj ell⟩)
    (S : Scheme.{u}) (hell : IsUnit (ell : Γ(S, ⊤)))
    {Z₁ Z₂ C : Over S}
    [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
    [LocallyOfFiniteType Z₂.hom] [QuasiCompact Z₂.hom]
    (h : Z₁ ⟶ Z₂) [IsProper h.left]
    (i : C ⟶ Z₂) [IsClosedImmersion i.left]
    (hc : ∃ (U : Scheme.{u}) (j : U ⟶ Z₂.left),
      IsOpenImmersion j ∧ QuasiCompact j ∧
        Set.range i.left.base = (Set.range j.base)ᶜ)
    (M : Mod (Sheaf (ProEt.topology Z₁.left) Ab.{u + 1})
      (condensedRingObj Λ.X Z₁.left))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ.X Z₁.left) M) :
    IsIso ((refinementAmbientExchange Λ.X
      (g' := pullback.fst h.left i.left) (f' := pullback.snd h.left i.left)
      (f := h.left) (g := i.left)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  rcases hΛ with rfl | rfl
  · exact originalCoefficientClosedRationalHeartFinite ell E S hell h i hc M hM
  · exact originalCoefficientClosedRationalHeartQbar ell S hell h i hc M hM

end AlgebraicGeometry.ProEtale.CondensedRing
