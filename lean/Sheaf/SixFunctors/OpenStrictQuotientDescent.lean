/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y8
-/
module

public import Sheaf.SixFunctors.AugmentedStrictIntegralCompletion

/-! # OpenStrictQuotientDescent

Source: Stacks Project, proetale.tex, Tag 099N (2),(5), and sites-cohomology.tex,
Tags 0G7E and 07A4 (blueprint: lem-sf-open-strict-quotient-descent).
The index n denotes exponent n+1. Site and coefficient universes are independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenQuotientCompletion
open CompletedTowerIndependent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {V W : Scheme.{t}} (e : V ⟶ W) [IsOpenImmersion e]
  (o : IntegralOpenReduction.Operations l E e)

attribute [local irreducible] restrict HasDerivedCategory.standard

/-- Strict augmented quotient towers commute with exact open restriction.
Source: Stacks Project, proetale.tex Tag 099N (2),(5), and
sites-cohomology.tex Tags 0G7E and 07A4
(blueprint: lem-sf-open-strict-quotient-descent).
Proof: use the slice-to-open equivalence and the specified constant-section
normalization of the finite coefficient maps. Both composites with a quotient
transition agree on constant sections, so those maps preserve all transitions
and are isomorphisms. The quotient projections identify the completed coefficient
map with the limit of these isomorphisms. The coefficient equivalence o already
specifies the ordinary restriction and the transports on sections. Ringed
restriction preserves flat terms and K-flatness. At every degree and quotient level,
the inverse-image tensor isomorphism sends a restricted pure tensor to the same
pure tensor. These maps commute with differentials, transitions and augmentation:
the respective formulas are d(x) tensor a, x tensor r(a), and x tensor one.
Tensor universality gives one natural isomorphism of strict tower complexes.
Localize the flat-term K-flat representatives. Change of rings preserves their
quasi-isomorphisms, which are detected levelwise on strict towers. Uniqueness of
left-derived computation comparisons gives tau and its computes equation; the
strict augmentation square descends to the displayed augmented equation.
This is before applying Rlim and makes no claim about Roos or module pullback.
For the identity open the tensor maps are identities; for the empty open all
module maps are the unique maps; the same formulas cover exponent one and zero
complexes. Neither good representatives nor exact localization needs a bound or
quasi-compactness. -/
theorem openStrictQuotientDescent
    (_d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (_hd : _d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E}) :
    Nonempty (StrictComparison l E e o) := by
  sorry

end WeilConjectures.OpenQuotientCompletion
