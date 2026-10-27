/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.Topology.Sober
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Normalization through an integral locally birational scheme

Source: Stacks Project, Morphisms, Tags 035Q (3), including its reductions footnote,
and 0CDV (blueprint: lem-sfb-normalization-integral-birational-factor).

## Main declarations

* `Hom.reducedRestriction`: the actual induced morphism on reductions of an open restriction.
* `exists_iso_reducedNormalization_of_integral_birational`: comparison over the target.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The morphism on reductions induced by restriction over an open of the target.
It is constructed by composing the source reduction inclusion with the restriction of `f`,
then applying the canonical factorization through the target reduction.
Source: Stacks Project, Morphisms, Tag 035Q (3), reductions footnote
(blueprint: lem-sfb-normalization-integral-birational-factor). -/
noncomputable def Hom.reducedRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (f ⁻¹ᵁ U).toScheme.nilradical.subscheme ⟶ U.toScheme.nilradical.subscheme :=
  ((f ⁻¹ᵁ U).toScheme.nilradical.subschemeι ≫ f ∣_ U).liftNilradical

/-- Componentwise normalization is unchanged by an integral morphism that is locally
birational on reductions, without a normality or Noetherian hypothesis on either scheme.
Source: Stacks Project, Morphisms, Tags 035Q (3), including its reductions footnote,
and 0CDV (blueprint: lem-sfb-normalization-integral-birational-factor).

Proof:
1. Every quasi-compact open W of X' is covered by finitely many intersections with
   inverse images of affine opens U of X. Each inverse image has finitely many
   irreducible components. The nonempty traces on W are irreducible; their closures
   give a finite irreducible closed cover of W, so W has finitely many components
   (def-weil-irreducible-components).
2. Write U = Spec A and its inverse image V = Spec B. Integrality gives an integral
   ring map A to B (def-weil-finite-integral-morphism). Reduction preserves points and
   residue fields (def-weil-pbc-scheme-reduction and def-weil-residue-field). The
   assumed reduced generic stalk isomorphisms therefore identify the corresponding
   generic residue fields via the actual maps induced by the morphism. Their finite
   products C_U and C_V have an isomorphism phi compatible with A to B.
3. This isomorphism carries the integral closure D_A in C_U onto D_B in C_V.
   One direction follows by mapping a monic equation. In the other direction an
   element integral over B is integral over A by lem-weil-pbc-integral-transitive;
   transport its monic equation through phi inverse. This uses the subring of
   integral elements (def-weil-pbc-integral-closure) and no injectivity of A to B.
4. By lem-sfb-normalization-generic-residue-affine-charts, the normalization over U
   is Spec D_A and that over V is Spec D_B. Applying contravariant Spec
   (def-weil-affine-spectrum) to phi inverse restricted to D_B gives an isomorphism
   over X on these opens, by compatibility of the structural ring maps.
5. Over affine W contained in U the generic residue product projections commute
   with phi, factor by factor. The restriction clause of the same chart lemma
   identifies the maps on D_A and D_B with these projections. Hence these local
   isomorphisms and their inverses agree on overlaps and glue
   (lem-weil-pbc-scheme-morphism-gluing). Their composites are identities on the
   cover and thus globally; their structural equations glue as well. The resulting
   e identifies the factor e.hom followed by the normalization of X' with that
   normalization transported along e (def-weil-pbc-reduced-normalization).
   For an empty target the source is empty, and the empty covers give the empty
   isomorphism. No reducedness of X or X' is used. -/
theorem exists_iso_reducedNormalization_of_integral_birational
    {X X' : Scheme.{u}} (α : X' ⟶ X) [IsIntegralHom α]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U.toScheme).Finite)
    (hcomponents : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents (α ⁻¹ᵁ U).toScheme).Finite)
    (hgeneric : ∀ U : X.Opens, IsCompact (U : Set X) →
      Set.BijOn (α.reducedRestriction U)
        (genericPoints (α ⁻¹ᵁ U).toScheme.nilradical.subscheme)
        (genericPoints U.toScheme.nilradical.subscheme))
    (hstalk : ∀ U : X.Opens, IsCompact (U : Set X) →
      ∀ η : (α ⁻¹ᵁ U).toScheme.nilradical.subscheme,
        η ∈ genericPoints (α ⁻¹ᵁ U).toScheme.nilradical.subscheme →
          IsIso ((α.reducedRestriction U).stalkMap η)) :
    ∃ e : X.reducedNormalization ≅ X'.reducedNormalization,
      e.hom ≫ X'.fromReducedNormalization ≫ α = X.fromReducedNormalization := by
  sorry

end AlgebraicGeometry.Scheme
