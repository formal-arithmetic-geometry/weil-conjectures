/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineChartTransitions

/-!
# Coherence on original elements of the affine section modules

Source: Stacks Project, Tag 0BLH, first two proof paragraphs; Tag 05EL, item (1).
(blueprint: lem-sbc-punctured-completion-affine-chart-generator-coherence)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The square and cocycle paths agree on the images of original module elements.
This checks maps already supplied; it constructs no section module or equivalence.

Source: Stacks Project, Tag 0BLH, second proof paragraph (the object check);
Tag 05EL, item (1), its square and cocycle clauses.
(blueprint: lem-sbc-punctured-completion-affine-chart-generator-coherence)

Proof: every V_i is affine by hypothesis.
First, b_right on the diagonal i=j and b_scalar show that c_i intertwines
A-scalars with the structural action on Gamma(Y,V_i). The two b formulas
identify alpha_ij on chart generators with restriction from V_i to V_i intersect V_j.
Use b_scalar and the affine basic-open localization property to extend these
identifications to fractions: b_ij(m/f_i^a) is the restriction of c_j(m) divided
by the image of f_i^a. Localizing b_ij further at f_k identifies the iterated
module with sections on V_i intersect V_j intersect V_k. The target section
map is an equivalence, since this is a principal open in the affine double
intersection. Under that equivalence the two cocycle routes take m to its
restriction to the triple intersection. On a fraction (m/f_j^a)/f_k^b both
routes divide that restriction by f_j^a f_k^b. The canonical swap exchanges
these denominators. In particular, setting both denominators equal to one gives
the asserted equality for each original chart element; the source restriction
maps coincide by functoriality of the structure presheaf.

For square, localize d_j at f_i. Structural C-linearity d_scalar and d_chart
identify the base change of alpha_ij on every pure tensor with restriction
between the completed principal opens: z tensor (m/f_j^a) maps to z times the
pullback restriction of c_i(m), divided by the image of f_j^a. This follows
first at denominator one from naturality of p.app and b_left and b_right,
then for all denominators because their structural actions are invertible
on the appropriate open. Additivity extends it to every tensor. The comparison
map sends (z tensor m)/1 to z tensor (m/1), and its fraction formula follows
by the same uniqueness property. Now d_prime says both square routes on an
original m' are restriction of D.toCompleted.appTop(e(m')) to the completed
double intersection. On (m'/f_i^a)/f_j^b both divide that same section by
f_i^a f_j^b. D.over ensures that the structural images of these denominators
agree on the two sides. The localized d_j is an equivalence to sections there,
so their images determine equality. Setting both denominators equal to one
proves the asserted square equation on each original completed section. There is no flatness
or covering assumption. Zero principal
opens give zero modules and all identities hold there; with t=0 the clauses
are vacuous.
-/
theorem affine_chart_transition_generator_coherence
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hf : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ U)
    (hV : ∀ i, IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)))
    (T : AffineChartTransitions D t f) :
    (∀ i j : Fin t,
      ∀ m : T.F.M',
      T.F.squareLeft i j (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
        T.F.squareRight i j (LocalizedModule.mk (LocalizedModule.mk m 1) 1)) ∧
    (∀ i j k : Fin t,
      ∀ m : FormalGlueing.piece (f i) (T.F.M i),
      T.F.cocycleLeft i j k (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
        T.F.cocycleRight i j k (LocalizedModule.mk (LocalizedModule.mk m 1) 1)) := by sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
