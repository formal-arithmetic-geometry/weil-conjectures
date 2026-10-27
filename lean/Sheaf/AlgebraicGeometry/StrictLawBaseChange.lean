/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q08
-/
module

public import Sheaf.AlgebraicGeometry.RelativeBirationalLaw
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Base change of fibrewise dense smooth charts and strict laws

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 2.5 p.55, 5.1 p.113,
5.2 Definition 1 p.115 (blueprint: lem-sfb-strict-law-base-change).

The base morphism is unrestricted, so these statements also apply to all overlap
projections of a covering. The chart domain is pulled back literally; its translations
are the base changes of the original charts under the canonical product comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

/-- Fibrewise dense opens of a smooth scheme remain fibrewise dense after arbitrary base change.
Source: BLR 2.5 p.55 (blueprint: lem-sfb-strict-law-base-change).
Proof: at t over s identify the new fibre with Y_s base changed from κ(s) to κ(t), using
pullback pasting (def-pc-base-change, def-pc-fibre-product). Its projection to Y_s is open:
apply lem-sc-scheme-over-field-universally-open to Spec κ(t) over κ(s) (Stacks 0383).
The image of every nonempty open is nonempty and open, hence meets U_s; lifting an
intersection point proves density of the inverse image. This argument allows arbitrary
residue-field extensions and requires no reduction or nonemptiness assumption on T. -/
theorem fiberwiseDenseOpen_baseChange {S Y T : Scheme.{u}} (f : Y ⟶ S) [Smooth f]
    (g : T ⟶ S) (U : Y.Opens) (hU : f.IsFiberwiseDenseOpen U) :
    (pullback.snd f g).IsFiberwiseDenseOpen ((pullback.fst f g) ⁻¹ᵁ U) := by
  sorry

/-- The ambient conditions for a strict law survive arbitrary base change.
Source: BLR 5.1 pp.112--113 (blueprint: lem-sfb-strict-law-base-change).
Proof: smoothness is clause (2) of lem-pc-proper-base-change (Stacks 01VB); separatedness
is lem-weil-pbc-separated-base-change (01KU); finite type is clause (2) of
lem-sfb-finite-type-composition-base-change (01T4), applying both locally finite type and
quasi-compact base-change instances. Nonempty fibres are equivalent to surjectivity;
lem-weil-pbc-surjective-base-change (01S1) preserves this condition. A point over t yields
a point of the scheme-theoretic fibre by its residue-field map and the pullback property.
For T empty the surjectivity and nonempty-fibre assertions are vacuous. -/
theorem strictLawAmbient_baseChange {S Y T : Scheme.{u}} (f : Y ⟶ S)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [Surjective f]
    (g : T ⟶ S) :
    Smooth (pullback.snd f g) ∧ IsSeparated (pullback.snd f g) ∧
      LocallyOfFiniteType (pullback.snd f g) ∧ QuasiCompact (pullback.snd f g) ∧
      Surjective (pullback.snd f g) := by
  sorry

/-- Base change preserves relative rational representatives, their equivalence and birationality.
The implication on `Agrees` makes the construction independent of representatives.
Source: BLR 2.5 p.55 (blueprint: lem-sfb-strict-law-base-change).
Proof: base change preserves open immersions by lem-weil-pbc-open-immersion-base-change
(01JY). The density argument of the first proof works for every morphism, not only smooth
ones: on each fibre it is pullback along a field extension, whose projection is open
by lem-sc-scheme-over-field-universally-open (0383). Apply it to the domain, a common
agreement open, and the image of a birational representative. Pull back the common-open
inclusions and the equality there by Over.pullback. Functoriality preserves their equations.
For a birational chart pull back its inverse; the two composite equations remain identities,
so the image is exactly the base change of the original open image. -/
theorem relativeRationalChart_baseChange {S T : Scheme.{u}} {X Y : Over S}
    (r : RelativeRationalChart X Y) (g : T ⟶ S) :
    (r.IsRational → (r.baseChange g).IsRational) ∧
      (∀ q : RelativeRationalChart X Y, r.Agrees q →
        (r.baseChange g).Agrees (q.baseChange g)) ∧
      (r.IsBirational → (r.baseChange g).IsBirational) := by
  sorry

/-- A chosen strict birational law remains strict on Y_T; the translations are precisely the
base changes of the original D ≅ V and D ≅ W, under the canonical product comparison.
Source: BLR 5.1 p.113 and 5.2 Definition 1 p.115
(blueprint: lem-sfb-strict-law-base-change).
Proof: (1) For any fibrewise dense open in Z over B, the fibre after B' → B is a field
extension of Z_b. The projection is open by lem-sc-scheme-over-field-universally-open;
images of nonempty opens meet the original dense open. Use def-pc-base-change and
def-pc-fibre-product to identify fibres.
(2) The ambient smoothness, separatedness, finite type and surjectivity persist by
lem-pc-proper-base-change, lem-weil-pbc-separated-base-change,
lem-sfb-finite-type-composition-base-change and lem-weil-pbc-surjective-base-change.
(3) Pull back the representative on D, its maps, inverses and agreement opens. Open
immersions persist by lem-weil-pbc-open-immersion-base-change; the first step preserves
their relative density, so rational representatives and their equivalence base change.
(4) Each projection from Y_T ×_T Y_T is the base change of the corresponding projection
from Y ×_S Y along Y_T → Y, by pullback pasting. Apply (1) to D, V, W and both
projections, proving all six density conditions, even over extended residue fields.
(5) Pull back the two chart isomorphisms and their inverses. Comparing the projections
identifies these maps with the displayed left and right translations. Their images
are V_T and W_T, and their common source is exactly D_T.
(6) Pull back a dense associativity chart in triples and its four lifts to D. Step (1)
preserves its density; composition and product maps commute with base change, so its
five equations remain true. This proves rational associativity. All constructions allow
arbitrary g, including every projection from iterated fibre products of a covering base. -/
theorem strictBirationalLaw_baseChange {S T : Scheme.{u}} (Y : Over S)
    [Smooth Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [Surjective Y.hom]
    (m : RelativeRationalChart (Y ⨯ Y) Y) (hm : m.IsStrictLaw) (g : T ⟶ S) :
    (m.lawBaseChange g).IsStrictLaw ∧
      (m.lawBaseChange g).leftTranslation =
        (Over.pullback g).map m.leftTranslation ≫ prodComparison (Over.pullback g) Y Y ∧
      (m.lawBaseChange g).rightTranslation =
        (Over.pullback g).map m.rightTranslation ≫ prodComparison (Over.pullback g) Y Y := by
  sorry

end

end AlgebraicGeometry
