/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FSLogGroupAction
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.AlgebraicGeometry.FineLogStalkChartSpreading
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Sheaf.AlgebraicGeometry.TameUnitExtensionCharacter

/-!
# Equivariant sharp charts for tame geometric stabilizers

Source: Illusie--Laszlo--Orgogozo, Exposé VI, Proposition 3.5(a), §3.4 and proof
3.7(a), printed pp.74--75 (blueprint: lem-per-very-tame-equivariant-sharp-chart).

The characteristic is the existing quotient of the actual étale log stalk by units.
Actions on its germs are tested using relative pointed étale diagrams, the presentation
used by `EtaleLogHom`. The coefficient ring is exactly Z[zeta_n,1/n], lifted only to
match the scheme universe. The scheme chart is pinned to evaluation of the coefficient
map and the given log chart. Multiplicative notation writes the sharp monoid's zero as 1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The actual cyclotomic coefficient ring Z[zeta_n,1/n], with a universe lift.
Source: ILO VI §3.4 (blueprint: lem-per-very-tame-equivariant-sharp-chart). -/
abbrev SharpChartCyclotomicRing (n : ℕ) :=
  ULift.{u} (Localization.Away (n : CyclotomicRing n ℤ ℚ))

/-- Data of the sharp chart in ILO VI 3.5(a). The pairing is on the abelianization
and the actual group completion. Its cyclotomic form specializes under the coefficient
map to the strict-local pairing. The eigenvector equation is an equality of log sections,
with the scalar lifted through the log unit identification. The model action is specified
on every basis monomial, including coefficients. `toModel_eq` makes the scheme chart
precisely the morphism induced by the displayed coefficient and log charts, and `isChart`
is its strictness for the standard monoid log structure on the model.
Source: ILO VI §3.4 and Proposition 3.5(a), pp.74--75
(blueprint: lem-per-very-tame-equivariant-sharp-chart). -/
structure EquivariantSharpChart (X : FineSaturatedLogScheme.{u})
    {G : Type v} [Group G] (a : FSLogGroupAction G X) (H : Subgroup G)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme) where
  fineSaturated : IsFineSaturatedMonoid (X.logStructure.characteristic t)
  sharp : ∀ q : X.logStructure.characteristic t, IsUnit q → q = 1
  W : X.scheme.Etale
  point : (Scheme.pointSmallEtale t).fiber.obj W
  action : H →* Aut W.left
  point_fixed : ∀ h : H, point.left ≫ (action h).hom = point.left
  action_over : ∀ h : H, (action h).hom ≫ W.hom = W.hom ≫ (a.baseAction h.val).hom
  chart : X.logStructure.characteristic t →* X.logStructure.monoidSheaf.obj.obj (op W)
  isChart : X.logStructure.IsChart W chart
  characteristic_identity : ∀ q : X.logStructure.characteristic t,
    Associates.mk (X.logStructure.toEtalePrelogStructure.germ t W point (chart q)) = q
  coefficient : SharpChartCyclotomicRing.{u} (Nat.card H) →+* Γ(W.left, ⊤)
  coefficient_fixed : ∀ (h : H) (c : SharpChartCyclotomicRing.{u} (Nat.card H)),
    (action h).hom.appTop (coefficient c) = coefficient c
  character : TensorProduct ℤ (Additive (Abelianization H))
      (Additive (Algebra.GrothendieckGroup (X.logStructure.characteristic t))) →+
    Additive (rootsOfUnity (Nat.card H) (strictLocalRing X.scheme t))
  cyclotomicCharacter : TensorProduct ℤ (Additive (Abelianization H))
      (Additive (Algebra.GrothendieckGroup (X.logStructure.characteristic t))) →+
    Additive (rootsOfUnity (Nat.card H) (SharpChartCyclotomicRing.{u} (Nat.card H)))
  character_germ : ∀ z, restrictRootsOfUnity
      ((strictLocalGerm X.scheme t W point).hom.comp coefficient) (Nat.card H)
      (cyclotomicCharacter z).toMul = (character z).toMul
  eigenvector : ∀ (h : H) (q : X.logStructure.characteristic t),
    ∃ z : (X.logStructure.monoidSheaf.obj.obj (op W))ˣ,
      X.logStructure.alpha.app (op W) z.val =
        coefficient (((cyclotomicCharacter (TensorProduct.tmul ℤ
          (Additive.ofMul (Abelianization.of h))
          (Additive.ofMul (Algebra.GrothendieckGroup.of q)))).toMul).val.val) ∧
      (a.logMap h.val).sectionMap W W (action h).hom
        (by simpa only [a.base_eq] using action_over h) (chart q) = z.val * chart q
  modelAction : H →* Aut (Spec (.of (MonoidAlgebra
    (SharpChartCyclotomicRing.{u} (Nat.card H)) (X.logStructure.characteristic t))))
  model_diagonal : ∀ (h : H) (q : X.logStructure.characteristic t)
      (c : SharpChartCyclotomicRing.{u} (Nat.card H)),
    (Scheme.ΓSpecIso (.of (MonoidAlgebra
      (SharpChartCyclotomicRing.{u} (Nat.card H)) (X.logStructure.characteristic t)))).hom
      ((modelAction h).hom.appTop
        ((Scheme.ΓSpecIso (.of (MonoidAlgebra
          (SharpChartCyclotomicRing.{u} (Nat.card H))
          (X.logStructure.characteristic t)))).inv (MonoidAlgebra.single q c))) =
    MonoidAlgebra.single q
      ((((cyclotomicCharacter (TensorProduct.tmul ℤ
        (Additive.ofMul (Abelianization.of h))
        (Additive.ofMul (Algebra.GrothendieckGroup.of q)))).toMul).val.val) * c)
  toModel : W.left ⟶ Spec (.of (MonoidAlgebra
    (SharpChartCyclotomicRing.{u} (Nat.card H)) (X.logStructure.characteristic t)))
  toModel_eq : toModel =
    (ΓSpec.adjunction.homEquiv W.left (op (.of (MonoidAlgebra
      (SharpChartCyclotomicRing.{u} (Nat.card H)) (X.logStructure.characteristic t)))))
      (CommRingCat.ofHom (MonoidAlgebra.liftNCRingHom coefficient
        ((X.logStructure.alpha.app (op W)).hom.comp chart)
        (fun _ _ ↦ Commute.all _ _))).op
  equivariant : ∀ h : H, (action h).hom ≫ toModel = toModel ≫ (modelAction h).hom

/-- A tame geometric stabilizer fixing the characteristic has the sharp diagonal
chart of ILO VI 3.5(a), without log regularity or triviality on the stratum.
`H` is exactly the geometric stabilizer by `hH`. Triviality on the characteristic and
fixedness of strict-local roots are expressed on all pointed relative étale diagrams:
`q.left ≫ k = p.left` identifies the two germs and `hk` identifies the given action.
These tests are not vacuous: rebasing any neighbourhood along an automorphism supplies
such a diagram. Invertibility in Ω is equivalent to invertibility in the residue field
of the strict local ring, since that residue field embeds into Ω.

Source: ILO VI Proposition 3.5(a) and proof 3.7(a), pp.74--75
(blueprint: lem-per-very-tame-equivariant-sharp-chart).

Proof:
1. Take an fs chart P at t. Localize at its unit face F and apply
lem-trf-fs-face-sharpening. The characteristic Q is fs sharp, Q^gp is finite free,
and the stalk group completion is an extension of Q^gp by the strict-local units.
2. Affine pointed neighbourhoods are cofinal
(lemma-weil-pbc-affine-neighbourhood-cofinal), so A is the strict henselization and is
strictly henselian by lem-weil-pbc-strict-henselization-local-structure. Stabilizer
members act identically on its residue field and n=|H| is a unit. A free-lattice
section sends Q into M: any lift differs from it by a unit. Apply
lem-per-tame-unit-extension-character to obtain the section and the pairing χ.
The unit correction stays in the positive monoid, so restriction gives a stalk chart
whose induced map to the characteristic is the identity.
3. The unit face of this chart is {1}, and Q times A-units maps bijectively to the log
stalk. Apply lem-trf-fine-log-stalk-chart-spreading. Spread the finitely many generators,
character values, and equivariance equations to a common pointed étale neighbourhood.
A finite product of its H-translates gives an H-equivariant neighbourhood; restrict to
the common invariant open where all the equations and the chart condition hold.
4. The strict-local roots are fixed because their residues are fixed and prime-to-
characteristic roots have unique Hensel lifts. By lem-sbc-strict-local-roots-of-unity
choose a primitive nth root and spread it with n inverted. This supplies the displayed
cyclotomic coefficient homomorphism and the cyclotomic pairing. The monoid algebra
has basis single q 1 and multiplication single q 1 * single r 1 = single (q*r) 1.
The pairing defines the diagonal model action. Evaluation of its basis monomials is
exactly the coefficient-valued log chart, proving strict equivariance.
-/
theorem exists_equivariant_sharp_chart
    (X : FineSaturatedLogScheme.{u}) (G : Type v) [Group G] [Finite G]
    (a : FSLogGroupAction G X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
    (H : Subgroup G) (hH : ∀ g : G, g ∈ H ↔ t ≫ (a.baseAction g).hom = t)
    (htame : IsUnit (Nat.card H : Ω))
    (hcharacteristic : ∀ (h : H) (U V : X.scheme.Etale)
      (p : (Scheme.pointSmallEtale t).fiber.obj U)
      (q : (Scheme.pointSmallEtale t).fiber.obj V) (k : V.left ⟶ U.left)
      (hk : k ≫ U.hom = V.hom ≫ (a.logMap h.val).base),
      q.left ≫ k = p.left →
      ∀ s : X.logStructure.monoidSheaf.obj.obj (op U),
        Associates.mk (X.logStructure.toEtalePrelogStructure.germ t V q
          ((a.logMap h.val).sectionMap U V k hk s)) =
        Associates.mk (X.logStructure.toEtalePrelogStructure.germ t U p s)) :
    Nonempty (EquivariantSharpChart X a H t) ∧
      ∀ (h : H) (U V : X.scheme.Etale)
        (p : (Scheme.pointSmallEtale t).fiber.obj U)
        (q : (Scheme.pointSmallEtale t).fiber.obj V) (k : V.left ⟶ U.left)
        (_hk : k ≫ U.hom = V.hom ≫ (a.logMap h.val).base),
        q.left ≫ k = p.left → ∀ r : Γ(U.left, ⊤),
          (strictLocalGerm X.scheme t U p r) ^ Nat.card H = 1 →
          strictLocalGerm X.scheme t V q (k.appTop r) = strictLocalGerm X.scheme t U p r := by
  sorry

end AlgebraicGeometry
