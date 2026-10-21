/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Paper.ScalarExtensionDualTowerCore
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

/-! # Signed powers of lines: scalar, tensor and tower comparisons

Source: blueprint main-20261015, prop-weil-twist-preserves.proof.md, tensor-power/internal-Hom
and common-finite-stage sentences; Stacks Project, Tags 03EK, 04TT and 0GMX.
(blueprint: lem-pur-signed-line-scalar-tensor-tower)

The coefficient and module universe is `max uC vC u`, so slice internal Homs stay in that
universe without equating the site's object and morphism universes. The scalar-extension
API puts the scalar first: `scalarExtensionSection α M U s x` denotes `x tensor s` in the
right-scalar convention of the node. Normalizations below refer to actual sheafified tensors.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC u} RingCat.{max uC vC u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]

/-- The node's signed powers, with the existing tensor powers and slice sheaf Hom.
Source: blueprint prop-weil-twist-preserves.proof.md; Stacks 03EK and 04TT.
(blueprint: lem-pur-signed-line-scalar-tensor-tower) -/
noncomputable def signedLinePower {R : Sheaf J CommRingCat.{max uC vC u}}
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ℤ → ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  | .ofNat n => scalarTensorPower R L n
  | .negSucc n => homObj (scalarTensorPower R L (n + 1))
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

/-- Local signed basis normalization: a genuine basis after every restriction, positive
powers by tensors, and negative powers dual to the positive ones on every slice object.
Source: Stacks 03EK and 04TT, local rank-one coordinates.
(blueprint: lem-pur-signed-line-scalar-tensor-tower) -/
def SignedLineBasisPowers {R : Sheaf J CommRingCat.{max uC vC u}}
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ)
    (e : ∀ m : ℤ, (signedLinePower.{uC, vC, u} L m).val.obj U) : Prop :=
  (∀ (m : ℤ) (W : (Over U.unop)ᵒᵖ), Function.Bijective
    (fun r : R.obj.obj (op W.unop.left) =>
      r • (signedLinePower.{uC, vC, u} L m).val.map W.unop.hom.op (e m))) ∧
  e 0 = (1 : R.obj.obj U) ∧
  (∀ n : ℕ, e (.ofNat (n + 2)) =
    siteSheafTensorTmul (scalarTensorPower R L (n + 1)) L U (e (.ofNat (n + 1))) (e 1)) ∧
  (∀ (n : ℕ) (W : (Over U.unop)ᵒᵖ),
    (e (.negSucc n)).app W
      ((scalarTensorPower R L (n + 1)).val.map W.unop.hom.op (e (.ofNat (n + 1)))) =
      (1 : R.obj.obj (op W.unop.left)))

/-- Normalization of the signed extension of the given exponent-one comparison.
The negative formula is the actual dual map followed by precomposition with the inverse
positive comparison. Source: Stacks 0GMX and 03EK.
(blueprint: lem-pur-signed-line-scalar-tensor-tower) -/
def SignedLineComparisonNormalized
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
    {R S : Sheaf J CommRingCat.{max uC vC u}} (α : R ⟶ S)
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (b : changeOfRingsOfUniverses α L ≅ K)
    (B : ∀ m : ℤ, changeOfRingsOfUniverses α (signedLinePower.{uC, vC, u} L m) ≅
      signedLinePower.{uC, vC, u} K m) : Prop :=
  (B 0).hom = (scalarExtensionUnitIso α).hom ∧
  (B 1).hom = b.hom ∧
  (∀ (n : ℕ) (U : Cᵒᵖ) (s : S.obj.obj U)
    (x : (scalarTensorPower R L (n + 1)).val.obj U) (y : L.val.obj U),
    (B (.ofNat (n + 2))).hom.val.app U
        (scalarExtensionSection α (scalarTensorPower R L (n + 2)) U s
          (siteSheafTensorTmul (scalarTensorPower R L (n + 1)) L U x y)) =
      siteSheafTensorTmul (scalarTensorPower S K (n + 1)) K U
        ((B (.ofNat (n + 1))).hom.val.app U
          (scalarExtensionSection α (scalarTensorPower R L (n + 1)) U s x))
        (b.hom.val.app U (scalarExtensionSection α L U 1 y))) ∧
  (∀ n : ℕ, (B (.negSucc n)).hom =
    scalarExtensionDualMap α (scalarTensorPower R L (n + 1)) ≫
      homObjMap (B (.ofNat (n + 1))).inv
        (𝟙 (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))))

/-- The canonical multiplication is specified by its normalization on every local basis.
Its normalization determines the contraction map uniquely, including mixed signs.
Source: Stacks 03EK and 04TT, tensor associativity, symmetry and evaluation.
(blueprint: lem-pur-signed-line-scalar-tensor-tower) -/
def SignedLineProductNormalized {R : Sheaf J CommRingCat.{max uC vC u}}
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (μ : ∀ a b : ℤ, (siteSheafTensorRight (signedLinePower.{uC, vC, u} L b)).obj
      (signedLinePower.{uC, vC, u} L a) ≅
      signedLinePower.{uC, vC, u} L (a + b)) : Prop :=
  ∀ (U : Cᵒᵖ) (e : ∀ m : ℤ, (signedLinePower.{uC, vC, u} L m).val.obj U),
    SignedLineBasisPowers.{uC, vC, u} L U e → ∀ a b : ℤ,
      (μ a b).hom.val.app U
        (siteSheafTensorTmul (signedLinePower.{uC, vC, u} L a)
          (signedLinePower.{uC, vC, u} L b) U (e a) (e b)) =
      e (a + b)

variable [∀ X : C,
  (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]

/-- Every local basis has its uniquely normalized positive and dual powers.
Source: Stacks 03EK and 04TT, node proof step 2.
(blueprint: lem-pur-signed-line-scalar-tensor-tower)
Proof: tensor the basis recursively, starting at 1 in degree zero. On each slice the
negative basis functional sends r times the positive basis to r. These linear maps
commute with restriction, hence are sections of the recorded slice Hom. A functional
on a free line is determined by its value on the basis, proving uniqueness. -/
theorem existsUnique_signedLineBasisPowers [HasFiniteLimits C]
    {R : Sheaf J CommRingCat.{max uC vC u}}
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (e : L.val.obj U)
    (he : ∀ W : (Over U.unop)ᵒᵖ, Function.Bijective
      (fun r : R.obj.obj (op W.unop.left) => r • L.val.map W.unop.hom.op e)) :
    ∃! E : ∀ m : ℤ, (signedLinePower.{uC, vC, u} L m).val.obj U,
      SignedLineBasisPowers.{uC, vC, u} L U E ∧ E 1 = e := by
  sorry

/-- Dual scalar comparison on every positive power of a line is invertible.
Source: Stacks 0GMX, specialized using 04TT and 03EK; node proof steps 1, 2 and 4.
(blueprint: lem-pur-signed-line-scalar-tensor-tower)
Proof: restrict to a trivializing cover using localized tensor restriction. The canonical
dual map sends the dual tensor basis to the functional taking the extended basis to 1.
Its inverse sends h to h(e tensor 1) times the extended dual basis. On overlaps inverses
agree because v = v f w = w. Hom cover gluing yields a global inverse. This uses no
flatness and no enough-points hypothesis. -/
theorem signedLineDual_isIso [HasFiniteLimits C]
    {R S : Sheaf J CommRingCat.{max uC vC u}} (α : R ⟶ S)
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hL : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (L.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (X i))))
    (n : ℕ) : IsIso (scalarExtensionDualMap α (scalarTensorPower R L (n + 1))) := by
  sorry

/-- Existence of all signed comparison isomorphisms, with the precise evaluation and
local coordinate formulas. Source: Stacks 0GMX, 03EK and 04TT, node proof steps 1--5.
(blueprint: lem-pur-signed-line-scalar-tensor-tower)
Proof: start with the scalar unit and b. Iterate the normalized binary scalar comparison
and tensor b to obtain the positive maps. For negative degrees compose the dual comparison,
which is invertible by the preceding line argument, with precomposition by the inverse
positive map. Evaluation cancels this inverse and gives alpha(phi(x)) s t. In compatible
bases positive induction and the dual evaluation formula give alpha(r) s in every degree.
All equalities descend from the cover by Hom gluing. -/
theorem exists_signedLineComparison [HasFiniteLimits C]
    {R S : Sheaf J CommRingCat.{max uC vC u}} (α : R ⟶ S)
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (hL : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (L.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (X i))))
    (hK : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (K.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (X i))))
    (b : changeOfRingsOfUniverses α L ≅ K) :
    ∃ B : ∀ m : ℤ, changeOfRingsOfUniverses α (signedLinePower.{uC, vC, u} L m) ≅
      signedLinePower.{uC, vC, u} K m,
      SignedLineComparisonNormalized.{uC, vC, u} α L K b B ∧
      (∀ (n : ℕ) (U : Cᵒᵖ) (s t : S.obj.obj U)
        (φ : (signedLinePower.{uC, vC, u} L (.negSucc n)).val.obj U)
        (x : (scalarTensorPower R L (n + 1)).val.obj U),
        ((B (.negSucc n)).hom.val.app U
          (scalarExtensionSection α (signedLinePower.{uC, vC, u} L (.negSucc n)) U s φ)).app
            (op (Over.mk (𝟙 U.unop)))
              ((B (.ofNat (n + 1))).hom.val.app U
                (scalarExtensionSection α (scalarTensorPower R L (n + 1)) U t x)) =
        α.hom.app U (φ.app (op (Over.mk (𝟙 U.unop))) x) * s * t) ∧
      (∀ (U : Cᵒᵖ) (e : ∀ m : ℤ, (signedLinePower.{uC, vC, u} L m).val.obj U)
        (f : ∀ m : ℤ, (signedLinePower.{uC, vC, u} K m).val.obj U),
        SignedLineBasisPowers.{uC, vC, u} L U e → SignedLineBasisPowers.{uC, vC, u} K U f →
        b.hom.val.app U (scalarExtensionSection α L U 1 (e 1)) = f 1 →
        ∀ (m : ℤ) (r : R.obj.obj U) (s : S.obj.obj U),
          (B m).hom.val.app U
            (scalarExtensionSection α (signedLinePower.{uC, vC, u} L m) U s (r • e m)) =
            (α.hom.app U r * s) • f m) := by
  sorry

/-- Canonical multiplication on all signed powers, characterized on every local basis.
Source: Stacks 03EK and 04TT, node proof steps 1, 2, 6 and 7.
(blueprint: lem-pur-signed-line-scalar-tensor-tower)
Proof: locally send (r e^a) tensor (q e^b) to rq e^(a+b); its inverse sends c e^(a+b)
to (c e^a) tensor e^b. Changing e to u e multiplies the degree m basis by u^m, including
negative m since u is a unit. Thus both maps agree on overlaps and glue uniquely by Hom
cover gluing. To identify this with associativity, symmetry and evaluation contractions,
identify the tensor of n duals with the dual of the nth tensor power by the product of
evaluations. In a mixed-sign product contract min(|a|,|b|) opposite pairs; every pairing
of dual basis elements is 1. The resulting map has the same normalization, hence equals
this unique multiplication. Zero exponents are the respective unitors. -/
theorem existsUnique_signedLineProduct [HasFiniteLimits C]
    {R : Sheaf J CommRingCat.{max uC vC u}}
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hL : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (L.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (X i)))) :
    ∃! μ : ∀ a b : ℤ, (siteSheafTensorRight (signedLinePower.{uC, vC, u} L b)).obj
      (signedLinePower.{uC, vC, u} L a) ≅
      signedLinePower.{uC, vC, u} L (a + b),
      SignedLineProductNormalized.{uC, vC, u} L μ := by
  sorry

/-- The canonical signed multiplication commutes with scalar extension.
Source: Stacks 03EK and 04TT, node proof step 8.
(blueprint: lem-pur-signed-line-scalar-tensor-tower)
Proof: over a basis chart both routes on ((r e^a) tensor (q e^b)) tensor s give
alpha(rq) s times the target basis in degree a+b. On the other route the coefficient
is alpha(r) s alpha(q), equal by multiplicativity and commutativity. Pure tensors
and linearity detect equality locally, and uniqueness of gluing detects it globally. -/
theorem signedLineComparison_tensor [HasFiniteLimits C]
    {R S : Sheaf J CommRingCat.{max uC vC u}} (α : R ⟶ S)
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (hL : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (L.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (X i))))
    (hK : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (K.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (X i))))
    (b : changeOfRingsOfUniverses α L ≅ K)
    (B : ∀ m : ℤ, changeOfRingsOfUniverses α (signedLinePower.{uC, vC, u} L m) ≅
      signedLinePower.{uC, vC, u} K m)
    (hB : SignedLineComparisonNormalized.{uC, vC, u} α L K b B)
    (μ : ∀ a b : ℤ, (siteSheafTensorRight (signedLinePower.{uC, vC, u} L b)).obj
      (signedLinePower.{uC, vC, u} L a) ≅
      signedLinePower.{uC, vC, u} L (a + b))
    (ν : ∀ a b : ℤ, (siteSheafTensorRight (signedLinePower.{uC, vC, u} K b)).obj
      (signedLinePower.{uC, vC, u} K a) ≅
      signedLinePower.{uC, vC, u} K (a + b))
    (hμ : SignedLineProductNormalized.{uC, vC, u} L μ)
    (hν : SignedLineProductNormalized.{uC, vC, u} K ν)
    (a c : ℤ) :
    changeOfRingsHomOfUniverses α _ (μ a c).hom ≫ (B (a + c)).hom =
      (scalarTensorBinaryIso α (signedLinePower.{uC, vC, u} L a)
        (signedLinePower.{uC, vC, u} L c)).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α (signedLinePower.{uC, vC, u} L c))).map
          (B a).hom ≫ siteSheafTensorSecondMap (signedLinePower.{uC, vC, u} K a) (B c).hom ≫
            (ν a c).hom := by
  sorry

/-- The exponent-one tower condition implies the tower condition in every signed degree.
Source: Stacks 03EK, 04TT and 0GMX, node proof step 10.
(blueprint: lem-pur-signed-line-scalar-tensor-tower)
Proof: choose a local basis e0 and propagate it by b01 and b12. The exponent-one
hypothesis identifies the resulting e2 with b02(e0 tensor 1). Both routes in degree m
send ((r e0^m) tensor s) tensor t to alpha02(r) beta(s) t e2^m, since
beta(alpha01(r)s) = alpha02(r) beta(s). This works for all signed m by the established
local formula. The associator is the existing scalarExtensionTowerIso: its forward map
sends (x tensor s) tensor t to x tensor beta(s)t, and its inverse sends x tensor t to
(x tensor 1) tensor t, by the published pure-section formulas. These follow from the
two balanced tensor universal properties, and their composites fix pure tensors.
Linearity proves equality on each chart and Hom gluing proves it globally. -/
theorem signedLineComparison_tower [HasFiniteLimits C]
    {R S T : Sheaf J CommRingCat.{max uC vC u}} (α : R ⟶ S) (β : S ⟶ T)
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (N : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (hL : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (L.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (X i))))
    (hK : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (K.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (X i))))
    (hN : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (N.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj T).over (X i))))
    (b01 : changeOfRingsOfUniverses α L ≅ K)
    (b12 : changeOfRingsOfUniverses β K ≅ N)
    (b02 : changeOfRingsOfUniverses (α ≫ β) L ≅ N)
    (B01 : ∀ m : ℤ, changeOfRingsOfUniverses α (signedLinePower.{uC, vC, u} L m) ≅
      signedLinePower.{uC, vC, u} K m)
    (B12 : ∀ m : ℤ, changeOfRingsOfUniverses β (signedLinePower.{uC, vC, u} K m) ≅
      signedLinePower.{uC, vC, u} N m)
    (B02 : ∀ m : ℤ, changeOfRingsOfUniverses (α ≫ β) (signedLinePower.{uC, vC, u} L m) ≅
      signedLinePower.{uC, vC, u} N m)
    (h01 : SignedLineComparisonNormalized.{uC, vC, u} α L K b01 B01)
    (h12 : SignedLineComparisonNormalized.{uC, vC, u} β K N b12 B12)
    (h02 : SignedLineComparisonNormalized.{uC, vC, u} (α ≫ β) L N b02 B02)
    (hb : (scalarExtensionTowerIso.{uC, vC, max uC vC u, max uC vC u} α β L).hom ≫
      b02.hom = changeOfRingsHomOfUniverses β _ b01.hom ≫ b12.hom) :
    ∀ m : ℤ, (scalarExtensionTowerIso.{uC, vC, max uC vC u, max uC vC u} α β
      (signedLinePower.{uC, vC, u} L m)).hom ≫ (B02 m).hom =
      changeOfRingsHomOfUniverses β _ (B01 m).hom ≫ (B12 m).hom := by
  sorry

/-- Identity coefficient maps with multiplication in degree one give the tensor-unit
comparison in every signed degree, explicitly on arbitrary pure sections.
Source: Stacks 03EK and 04TT, node proof step 10.
(blueprint: lem-pur-signed-line-scalar-tensor-tower)
Proof: the given multiplication carries e tensor 1 to e on any basis chart. The local
formula in each signed degree is therefore (r e^m) tensor s mapped to rs e^m. This is
the unit comparison; pure tensors and cover gluing give equality on arbitrary sections. -/
theorem signedLineComparison_identity [HasFiniteLimits C]
    {R : Sheaf J CommRingCat.{max uC vC u}}
    (L : ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hL : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (L.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (X i))))
    (b : changeOfRingsOfUniverses (𝟙 R) L ≅ L)
    (hb : ∀ (U : Cᵒᵖ) (s : R.obj.obj U) (x : L.val.obj U),
      b.hom.val.app U (scalarExtensionSection (𝟙 R) L U s x) = s • x)
    (B : ∀ m : ℤ, changeOfRingsOfUniverses (𝟙 R) (signedLinePower.{uC, vC, u} L m) ≅
      signedLinePower.{uC, vC, u} L m)
    (hB : SignedLineComparisonNormalized.{uC, vC, u} (𝟙 R) L L b B) :
    ∀ (m : ℤ) (U : Cᵒᵖ) (s : R.obj.obj U) (x : (signedLinePower.{uC, vC, u} L m).val.obj U),
      (B m).hom.val.app U (scalarExtensionSection (𝟙 R) (signedLinePower.{uC, vC, u} L m) U s x) =
        s • x := by
  sorry

end SheafOfModules
