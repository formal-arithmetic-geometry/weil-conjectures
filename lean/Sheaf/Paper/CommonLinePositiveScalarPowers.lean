/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionExistence
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionUniqueness
import Sheaf.Paper.ScalarExtensionBinaryCoherence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction

/-! # Common-line presentations and nonnegative powers under scalar extension

Source: main-20261015, prop-weil-twist-preserves.proof.md, first and last sentences;
Stacks Project, Modules on Sites, Tags 03EK and 03EL
(blueprint: lem-pur-common-line-positive-scalar-powers).

The existential package below specifies the ring, its actual underlying sheaf tensor,
the module tensor presentations, and every comparison on local pure tensors. In
particular it does not assume an unspecified tensor ring or choose data from an
uncharacterized existence assertion. Scalar-extension notation puts the scalar first.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uC vC u uI

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.CommonLine

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The recorded category of modules, with the commutative ring viewed as a ring.
Source: Stacks 03CY (blueprint: lem-pur-common-line-positive-scalar-powers). -/
abbrev Modules (R : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- The recorded restriction of scalars along a commutative ring sheaf map.
Source: Stacks 03CY (blueprint: lem-pur-common-line-positive-scalar-powers). -/
abbrev restrict {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) : Modules S ⥤ Modules R :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)

/-- The algebra sheaf regarded as a module over its base, using its regular module.
Source: Stacks 03CY (blueprint: lem-pur-common-line-positive-scalar-powers). -/
abbrev regular {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) : Modules R :=
  (restrict a).obj (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))

/-- The existing sheaf tensor; its local tensors are `siteSheafTensorTmul`.
Source: Stacks 03EK (blueprint: lem-pur-common-line-positive-scalar-powers). -/
abbrev tensor {R : Sheaf J CommRingCat.{u}} (M N : Modules R) : Modules R :=
  (siteSheafTensorRight N).obj M

/-- The power of a local section, with one in degree zero and left association.
Source: Stacks 03EK (blueprint: lem-pur-common-line-positive-scalar-powers). -/
def sectionPower {R : Sheaf J CommRingCat.{u}} (M : Modules R) (U : Cᵒᵖ)
    (e : M.val.obj U) : (n : ℕ) → (scalarTensorPower R M n).val.obj U
  | 0 => @id (R.obj.obj U) 1
  | 1 => e
  | n + 2 => siteSheafTensorTmul (scalarTensorPower R M (n + 1)) M U
      (sectionPower M U e (n + 1)) e

attribute [local irreducible] changeOfRingsOfUniverses changeOfRingsHomOfUniverses
  scalarExtensionSection siteSheafTensorTmul siteSheafTensorRight siteSheafTensorSecondMap

/-- A presentation of the tensor ring by the actual sheafified module tensor.
The normalization identifies `a tensor c` with the product of the two ring maps.
It determines multiplication `(a tensor c)(a' tensor c') = aa' tensor cc'`
and the unit `1 tensor 1`, since both structure maps preserve multiplication and one.
Source: Stacks 03EK (blueprint: lem-pur-common-line-positive-scalar-powers). -/
structure Coefficients {B A D : Sheaf J CommRingCat.{u}} (a : B ⟶ A) (c : B ⟶ D) where
  ring : Sheaf J CommRingCat.{u}
  left : A ⟶ ring
  right : D ⟶ ring
  balance : a ≫ left = c ≫ right
  tensorIso : tensor (regular a) (regular c) ≅ regular (a ≫ left)
  tensor_tmul : ∀ (U : Cᵒᵖ) (x : A.obj.obj U) (y : D.obj.obj U),
    tensorIso.hom.val.app U (siteSheafTensorTmul (regular a) (regular c) U x y) =
      left.hom.app U x * right.hom.app U y

/-- The common presentation, for every module, with its prescribed inverse.
`underlying` identifies `line T` with the actual sheafified `T tensor_B D`;
`common` is the ring-linear isomorphism from `T tensor_A (A tensor_B D)`.
Source: Stacks 03EK and 03EL (blueprint: lem-pur-common-line-positive-scalar-powers). -/
structure Presentation {B A D : Sheaf J CommRingCat.{u}} {a : B ⟶ A} {c : B ⟶ D}
    (K : Coefficients a c) where
  line : Modules A → Modules K.ring
  underlying : ∀ T : Modules A,
    tensor ((restrict a).obj T) (regular c) ≅ (restrict (a ≫ K.left)).obj (line T)
  common : ∀ T : Modules A, changeOfRingsOfUniverses K.left T ≅ line T
  common_tmul : ∀ (T : Modules A) (U : Cᵒᵖ) (t : T.val.obj U)
      (x : A.obj.obj U) (y : D.obj.obj U),
    (common T).hom.val.app U
        (scalarExtensionSection K.left T U (K.left.hom.app U x * K.right.hom.app U y) t) =
      (underlying T).hom.val.app U
        (siteSheafTensorTmul ((restrict a).obj T) (regular c) U (x • t) y)
  inverse_tmul : ∀ (T : Modules A) (U : Cᵒᵖ) (t : T.val.obj U) (y : D.obj.obj U),
    (common T).inv.val.app U ((underlying T).hom.val.app U
        (siteSheafTensorTmul ((restrict a).obj T) (regular c) U t y)) =
      scalarExtensionSection K.left T U (K.right.hom.app U y) t
  naturality : ∀ (T T' : Modules A) (f : T ⟶ T'),
    (siteSheafTensorRight (regular c)).map ((restrict a).map f) ≫
        (underlying T').hom =
      (underlying T).hom ≫ (restrict (a ≫ K.left)).map
        ((common T).inv ≫ changeOfRingsHomOfUniverses K.left T f ≫ (common T').hom)

/-- The map induced on the common presentation by an A-linear map.
This conjugates the existing scalar-extension map by the normalized common isomorphisms.
Source: Stacks 03EK (blueprint: lem-pur-common-line-positive-scalar-powers). -/
def Presentation.map {B A D : Sheaf J CommRingCat.{u}} {a : B ⟶ A} {c : B ⟶ D}
    {K : Coefficients a c} (p : Presentation K) {T T' : Modules A} (f : T ⟶ T') :
    p.line T ⟶ p.line T' :=
  (p.common T).inv ≫ changeOfRingsHomOfUniverses K.left T f ≫ (p.common T').hom

/-- The complete normalized data asserted by the common-line lemma.
The degree-successor formula is the canonical relative tensor comparison followed
by the previous-degree map tensor the degree-one map. Its local formulas determine
it on sheafified tensors, without assuming that all sections are pure tensors.
Source: Stacks 03EK, 03EL (blueprint: lem-pur-common-line-positive-scalar-powers). -/
structure PositiveScalarPowers {B A D₀ D₁ : Sheaf J CommRingCat.{u}}
    (a : B ⟶ A) (c₀ : B ⟶ D₀) (c₁ : B ⟶ D₁)
    (φ : D₀ ⟶ D₁) (hφ : c₀ ≫ φ = c₁) where
  coefficients₀ : Coefficients a c₀
  coefficients₁ : Coefficients a c₁
  iota : coefficients₀.ring ⟶ coefficients₁.ring
  iota_left : coefficients₀.left ≫ iota = coefficients₁.left
  iota_right : coefficients₀.right ≫ iota = φ ≫ coefficients₁.right
  presentation₀ : Presentation coefficients₀
  presentation₁ : Presentation coefficients₁
  transition : ∀ T : Modules A,
    presentation₀.line T ⟶ (restrict iota).obj (presentation₁.line T)
  transition_tmul : ∀ (T : Modules A) (U : Cᵒᵖ) (t : T.val.obj U) (y : D₀.obj.obj U),
    (transition T).val.app U ((presentation₀.underlying T).hom.val.app U
        (siteSheafTensorTmul ((restrict a).obj T) (regular c₀) U t y)) =
      (presentation₁.underlying T).hom.val.app U
        (siteSheafTensorTmul ((restrict a).obj T) (regular c₁) U t (φ.hom.app U y))
  common_square : ∀ (T : Modules A) (U : Cᵒᵖ) (t : T.val.obj U)
      (r : coefficients₀.ring.obj.obj U),
    (transition T).val.app U ((presentation₀.common T).hom.val.app U
        (scalarExtensionSection coefficients₀.left T U r t)) =
      (presentation₁.common T).hom.val.app U
        (scalarExtensionSection coefficients₁.left T U (iota.hom.app U r) t)
  comparison : ∀ (T : Modules A) (n : ℕ),
    changeOfRingsOfUniverses iota
        (scalarTensorPower coefficients₀.ring (presentation₀.line T) n) ≅
      scalarTensorPower coefficients₁.ring (presentation₁.line T) n
  zero_tmul : ∀ (T : Modules A) (U : Cᵒᵖ)
      (r : coefficients₀.ring.obj.obj U) (s : coefficients₁.ring.obj.obj U),
    (comparison T 0).hom.val.app U
        (scalarExtensionSection iota
          (scalarTensorPower coefficients₀.ring (presentation₀.line T) 0) U s r) =
      iota.hom.app U r * s
  one_tmul : ∀ (T : Modules A) (U : Cᵒᵖ) (t : T.val.obj U)
      (r : coefficients₀.ring.obj.obj U) (s : coefficients₁.ring.obj.obj U),
    (comparison T 1).hom.val.app U
        (scalarExtensionSection iota (presentation₀.line T) U s
          ((presentation₀.common T).hom.val.app U
            (scalarExtensionSection coefficients₀.left T U r t))) =
      (presentation₁.common T).hom.val.app U
        (scalarExtensionSection coefficients₁.left T U (iota.hom.app U r * s) t)
  one_inverse : ∀ (T : Modules A) (U : Cᵒᵖ) (t : T.val.obj U)
      (s : coefficients₁.ring.obj.obj U),
    (comparison T 1).inv.val.app U ((presentation₁.common T).hom.val.app U
        (scalarExtensionSection coefficients₁.left T U s t)) =
      scalarExtensionSection iota (presentation₀.line T) U s
        ((presentation₀.common T).hom.val.app U
          (scalarExtensionSection coefficients₀.left T U 1 t))
  succ_tmul : ∀ (T : Modules A) (n : ℕ) (U : Cᵒᵖ)
      (x : (scalarTensorPower coefficients₀.ring (presentation₀.line T) (n + 1)).val.obj U)
      (y : (presentation₀.line T).val.obj U) (s : coefficients₁.ring.obj.obj U),
    (comparison T (n + 2)).hom.val.app U
        (scalarExtensionSection iota
          (scalarTensorPower coefficients₀.ring (presentation₀.line T) (n + 2)) U s
          (siteSheafTensorTmul
            (scalarTensorPower coefficients₀.ring (presentation₀.line T) (n + 1))
            (presentation₀.line T) U x y)) =
      siteSheafTensorTmul
        (scalarTensorPower coefficients₁.ring (presentation₁.line T) (n + 1))
        (presentation₁.line T) U
        ((comparison T (n + 1)).hom.val.app U
          (scalarExtensionSection iota
            (scalarTensorPower coefficients₀.ring (presentation₀.line T) (n + 1)) U s x))
        ((comparison T 1).hom.val.app U
          (scalarExtensionSection iota (presentation₀.line T) U 1 y))
  naturality : ∀ (T T' : Modules A) (f : T ⟶ T') (n : ℕ),
    changeOfRingsHomOfUniverses iota
        (scalarTensorPower coefficients₀.ring (presentation₀.line T) n)
        (scalarTensorPowerMap coefficients₀.ring (presentation₀.map f) n) ≫
        (comparison T' n).hom =
      (comparison T n).hom ≫
        scalarTensorPowerMap coefficients₁.ring (presentation₁.map f) n
  same_cover : ∀ (T : Modules A) (I : Type uI) (U : I → C), J.CoversTop U →
    (∀ i : I, Nonempty (T.over (U i) ≅
      unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).over (U i)))) →
    ∀ (i : I) (n : ℕ),
      Nonempty ((scalarTensorPower coefficients₀.ring (presentation₀.line T) n).over (U i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          coefficients₀.ring).over (U i))) ∧
      Nonempty ((scalarTensorPower coefficients₁.ring (presentation₁.line T) n).over (U i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          coefficients₁.ring).over (U i)))
  generator_tmul : ∀ (T : Modules A) (U : C)
      (frame : unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).over U) ≅ T.over U)
      (V : Over U) (n : ℕ) (r : coefficients₀.ring.obj.obj (op V.left))
      (s : coefficients₁.ring.obj.obj (op V.left)),
    (comparison T n).hom.val.app (op V.left)
        (scalarExtensionSection iota
          (scalarTensorPower coefficients₀.ring (presentation₀.line T) n) (op V.left) s
          (r • sectionPower (presentation₀.line T) (op V.left)
            ((presentation₀.common T).hom.val.app (op V.left)
              (scalarExtensionSection coefficients₀.left T (op V.left) 1
                (frame.hom.val.app (op V) (@id (A.obj.obj (op V.left)) 1)))) n)) =
      (iota.hom.app (op V.left) r * s) •
        sectionPower (presentation₁.line T) (op V.left)
          ((presentation₁.common T).hom.val.app (op V.left)
            (scalarExtensionSection coefficients₁.left T (op V.left) 1
              (frame.hom.val.app (op V) (@id (A.obj.obj (op V.left)) 1)))) n

/-- Common-line tensor presentations and normalized scalar extension of every
nonnegative power, including rank one on the original covering.

Source: main-20261015, prop-weil-twist-preserves.proof.md, scalar-extension sentence
and final integral-coefficient sentence; Stacks 03EK, 03EL
(blueprint: lem-pur-common-line-positive-scalar-powers).

Proof: (1) Apply the sheaf tensor Hom/Bilin universal property
(lem-pc-sites-sheaf-tensor-bilinear-universal) and module sheafification
(def-weil-presheaf-modules-sheafification). For nested tensors, extend bilinear
formulas along both sheafification units, using
lem-pc-sites-module-sheafification-bilinear-extension-existence and its uniqueness
counterpart; equality is detected on presheaf pure tensors, not arbitrary sheaf sections.
(2) Give A tensor_B D its product aa' tensor cc', unit 1 tensor 1, and let it act
on T tensor_B D by (a tensor c)(t tensor d)=at tensor cd. Balancing and all ring
and module laws follow on pure tensors and descend by bilinear-extension uniqueness.
(3) The common presentation sends t tensor (a tensor c) to at tensor c; its inverse
sends t tensor c to t tensor (1 tensor c). The A and B balanced relations prove
well-definedness and ring-linearity. Both composites fix pure tensors.
(4) Coefficient change sends a tensor c to a tensor phi(c), so the common square
commutes. The degree-one comparison and its inverse are the displayed balanced
formulas, which fix pure tensors in both composites. These formulas also prove
naturality in T and every commuting diagram of coefficient algebra maps.
(5) Degree zero is multiplication with inverse s mapped to 1 tensor s. Apply
lem-sp-scalar-extension-binary-coherence to R0 to R1 and the factors P0(n), L0,
then apply b_n tensor b_1. Induct from degree one, using the left-associated powers
of def-pur-sheaf-tensor-product. Its pure-tensor formula is exactly succ_tmul.
(6) Restrict to each member of the given cover by
lem-sfb-localized-site-tensor-restriction. A frame e and its inverse coefficient
map identify L_i with R_i. Induct on n: coefficients in a tensor of two framed
lines multiply, with inverse sending v to v times the tensor of the frames.
This retains the original covering and includes the ring in degree zero.
(7) The generator formula is multiplication in degree zero and the degree-one
normalization in degree one. The binary comparison takes (x tensor y) tensor s
to (x tensor s) tensor (y tensor 1), proving the successor formula inductively.
Every operation and sheafification unit used commutes with restrictions; the slice
tensor comparison preserves the same local pure tensors. -/
theorem exists_positiveScalarPowers
    [HasFiniteLimits C] [EssentiallySmall.{u} C]
    (B A D₀ D₁ : Sheaf J CommRingCat.{u}) (a : B ⟶ A)
    (c₀ : B ⟶ D₀) (c₁ : B ⟶ D₁) (φ : D₀ ⟶ D₁) (hφ : c₀ ≫ φ = c₁) :
    Nonempty (PositiveScalarPowers a c₀ c₁ φ hφ) := by
  sorry

/-- A coefficient map on the common presentations and all their powers.
Every component is a morphism of module sheaves after scalar restriction, normalized
in degree zero, degree one, and by the same left-associated recursion.
Source: Stacks 03EK (blueprint: lem-pur-common-line-positive-scalar-powers). -/
structure PresentationChange {B A D D' : Sheaf J CommRingCat.{u}}
    {a : B ⟶ A} {c : B ⟶ D} {c' : B ⟶ D'}
    {K : Coefficients a c} {K' : Coefficients a c'}
    (p : Presentation K) (p' : Presentation K') (β : D ⟶ D') where
  ringMap : K.ring ⟶ K'.ring
  left : K.left ≫ ringMap = K'.left
  right : K.right ≫ ringMap = β ≫ K'.right
  powerMap : ∀ (T : Modules A) (n : ℕ),
    scalarTensorPower K.ring (p.line T) n ⟶
      (restrict ringMap).obj (scalarTensorPower K'.ring (p'.line T) n)
  zero : ∀ (T : Modules A) (U : Cᵒᵖ) (r : K.ring.obj.obj U),
    (powerMap T 0).val.app U r = ringMap.hom.app U r
  one : ∀ (T : Modules A) (U : Cᵒᵖ) (t : T.val.obj U) (y : D.obj.obj U),
    (powerMap T 1).val.app U ((p.underlying T).hom.val.app U
        (siteSheafTensorTmul ((restrict a).obj T) (regular c) U t y)) =
      (p'.underlying T).hom.val.app U
        (siteSheafTensorTmul ((restrict a).obj T) (regular c') U t (β.hom.app U y))
  succ : ∀ (T : Modules A) (n : ℕ) (U : Cᵒᵖ)
      (x : (scalarTensorPower K.ring (p.line T) (n + 1)).val.obj U)
      (y : (p.line T).val.obj U),
    (powerMap T (n + 2)).val.app U
        (siteSheafTensorTmul (scalarTensorPower K.ring (p.line T) (n + 1))
          (p.line T) U x y) =
      siteSheafTensorTmul (scalarTensorPower K'.ring (p'.line T) (n + 1))
        (p'.line T) U ((powerMap T (n + 1)).val.app U x) ((powerMap T 1).val.app U y)

/-- Naturality in a commuting square of coefficient algebras, including the
induced map on the source of the base-change comparison.
Source: Stacks 03EK, 03EL (blueprint: lem-pur-common-line-positive-scalar-powers). -/
structure CoefficientNaturality {B A D₀ D₁ D₀' D₁' : Sheaf J CommRingCat.{u}}
    {a : B ⟶ A} {c₀ : B ⟶ D₀} {c₁ : B ⟶ D₁}
    {φ : D₀ ⟶ D₁} {hφ : c₀ ≫ φ = c₁}
    {c₀' : B ⟶ D₀'} {c₁' : B ⟶ D₁'}
    {φ' : D₀' ⟶ D₁'} {hφ' : c₀' ≫ φ' = c₁'}
    (p : PositiveScalarPowers.{uC, vC, u, uI} a c₀ c₁ φ hφ)
    (p' : PositiveScalarPowers.{uC, vC, u, uI} a c₀' c₁' φ' hφ')
    (β₀ : D₀ ⟶ D₀') (β₁ : D₁ ⟶ D₁') where
  source : PresentationChange p.presentation₀ p'.presentation₀ β₀
  target : PresentationChange p.presentation₁ p'.presentation₁ β₁
  ring_square : p.iota ≫ target.ringMap = source.ringMap ≫ p'.iota
  extensionMap : ∀ (T : Modules A) (n : ℕ),
    changeOfRingsOfUniverses p.iota
        (scalarTensorPower p.coefficients₀.ring (p.presentation₀.line T) n) ⟶
      (restrict target.ringMap).obj (changeOfRingsOfUniverses p'.iota
        (scalarTensorPower p'.coefficients₀.ring (p'.presentation₀.line T) n))
  extension_tmul : ∀ (T : Modules A) (n : ℕ) (U : Cᵒᵖ)
      (s : p.coefficients₁.ring.obj.obj U)
      (x : (scalarTensorPower p.coefficients₀.ring (p.presentation₀.line T) n).val.obj U),
    (extensionMap T n).val.app U
        (scalarExtensionSection p.iota
          (scalarTensorPower p.coefficients₀.ring (p.presentation₀.line T) n) U s x) =
      scalarExtensionSection p'.iota
        (scalarTensorPower p'.coefficients₀.ring (p'.presentation₀.line T) n) U
        (target.ringMap.hom.app U s) ((source.powerMap T n).val.app U x)
  square : ∀ (T : Modules A) (n : ℕ),
    extensionMap T n ≫ (restrict target.ringMap).map (p'.comparison T n).hom =
      (p.comparison T n).hom ≫ target.powerMap T n

/-- The common presentations and all base-change comparisons are natural in
commuting diagrams of coefficient algebra maps, with A and the common T fixed.

Source: Stacks 03EK, 03EL; main-20261015 prop-weil-twist-preserves.proof.md
(blueprint: lem-pur-common-line-positive-scalar-powers).
Proof: use the bilinear-extension existence and uniqueness nodes to sheafify
id_A tensor beta_i and id_T tensor beta_i. These are respectively ring maps and
semilinear module maps by their pure-tensor formulas. Define the maps on powers
by the ring map in degree zero, the module map in degree one, and tensoring the
previous map with the degree-one map thereafter. The extension map sends s tensor x
to beta_1(s) tensor beta_0(x), using the commuting coefficient square for balancing.
In degrees zero and one its square with b_n commutes by multiplication and the
common-presentation formulas. For higher degrees use the normalized binary
comparison of lem-sp-scalar-extension-binary-coherence, natural in both factors,
and induction. Equalities descend through sheafification by the bilinear-extension
uniqueness node, and all maps commute with restriction because they are sheaf maps. -/
theorem exists_coefficientNaturality
    {B A D₀ D₁ D₀' D₁' : Sheaf J CommRingCat.{u}}
    {a : B ⟶ A} {c₀ : B ⟶ D₀} {c₁ : B ⟶ D₁}
    {φ : D₀ ⟶ D₁} {hφ : c₀ ≫ φ = c₁}
    {c₀' : B ⟶ D₀'} {c₁' : B ⟶ D₁'}
    {φ' : D₀' ⟶ D₁'} {hφ' : c₀' ≫ φ' = c₁'}
    (p : PositiveScalarPowers.{uC, vC, u, uI} a c₀ c₁ φ hφ)
    (p' : PositiveScalarPowers.{uC, vC, u, uI} a c₀' c₁' φ' hφ')
    (β₀ : D₀ ⟶ D₀') (β₁ : D₁ ⟶ D₁')
    (h₀ : c₀ ≫ β₀ = c₀') (h₁ : c₁ ≫ β₁ = c₁')
    (hβ : φ ≫ β₁ = β₀ ≫ φ') : Nonempty (CoefficientNaturality p p' β₀ β₁) := by
  sorry

end SheafOfModules.CommonLine
