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
import Sheaf.Paper.ScalarExtensionBinaryCoherence

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

open scoped ChangeOfRings

set_option backward.isDefEq.respectTransparency false

attribute [local semireducible] siteSheafTensorRight changeOfRingsOfUniverses

private def regularMap {R S S' : Sheaf J CommRingCat.{u}}
    (c : R ⟶ S) (c' : R ⟶ S') (β : S ⟶ S') (h : c ≫ β = c') :
    regular c ⟶ regular c' where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (regular c).val.obj U) (Y := (regular c').val.obj U)
        { toFun := β.hom.app U
          map_add' := map_add _
          map_smul' := by
            intro r x
            change S.obj.obj U at x
            change β.hom.app U (c.hom.app U r * x) =
              c'.hom.app U r * β.hom.app U x
            rw [map_mul]
            have e := ConcreteCategory.congr_hom (congrArg (fun f : R ⟶ S' ↦ f.hom.app U) h) r
            change β.hom.app U (c.hom.app U r) = c'.hom.app U r at e
            rw [e] }
      naturality := by
        intro U V f
        ext x
        exact ConcreteCategory.congr_hom (β.hom.naturality f) x }

private def coefficientLinearMap
    {B A D D' : Sheaf J CommRingCat.{u}} {a : B ⟶ A}
    {c : B ⟶ D} {c' : B ⟶ D'} (K : Coefficients a c) (K' : Coefficients a c')
    (β : D ⟶ D') (h : c ≫ β = c') :
    regular (a ≫ K.left) ⟶ regular (a ≫ K'.left) :=
  K.tensorIso.inv ≫ siteSheafTensorSecondMap (regular a) (regularMap c c' β h) ≫
    K'.tensorIso.hom

private theorem coefficientLinearMap_tmul
    {B A D D' : Sheaf J CommRingCat.{u}} {a : B ⟶ A}
    {c : B ⟶ D} {c' : B ⟶ D'} (K : Coefficients a c) (K' : Coefficients a c')
    (β : D ⟶ D') (h : c ≫ β = c') (U : Cᵒᵖ) (x : A.obj.obj U) (y : D.obj.obj U) :
    (coefficientLinearMap K K' β h).val.app U (K.left.hom.app U x * K.right.hom.app U y) =
      K'.left.hom.app U x * K'.right.hom.app U (β.hom.app U y) := by
  rw [← K.tensor_tmul]
  change K'.tensorIso.hom.val.app U
    ((siteSheafTensorSecondMap (regular a) (regularMap c c' β h)).val.app U
      (K.tensorIso.inv.val.app U (K.tensorIso.hom.val.app U _))) = _
  have e := congrArg (fun f ↦ f.val.app U) K.tensorIso.hom_inv_id
  have ee := ConcreteCategory.congr_hom e
    (siteSheafTensorTmul (regular a) (regular c) U x y)
  change K.tensorIso.inv.val.app U (K.tensorIso.hom.val.app U _) =
    siteSheafTensorTmul (regular a) (regular c) U x y at ee
  rw [ee]
  change K'.tensorIso.hom.val.app U
    ((siteSheafTensorSecondMap (regular a) (regularMap c c' β h)).val.app U
      (siteSheafTensorTmul (regular a) (regular c) U x y)) = _
  rw [scalarTensor_second_tmul]
  exact K'.tensor_tmul U x (β.hom.app U y)

private def coefficientAddMap
    {B A D D' : Sheaf J CommRingCat.{u}} {a : B ⟶ A}
    {c : B ⟶ D} {c' : B ⟶ D'} (K : Coefficients a c) (K' : Coefficients a c')
    (β : D ⟶ D') (h : c ≫ β = c') (U : Cᵒᵖ) :
    K.ring.obj.obj U →+ K'.ring.obj.obj U where
  toFun := (coefficientLinearMap K K' β h).val.app U
  map_zero' := map_zero _
  map_add' := map_add _

private theorem coefficientAddMap_tmul
    {B A D D' : Sheaf J CommRingCat.{u}} {a : B ⟶ A}
    {c : B ⟶ D} {c' : B ⟶ D'} (K : Coefficients a c) (K' : Coefficients a c')
    (β : D ⟶ D') (h : c ≫ β = c') (U : Cᵒᵖ) (x : A.obj.obj U) (y : D.obj.obj U) :
    coefficientAddMap K K' β h U (K.left.hom.app U x * K.right.hom.app U y) =
      K'.left.hom.app U x * K'.right.hom.app U (β.hom.app U y) :=
  coefficientLinearMap_tmul K K' β h U x y

private def coefficientUnit {B A D : Sheaf J CommRingCat.{u}}
    {a : B ⟶ A} {c : B ⟶ D} (K : Coefficients a c) :
    siteTensorPresheaf (regular a).val (regular c).val ⟶ (regular (a ≫ K.left)).val :=
  scalarSheafificationUnit (siteTensorPresheaf (regular a).val (regular c).val) ≫
    K.tensorIso.hom.val

private theorem coefficientUnit_surjective {B A D : Sheaf J CommRingCat.{u}}
    {a : B ⟶ A} {c : B ⟶ D} (K : Coefficients a c) :
    PresheafOfModules.IsLocallySurjective J (coefficientUnit K) := by
  have hunit : PresheafOfModules.IsLocallySurjective J
      (scalarSheafificationUnit (siteTensorPresheaf (regular a).val (regular c).val)) :=
    scalarSheafificationUnit_locallySurjective _
  have hiso : IsIso ((PresheafOfModules.toPresheaf _).map K.tensorIso.hom.val) := by
    change IsIso (((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).mapIso
      K.tensorIso).hom)
    infer_instance
  dsimp only [coefficientUnit, PresheafOfModules.IsLocallySurjective]
  rw [Functor.map_comp]
  exact @Presheaf.isLocallySurjective_comp _ _ J _ _ _ _ _ _ _ _ _ _ _ hunit
    (@Presheaf.isLocallySurjective_of_iso _ _ J _ _ _ _ _ _ _ _ _ hiso)

private theorem coefficientUnit_tmul {B A D : Sheaf J CommRingCat.{u}}
    {a : B ⟶ A} {c : B ⟶ D} (K : Coefficients a c) (U : Cᵒᵖ)
    (x : A.obj.obj U) (y : D.obj.obj U) :
    (coefficientUnit K).app U (x ⊗ₜ[B.obj.obj U] y) =
      K.left.hom.app U x * K.right.hom.app U y := by
  have he := K.tensor_tmul U x y
  unfold siteSheafTensorTmul at he
  exact he

private def coefficientSectionUnit {B A D : Sheaf J CommRingCat.{u}}
    {a : B ⟶ A} {c : B ⟶ D} (K : Coefficients a c) (U : Cᵒᵖ) :
    (siteTensorPresheaf (regular a).val (regular c).val).obj U →+ K.ring.obj.obj U where
  toFun := (coefficientUnit K).app U
  map_zero' := map_zero _
  map_add' := map_add _

private theorem coefficientSectionUnit_tmul {B A D : Sheaf J CommRingCat.{u}}
    {a : B ⟶ A} {c : B ⟶ D} (K : Coefficients a c) (U : Cᵒᵖ)
    (x : (regular a).val.obj U) (y : (regular c).val.obj U) :
    coefficientSectionUnit K U (x ⊗ₜ[B.obj.obj U] y) =
      K.left.hom.app U (show A.obj.obj U from x) *
        K.right.hom.app U (show D.obj.obj U from y) :=
  coefficientUnit_tmul K U x y

private def commonUnit {A R : Sheaf J CommRingCat.{u}} (α : A ⟶ R)
    (T : Modules A) {L : Modules R} (e : changeOfRingsOfUniverses α T ≅ L) :
    changeOfRingsPresheafOfUniverses α T ⟶ L.val :=
  scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α T) ≫ e.hom.val

private theorem commonUnit_surjective {A R : Sheaf J CommRingCat.{u}} (α : A ⟶ R)
    (T : Modules A) {L : Modules R} (e : changeOfRingsOfUniverses α T ≅ L) :
    PresheafOfModules.IsLocallySurjective J (commonUnit α T e) := by
  have hu : PresheafOfModules.IsLocallySurjective J
      (scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α T)) :=
    scalarSheafificationUnit_locallySurjective _
  have hi : IsIso ((PresheafOfModules.toPresheaf _).map e.hom.val) := by
    change IsIso (((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).mapIso e).hom)
    infer_instance
  dsimp only [commonUnit, PresheafOfModules.IsLocallySurjective]
  rw [Functor.map_comp]
  exact @Presheaf.isLocallySurjective_comp _ _ J _ _ _ _ _ _ _ _ _ _ _ hu
    (@Presheaf.isLocallySurjective_of_iso _ _ J _ _ _ _ _ _ _ _ _ hi)

private theorem commonUnit_tmul {A R : Sheaf J CommRingCat.{u}} (α : A ⟶ R)
    (T : Modules A) {L : Modules R} (e : changeOfRingsOfUniverses α T ≅ L)
    (U : Cᵒᵖ) (r : R.obj.obj U) (t : T.val.obj U) :
    (commonUnit α T e).app U (r ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] t) =
      e.hom.val.app U (scalarExtensionSection α T U r t) := by
  unfold commonUnit scalarSheafificationUnit scalarExtensionSection
  rfl

attribute [local instance] coefficientUnit_surjective commonUnit_surjective

attribute [local irreducible] siteSheafTensorRight changeOfRingsOfUniverses
  coefficientLinearMap coefficientUnit commonUnit

private theorem coefficientAddMap_mul
    {B A D D' : Sheaf J CommRingCat.{u}} {a : B ⟶ A}
    {c : B ⟶ D} {c' : B ⟶ D'} (K : Coefficients a c) (K' : Coefficients a c')
    (β : D ⟶ D') (h : c ≫ β = c') (U : Cᵒᵖ) (z w : K.ring.obj.obj U) :
    (coefficientAddMap K K' β h U) (z * w) =
      coefficientAddMap K K' β h U z *
        coefficientAddMap K K' β h U w := by
  let f := coefficientAddMap K K' β h
  have raw (V : Cᵒᵖ)
      (x y : (siteTensorPresheaf (regular a).val (regular c).val).obj V) :
      f V ((coefficientSectionUnit K V x) *
        (coefficientSectionUnit K V y)) =
        f V (coefficientSectionUnit K V x) *
          f V (coefficientSectionUnit K V y) := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, zero_mul]
    | add x x' hx hx' => simp only [map_add, add_mul, hx, hx']
    | tmul a d =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, mul_zero]
      | add y y' hy hy' => simp only [map_add, mul_add, hy, hy']
      | tmul b e =>
        erw [coefficientSectionUnit_tmul K V a d, coefficientSectionUnit_tmul K V b e]
        change A.obj.obj V at a b
        change D.obj.obj V at d e
        have mul_tensor :
            K.left.hom.app V a * K.right.hom.app V d *
                (K.left.hom.app V b * K.right.hom.app V e) =
              K.left.hom.app V (a * b) * K.right.hom.app V (d * e) := by
          simp only [map_mul]
          ring
        rw [mul_tensor]
        dsimp only [f]
        rw [coefficientAddMap_tmul, coefficientAddMap_tmul,
          coefficientAddMap_tmul]
        simp only [map_mul]
        ring
  apply (regular (a ≫ K'.left)).isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map
      (coefficientUnit K)) z)
  intro V i hi
  obtain ⟨x, hx⟩ := hi
  change coefficientSectionUnit K (op V) x = K.ring.obj.map i.op z at hx
  have nat (W W' : Cᵒᵖ) (j : W ⟶ W') (t : K.ring.obj.obj W) :
      K'.ring.obj.map j (f W t) = f W' (K.ring.obj.map j t) :=
    (PresheafOfModules.naturality_apply (coefficientLinearMap K K' β h).val j t).symm
  change K'.ring.obj.map i.op (f U (z * w)) =
    K'.ring.obj.map i.op (f U z * f U w)
  rw [map_mul (K'.ring.obj.map i.op).hom, nat, nat, nat,
    map_mul (K.ring.obj.map i.op).hom, ← hx]
  apply (regular (a ≫ K'.left)).isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map
      (coefficientUnit K)) (K.ring.obj.map i.op w))
  intro W j hj
  obtain ⟨y, hy⟩ := hj
  change coefficientSectionUnit K (op W) y =
    K.ring.obj.map j.op (K.ring.obj.map i.op w) at hy
  change K'.ring.obj.map j.op
    (f (op V) (coefficientSectionUnit K (op V) x * K.ring.obj.map i.op w)) =
    K'.ring.obj.map j.op
      (f (op V) (coefficientSectionUnit K (op V) x) *
        f (op V) (K.ring.obj.map i.op w))
  rw [map_mul (K'.ring.obj.map j.op).hom, nat, nat, nat,
    map_mul (K.ring.obj.map j.op).hom, ← hy]
  have hn := (PresheafOfModules.naturality_apply (coefficientUnit K) j.op x).symm
  change K.ring.obj.map j.op (coefficientSectionUnit K (op V) x) =
    coefficientSectionUnit K (op W)
      ((siteTensorPresheaf (regular a).val (regular c).val).map j.op x) at hn
  rw [hn]
  exact raw _ _ _

private def coefficientMap
    {B A D D' : Sheaf J CommRingCat.{u}} {a : B ⟶ A}
    {c : B ⟶ D} {c' : B ⟶ D'} (K : Coefficients a c) (K' : Coefficients a c')
    (β : D ⟶ D') (h : c ≫ β = c') : K.ring ⟶ K'.ring where
  hom :=
    { app := fun U ↦ CommRingCat.ofHom
        { toFun := coefficientAddMap K K' β h U
          map_zero' := map_zero _
          map_add' := map_add _
          map_mul' := coefficientAddMap_mul K K' β h U
          map_one' := by
            simpa only [map_one, mul_one] using
              coefficientAddMap_tmul K K' β h U 1 1 }
      naturality := by
        intro U V i
        ext z
        exact PresheafOfModules.naturality_apply (coefficientLinearMap K K' β h).val i z }

private theorem coefficientMap_left
    {B A D D' : Sheaf J CommRingCat.{u}} {a : B ⟶ A}
    {c : B ⟶ D} {c' : B ⟶ D'} (K : Coefficients a c) (K' : Coefficients a c')
    (β : D ⟶ D') (h : c ≫ β = c') :
    K.left ≫ coefficientMap K K' β h = K'.left := by
  ext U x
  change (coefficientAddMap K K' β h U) (K.left.hom.app U x) = _
  simpa only [map_one, mul_one] using coefficientAddMap_tmul K K' β h U x 1

private theorem coefficientMap_right
    {B A D D' : Sheaf J CommRingCat.{u}} {a : B ⟶ A}
    {c : B ⟶ D} {c' : B ⟶ D'} (K : Coefficients a c) (K' : Coefficients a c')
    (β : D ⟶ D') (h : c ≫ β = c') :
    K.right ≫ coefficientMap K K' β h = β ≫ K'.right := by
  ext U y
  change (coefficientAddMap K K' β h U) (K.right.hom.app U y) =
    K'.right.hom.app U (β.hom.app U y)
  simpa only [map_one, one_mul] using coefficientAddMap_tmul K K' β h U 1 y

private theorem coefficient_ring_ext
    {B A D S : Sheaf J CommRingCat.{u}} {a : B ⟶ A} {c : B ⟶ D}
    (K : Coefficients a c) (f g : K.ring ⟶ S)
    (h : ∀ (U : Cᵒᵖ) (x : A.obj.obj U) (y : D.obj.obj U),
      f.hom.app U (K.left.hom.app U x * K.right.hom.app U y) =
        g.hom.app U (K.left.hom.app U x * K.right.hom.app U y)) : f = g := by
  ext U z
  apply (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)).isSheaf.isSeparated
    _ _ (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map
      (coefficientUnit K)) z)
  intro V i hi
  obtain ⟨t, ht⟩ := hi
  change coefficientSectionUnit K (op V) t = K.ring.obj.map i.op z at ht
  change S.obj.map i.op (f.hom.app U z) = S.obj.map i.op (g.hom.app U z)
  have hf := ConcreteCategory.congr_hom (f.hom.naturality i.op) z
  have hg := ConcreteCategory.congr_hom (g.hom.naturality i.op) z
  change f.hom.app (op V) (K.ring.obj.map i.op z) =
    S.obj.map i.op (f.hom.app U z) at hf
  change g.hom.app (op V) (K.ring.obj.map i.op z) =
    S.obj.map i.op (g.hom.app U z) at hg
  rw [← hf, ← hg]
  change f.hom.app (op V) (K.ring.obj.map i.op z) =
    g.hom.app (op V) (K.ring.obj.map i.op z)
  rw [← ht]
  clear ht
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    erw [coefficientSectionUnit_tmul K (op V) x y]
    exact h _ x y

private def coefficientExtension
    {A R S : Sheaf J CommRingCat.{u}}
    (α : A ⟶ R) (α' : A ⟶ S) (ρ : R ⟶ S) (h : α ≫ ρ = α') (T : Modules A) :
    changeOfRingsOfUniverses α T ⟶ (restrict ρ).obj (changeOfRingsOfUniverses α' T) :=
  scalarExtensionLift α T ((restrict ρ).obj (changeOfRingsOfUniverses α' T))
    { val :=
      { app := fun U ↦ ModuleCat.ofHom
          (X := T.val.obj U)
          (Y := ((restrict α).obj ((restrict ρ).obj
            (changeOfRingsOfUniverses α' T))).val.obj U)
          { toFun := fun t ↦ scalarExtensionSection α' T U 1 t
            map_add' := fun x y ↦ scalarExtensionSection_add α' T U 1 x y
            map_smul' := by
              intro r t
              have he := ConcreteCategory.congr_hom (congrArg (fun f : A ⟶ S ↦ f.hom.app U) h) r
              change ρ.hom.app U (α.hom.app U r) = α'.hom.app U r at he
              change scalarExtensionSection α' T U 1 (r • t) =
                ρ.hom.app U (α.hom.app U r) • scalarExtensionSection α' T U 1 t
              rw [he, scalarExtensionSection_base_smul, one_mul,
                scalarExtensionSection_smul, mul_one] }
        naturality := by
          intro U V i
          ext t
          change scalarExtensionSection α' T V 1 (T.val.map i t) =
            (changeOfRingsOfUniverses α' T).val.map i (scalarExtensionSection α' T U 1 t)
          rw [scalarExtensionSection_naturality, map_one] } }

private theorem coefficientExtension_tmul
    {A R S : Sheaf J CommRingCat.{u}}
    (α : A ⟶ R) (α' : A ⟶ S) (ρ : R ⟶ S) (h : α ≫ ρ = α') (T : Modules A)
    (U : Cᵒᵖ) (r : R.obj.obj U) (t : T.val.obj U) :
    (coefficientExtension α α' ρ h T).val.app U (scalarExtensionSection α T U r t) =
      scalarExtensionSection α' T U (ρ.hom.app U r) t := by
  rw [coefficientExtension, scalarExtensionLift_tmul]
  change ρ.hom.app U r • scalarExtensionSection α' T U 1 t = _
  rw [scalarExtensionSection_smul, mul_one]

private def scalarUnit {R S : Sheaf J CommRingCat.{u}} (ρ : R ⟶ S) (M : Modules R) :
    M ⟶ (restrict ρ).obj (changeOfRingsOfUniverses ρ M) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := M.val.obj U) (Y := ((restrict ρ).obj (changeOfRingsOfUniverses ρ M)).val.obj U)
        { toFun := fun x ↦ scalarExtensionSection ρ M U 1 x
          map_add' := fun x y ↦ scalarExtensionSection_add ρ M U 1 x y
          map_smul' := by
            intro r x
            change scalarExtensionSection ρ M U 1 (r • x) =
              ρ.hom.app U r • scalarExtensionSection ρ M U 1 x
            rw [scalarExtensionSection_base_smul, one_mul,
              scalarExtensionSection_smul, mul_one] }
      naturality := by
        intro U V i
        ext x
        change scalarExtensionSection ρ M V 1 (M.val.map i x) =
          (changeOfRingsOfUniverses ρ M).val.map i (scalarExtensionSection ρ M U 1 x)
        rw [scalarExtensionSection_naturality, map_one] }

private def semilinearTensorMap {R S : Sheaf J CommRingCat.{u}} (ρ : R ⟶ S)
    {M P : Modules R} {N Q : Modules S}
    (f : M ⟶ (restrict ρ).obj N) (g : P ⟶ (restrict ρ).obj Q) :
    tensor M P ⟶ (restrict ρ).obj (tensor N Q) :=
  scalarUnit ρ (tensor M P) ≫ (restrict ρ).map
    ((scalarTensorBinaryIso ρ M P).hom ≫
      (siteSheafTensorRight (changeOfRingsOfUniverses ρ P)).map
        (scalarExtensionLift ρ M N f) ≫
      siteSheafTensorSecondMap N (scalarExtensionLift ρ P Q g))

private theorem semilinearTensorMap_tmul {R S : Sheaf J CommRingCat.{u}} (ρ : R ⟶ S)
    {M P : Modules R} {N Q : Modules S}
    (f : M ⟶ (restrict ρ).obj N) (g : P ⟶ (restrict ρ).obj Q)
    (U : Cᵒᵖ) (x : M.val.obj U) (y : P.val.obj U) :
    (semilinearTensorMap ρ f g).val.app U (siteSheafTensorTmul M P U x y) =
      siteSheafTensorTmul N Q U (show N.val.obj U from f.val.app U x)
        (show Q.val.obj U from g.val.app U y) := by
  change (siteSheafTensorSecondMap N (scalarExtensionLift ρ P Q g)).val.app U
    (((siteSheafTensorRight (changeOfRingsOfUniverses ρ P)).map
      (scalarExtensionLift ρ M N f)).val.app U
      ((scalarTensorBinaryForward ρ M P).val.app U
        (scalarExtensionSection ρ (tensor M P) U 1 (siteSheafTensorTmul M P U x y)))) = _
  rw [scalarTensorBinaryForward_tmul, scalarTensor_first_tmul, scalarTensor_second_tmul,
    scalarExtensionLift_tmul, scalarExtensionLift_tmul, one_smul, one_smul]

private def presentationLineMap
    {B A D D' : Sheaf J CommRingCat.{u}} {a : B ⟶ A}
    {c : B ⟶ D} {c' : B ⟶ D'} {K : Coefficients a c} {K' : Coefficients a c'}
    (p : Presentation K) (p' : Presentation K') (β : D ⟶ D') (h : c ≫ β = c') :
    (T : Modules A) →
      (p.line T ⟶ (restrict (coefficientMap K K' β h)).obj (p'.line T)) := fun T ↦
  (p.common T).inv ≫
    coefficientExtension K.left K'.left (coefficientMap K K' β h)
      (coefficientMap_left K K' β h) T ≫
    (restrict (coefficientMap K K' β h)).map (p'.common T).hom

private theorem presentationLineMap_common
    {B A D D' : Sheaf J CommRingCat.{u}} {a : B ⟶ A}
    {c : B ⟶ D} {c' : B ⟶ D'} {K : Coefficients a c} {K' : Coefficients a c'}
    (p : Presentation K) (p' : Presentation K') (β : D ⟶ D') (h : c ≫ β = c')
    (T : Modules A) (U : Cᵒᵖ) (r : K.ring.obj.obj U) (t : T.val.obj U) :
    (presentationLineMap p p' β h T).val.app U
      ((p.common T).hom.val.app U (scalarExtensionSection K.left T U r t)) =
      (p'.common T).hom.val.app U
        (scalarExtensionSection K'.left T U ((coefficientMap K K' β h).hom.app U r) t) := by
  change (p'.common T).hom.val.app U
    ((coefficientExtension K.left K'.left (coefficientMap K K' β h)
      (coefficientMap_left K K' β h) T).val.app U
        ((p.common T).inv.val.app U ((p.common T).hom.val.app U _))) = _
  have he := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.val.app U) (p.common T).hom_inv_id)
      (scalarExtensionSection K.left T U r t)
  change (p.common T).inv.val.app U ((p.common T).hom.val.app U _) =
    scalarExtensionSection K.left T U r t at he
  rw [he, coefficientExtension_tmul]

private def presentationPowerMap
    {B A D D' : Sheaf J CommRingCat.{u}} {a : B ⟶ A}
    {c : B ⟶ D} {c' : B ⟶ D'} {K : Coefficients a c} {K' : Coefficients a c'}
    (p : Presentation K) (p' : Presentation K') (β : D ⟶ D') (h : c ≫ β = c')
    (T : Modules A) : (n : ℕ) →
    scalarTensorPower K.ring (p.line T) n ⟶
      (restrict (coefficientMap K K' β h)).obj (scalarTensorPower K'.ring (p'.line T) n)
  | 0 =>
    { val :=
      { app := fun U ↦ ModuleCat.ofHom
          (X := (scalarTensorPower K.ring (p.line T) 0).val.obj U)
          (Y := ((restrict (coefficientMap K K' β h)).obj
            (scalarTensorPower K'.ring (p'.line T) 0)).val.obj U)
          { toFun := (coefficientMap K K' β h).hom.app U
            map_add' := map_add _
            map_smul' := by
              intro r x
              change K.ring.obj.obj U at r x
              change (coefficientMap K K' β h).hom.app U (r * x) =
                (coefficientMap K K' β h).hom.app U r *
                  (coefficientMap K K' β h).hom.app U x
              exact map_mul _ r x }
        naturality := by
          intro U V i
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact ConcreteCategory.congr_hom ((coefficientMap K K' β h).hom.naturality i) x } }
  | 1 => presentationLineMap p p' β h T
  | n + 2 => semilinearTensorMap (coefficientMap K K' β h)
      (presentationPowerMap p p' β h T (n + 1)) (presentationLineMap p p' β h T)

private def presentationChange
    {B A D D' : Sheaf J CommRingCat.{u}} {a : B ⟶ A}
    {c : B ⟶ D} {c' : B ⟶ D'} {K : Coefficients a c} {K' : Coefficients a c'}
    (p : Presentation K) (p' : Presentation K') (β : D ⟶ D') (h : c ≫ β = c') :
    PresentationChange p p' β where
  ringMap := coefficientMap K K' β h
  left := coefficientMap_left K K' β h
  right := coefficientMap_right K K' β h
  powerMap := presentationPowerMap p p' β h
  zero _ _ _ := rfl
  one T U t y := by
    change (p'.common T).hom.val.app U
      ((coefficientExtension K.left K'.left (coefficientMap K K' β h)
        (coefficientMap_left K K' β h) T).val.app U
          ((p.common T).inv.val.app U ((p.underlying T).hom.val.app U _))) = _
    rw [p.inverse_tmul, coefficientExtension_tmul]
    have he := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app U) (coefficientMap_right K K' β h)) y
    change (coefficientMap K K' β h).hom.app U (K.right.hom.app U y) =
      K'.right.hom.app U (β.hom.app U y) at he
    rw [he]
    simpa only [map_one, one_mul, one_smul] using p'.common_tmul T U t 1 (β.hom.app U y)
  succ T n U x y := semilinearTensorMap_tmul _ _ _ U x y

private theorem presentationChange_common
    {B A D D' : Sheaf J CommRingCat.{u}} {a : B ⟶ A}
    {c : B ⟶ D} {c' : B ⟶ D'} {K : Coefficients a c} {K' : Coefficients a c'}
    (p : Presentation K) (p' : Presentation K') (β : D ⟶ D') (h : c ≫ β = c')
    (T : Modules A) (U : Cᵒᵖ) (r : K.ring.obj.obj U) (t : T.val.obj U) :
    ((presentationChange p p' β h).powerMap T 1).val.app U
      ((p.common T).hom.val.app U (scalarExtensionSection K.left T U r t)) =
      (p'.common T).hom.val.app U
        (scalarExtensionSection K'.left T U
          ((presentationChange p p' β h).ringMap.hom.app U r) t) :=
  presentationLineMap_common p p' β h T U r t

attribute [local irreducible] coefficientMap presentationLineMap presentationPowerMap
  presentationChange coefficientExtension semilinearTensorMap

private def squareExtension
    {R S R' S' : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (α' : R' ⟶ S') (ρ : R ⟶ R') (σ : S ⟶ S')
    (h : α ≫ σ = ρ ≫ α') {M : Modules R} {N : Modules R'}
    (f : M ⟶ (restrict ρ).obj N) :
    changeOfRingsOfUniverses α M ⟶ (restrict σ).obj (changeOfRingsOfUniverses α' N) :=
  scalarExtensionLift α M ((restrict σ).obj (changeOfRingsOfUniverses α' N))
    { val :=
      { app := fun U ↦ ModuleCat.ofHom
          (X := M.val.obj U)
          (Y := ((restrict α).obj ((restrict σ).obj
            (changeOfRingsOfUniverses α' N))).val.obj U)
          { toFun := fun x ↦ scalarExtensionSection α' N U 1 (f.val.app U x)
            map_add' := by
              intro x y
              rw [map_add, scalarExtensionSection_add]
            map_smul' := by
              intro r x
              have he := ConcreteCategory.congr_hom
                (congrArg (fun k : R ⟶ S' ↦ k.hom.app U) h) r
              change σ.hom.app U (α.hom.app U r) =
                α'.hom.app U (ρ.hom.app U r) at he
              change scalarExtensionSection α' N U 1 (f.val.app U (r • x)) =
                σ.hom.app U (α.hom.app U r) •
                  scalarExtensionSection α' N U 1 (f.val.app U x)
              rw [(f.val.app U).hom.map_smul]
              change scalarExtensionSection α' N U 1
                (ρ.hom.app U r • (show N.val.obj U from f.val.app U x)) = _
              rw [scalarExtensionSection_base_smul, one_mul, he,
                scalarExtensionSection_smul, mul_one] }
        naturality := by
          intro U V i
          ext x
          change scalarExtensionSection α' N V 1 (f.val.app V (M.val.map i x)) =
            (changeOfRingsOfUniverses α' N).val.map i
              (scalarExtensionSection α' N U 1 (f.val.app U x))
          rw [scalarExtensionSection_naturality, map_one,
            PresheafOfModules.naturality_apply f.val]
          rfl } }

private theorem squareExtension_tmul
    {R S R' S' : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (α' : R' ⟶ S') (ρ : R ⟶ R') (σ : S ⟶ S')
    (h : α ≫ σ = ρ ≫ α') {M : Modules R} {N : Modules R'}
    (f : M ⟶ (restrict ρ).obj N) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (squareExtension α α' ρ σ h f).val.app U (scalarExtensionSection α M U s x) =
      scalarExtensionSection α' N U (σ.hom.app U s) (f.val.app U x) := by
  rw [squareExtension, scalarExtensionLift_tmul]
  change σ.hom.app U s • scalarExtensionSection α' N U 1 (f.val.app U x) = _
  rw [scalarExtensionSection_smul, mul_one]

private theorem extension_common_ext
    {A R S : Sheaf J CommRingCat.{u}} (α : A ⟶ R) (ρ : R ⟶ S)
    (T : Modules A) (L : Modules R) (e : changeOfRingsOfUniverses α T ≅ L)
    {H : Modules S} (f g : changeOfRingsOfUniverses ρ L ⟶ H)
    (h : ∀ U s r t, f.val.app U
        (scalarExtensionSection ρ L U s (e.hom.val.app U
          (scalarExtensionSection α T U r t))) =
      g.val.app U (scalarExtensionSection ρ L U s (e.hom.val.app U
        (scalarExtensionSection α T U r t)))) : f = g := by
  apply scalarExtension_hom_ext ρ L
  intro U s z
  let η := commonUnit α T e
  apply H.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map η) z)
  intro V i hi
  obtain ⟨v, hv⟩ := hi
  change η.app (op V) v = L.val.map i.op z at hv
  change H.val.map i.op (f.val.app U _) = H.val.map i.op (g.val.app U _)
  rw [← PresheafOfModules.naturality_apply f.val,
    ← PresheafOfModules.naturality_apply g.val, scalarExtensionSection_naturality, ← hv]
  clear hv
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero, scalarExtensionSection_zero]
  | add v w hv hw => simp only [map_add, scalarExtensionSection_add, hv, hw]
  | tmul r t =>
    rw [show η.app (op V) (r ⊗ₜ[A.obj.obj (op V), (α.hom.app (op V)).hom] t) =
      e.hom.val.app (op V) (scalarExtensionSection α T (op V) r t) from
        commonUnit_tmul α T e (op V) r t]
    exact h (op V) (S.obj.map i.op s) r t

private theorem coefficientMap_formula
    {B A D D' : Sheaf J CommRingCat.{u}} {a : B ⟶ A}
    {c : B ⟶ D} {c' : B ⟶ D'} (K : Coefficients a c) (K' : Coefficients a c')
    (τ : K.ring ⟶ K'.ring) (β : D ⟶ D')
    (hl : K.left ≫ τ = K'.left) (hr : K.right ≫ τ = β ≫ K'.right)
    (U : Cᵒᵖ) (x : A.obj.obj U) (y : D.obj.obj U) :
    τ.hom.app U (K.left.hom.app U x * K.right.hom.app U y) =
      K'.left.hom.app U x * K'.right.hom.app U (β.hom.app U y) := by
  have hleft := ConcreteCategory.congr_hom
    (congrArg (fun k : A ⟶ K'.ring ↦ k.hom.app U) hl) x
  have hright := ConcreteCategory.congr_hom
    (congrArg (fun k : D ⟶ K'.ring ↦ k.hom.app U) hr) y
  change τ.hom.app U (K.left.hom.app U x) = K'.left.hom.app U x at hleft
  change τ.hom.app U (K.right.hom.app U y) =
    K'.right.hom.app U (β.hom.app U y) at hright
  rw [map_mul, hleft, hright]

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
  let q₀ := presentationChange p.presentation₀ p'.presentation₀ β₀ h₀
  let q₁ := presentationChange p.presentation₁ p'.presentation₁ β₁ h₁
  have ring_square : p.iota ≫ q₁.ringMap = q₀.ringMap ≫ p'.iota := by
    apply coefficient_ring_ext p.coefficients₀
    intro U x y
    change q₁.ringMap.hom.app U
      (p.iota.hom.app U (p.coefficients₀.left.hom.app U x *
        p.coefficients₀.right.hom.app U y)) =
      p'.iota.hom.app U (q₀.ringMap.hom.app U
        (p.coefficients₀.left.hom.app U x * p.coefficients₀.right.hom.app U y))
    rw [coefficientMap_formula _ _ p.iota φ p.iota_left p.iota_right,
      coefficientMap_formula _ _ q₁.ringMap β₁ q₁.left q₁.right,
      coefficientMap_formula _ _ q₀.ringMap β₀ q₀.left q₀.right,
      coefficientMap_formula _ _ p'.iota φ' p'.iota_left p'.iota_right]
    have he := ConcreteCategory.congr_hom
      (congrArg (fun k : D₀ ⟶ D₁' ↦ k.hom.app U) hβ) y
    change β₁.hom.app U (φ.hom.app U y) = φ'.hom.app U (β₀.hom.app U y) at he
    rw [he]
  let e (T : Modules A) (n : ℕ) :=
    squareExtension p.iota p'.iota q₀.ringMap q₁.ringMap ring_square (q₀.powerMap T n)
  have formula (T : Modules A) (n : ℕ) (U : Cᵒᵖ)
      (s : p.coefficients₁.ring.obj.obj U)
      (x : (scalarTensorPower p.coefficients₀.ring (p.presentation₀.line T) n).val.obj U) :
      (e T n).val.app U (scalarExtensionSection p.iota
        (scalarTensorPower p.coefficients₀.ring (p.presentation₀.line T) n) U s x) =
      scalarExtensionSection p'.iota
        (scalarTensorPower p'.coefficients₀.ring (p'.presentation₀.line T) n) U
        (q₁.ringMap.hom.app U s) ((q₀.powerMap T n).val.app U x) :=
    squareExtension_tmul _ _ _ _ _ _ U s x
  have hr (U : Cᵒᵖ) (r : p.coefficients₀.ring.obj.obj U) :
      q₁.ringMap.hom.app U (p.iota.hom.app U r) =
        p'.iota.hom.app U (q₀.ringMap.hom.app U r) := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun k : p.coefficients₀.ring ⟶ p'.coefficients₁.ring ↦
        k.hom.app U) ring_square) r
  have one_square (T : Modules A) :
      e T 1 ≫ (restrict q₁.ringMap).map (p'.comparison T 1).hom =
        (p.comparison T 1).hom ≫ q₁.powerMap T 1 := by
    apply extension_common_ext p.coefficients₀.left p.iota T
      (p.presentation₀.line T) (p.presentation₀.common T)
    intro U s r t
    change (p'.comparison T 1).hom.val.app U
      ((e T 1).val.app U (scalarExtensionSection p.iota (p.presentation₀.line T) U s
        ((p.presentation₀.common T).hom.val.app U
          (scalarExtensionSection p.coefficients₀.left T U r t)))) =
      (q₁.powerMap T 1).val.app U ((p.comparison T 1).hom.val.app U
        (scalarExtensionSection p.iota (p.presentation₀.line T) U s
          ((p.presentation₀.common T).hom.val.app U
            (scalarExtensionSection p.coefficients₀.left T U r t))))
    have hf := formula T 1 U s
      ((p.presentation₀.common T).hom.val.app U
        (scalarExtensionSection p.coefficients₀.left T U r t))
    dsimp only [scalarTensorPower] at hf
    erw [hf, presentationChange_common, p'.one_tmul, p.one_tmul,
      presentationChange_common, map_mul, hr]
  have square (T : Modules A) (n : ℕ) :
      e T n ≫ (restrict q₁.ringMap).map (p'.comparison T n).hom =
        (p.comparison T n).hom ≫ q₁.powerMap T n := by
    induction n using Nat.twoStepInduction with
    | zero =>
      apply scalarExtension_hom_ext p.iota
      intro U s r
      change (p'.comparison T 0).hom.val.app U
        ((e T 0).val.app U (scalarExtensionSection p.iota
          (scalarTensorPower p.coefficients₀.ring (p.presentation₀.line T) 0) U s r)) =
        (q₁.powerMap T 0).val.app U ((p.comparison T 0).hom.val.app U
          (scalarExtensionSection p.iota
            (scalarTensorPower p.coefficients₀.ring (p.presentation₀.line T) 0) U s r))
      rw [formula, q₀.zero, p'.zero_tmul, p.zero_tmul, q₁.zero, map_mul, hr]
    | one => exact one_square T
    | more n _ ih =>
      apply scalarExtension_tensor_hom_ext p.iota
        (scalarTensorPower p.coefficients₀.ring (p.presentation₀.line T) (n + 1))
        (p.presentation₀.line T)
      intro U s x y
      change (p'.comparison T (n + 2)).hom.val.app U
        ((e T (n + 2)).val.app U (scalarExtensionSection p.iota
          (scalarTensorPower p.coefficients₀.ring (p.presentation₀.line T) (n + 2)) U s
          (siteSheafTensorTmul _ _ U x y))) =
        (q₁.powerMap T (n + 2)).val.app U ((p.comparison T (n + 2)).hom.val.app U
          (scalarExtensionSection p.iota
            (scalarTensorPower p.coefficients₀.ring (p.presentation₀.line T) (n + 2)) U s
            (siteSheafTensorTmul _ _ U x y)))
      rw [formula, q₀.succ, p'.succ_tmul, p.succ_tmul, q₁.succ]
      have previous := ConcreteCategory.congr_hom
        (congrArg (fun f ↦ f.val.app U) ih)
          (scalarExtensionSection p.iota
            (scalarTensorPower p.coefficients₀.ring (p.presentation₀.line T) (n + 1)) U s x)
      have first := ConcreteCategory.congr_hom
        (congrArg (fun f ↦ f.val.app U) (one_square T))
          (scalarExtensionSection p.iota (p.presentation₀.line T) U 1 y)
      change (p'.comparison T (n + 1)).hom.val.app U
          ((e T (n + 1)).val.app U _) = _ at previous
      change (p'.comparison T 1).hom.val.app U ((e T 1).val.app U _) = _ at first
      rw [formula T (n + 1)] at previous
      have hf := formula T 1 U 1 y
      dsimp only [scalarTensorPower] at hf
      erw [hf] at first
      rw [map_one] at first
      exact congrArg₂ (siteSheafTensorTmul
        (scalarTensorPower p'.coefficients₁.ring (p'.presentation₁.line T) (n + 1))
        (p'.presentation₁.line T) U) previous first
  exact ⟨{ source := q₀
           target := q₁
           ring_square := ring_square
           extensionMap := e
           extension_tmul := formula
           square := square }⟩

end SheafOfModules.CommonLine
