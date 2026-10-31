/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TraceFormulaCoefficientSetup
public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.FiniteTorStability
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-! # Geometric comparison data

Source: Weil blueprint, sec-trace-formula/sk-d-six, the five comparison-data bullets
(blueprint: def-trf-geometric-comparison-data).
The functors are the recorded intrinsic finite-coefficient operations. The exceptional
adjunction is supplied only on the full bounded constructible finite-Tor subcategories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The separated geometric part of the existing finite-type over category.
Source: sk-d-setup, geometric schemes (blueprint: def-trf-geometric-comparison-data). -/
abbrev TraceFormulaGeometricSpace (F : FiniteFieldDatum.{u}) :=
  ObjectProperty.FullSubcategory (fun X : SixFunctorSpace F ↦ IsSeparated X.obj.hom)

namespace TraceFormulaGeometricSpace

variable {F : FiniteFieldDatum.{u}}

/-- The inherited separatedness, not additional geometric data.
Source: sk-d-setup (blueprint: def-trf-geometric-comparison-data). -/
instance separated (X : TraceFormulaGeometricSpace F) : IsSeparated X.obj.obj.hom := X.property

/-- The inherited local finite-type condition.
Source: sk-d-setup (blueprint: def-trf-geometric-comparison-data). -/
instance locallyFiniteType (X : TraceFormulaGeometricSpace F) :
    LocallyOfFiniteType X.obj.obj.hom := X.obj.property.1

/-- The inherited quasi-compactness condition.
Source: sk-d-setup (blueprint: def-trf-geometric-comparison-data). -/
instance quasiCompact (X : TraceFormulaGeometricSpace F) :
    QuasiCompact X.obj.obj.hom := X.obj.property.2

/-- The base, with its identity structure morphism.
Source: def-trf-geometric-comparison-data, normalization clause
(blueprint: def-trf-geometric-comparison-data). -/
def point (F : FiniteFieldDatum.{u}) : TraceFormulaGeometricSpace F :=
  ⟨sixFunctorPoint F, inferInstanceAs (IsSeparated (𝟙 (Spec (.of F.k))))⟩

/-- The original structure map, regarded as a map of geometric schemes.
Source: def-trf-geometric-comparison-data, a_X (blueprint: def-trf-geometric-comparison-data). -/
def structureMap (X : TraceFormulaGeometricSpace F) : X ⟶ point F :=
  ObjectProperty.homMk (sixFunctorStructure X.obj)

/-- Separatedness follows by cancelling the structure map on the right.
Source: sk-d-setup and separated composition cancellation (blueprint: def-trf-geometric-compari
son-data). -/
instance separatedHom {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) :
    IsSeparated f.hom.hom.left :=
  have : IsSeparated (f.hom.hom.left ≫ Y.obj.obj.hom) :=
    f.hom.hom.w.symm ▸ X.property
  IsSeparated.of_comp f.hom.hom.left Y.obj.obj.hom

/-- Finite type follows by cancelling the structure map on the right.
Source: sk-d-setup and finite-type cancellation (blueprint: def-trf-geometric-comparison-data). -/
instance locallyFiniteTypeHom {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) :
    LocallyOfFiniteType f.hom.hom.left :=
  have : LocallyOfFiniteType (f.hom.hom.left ≫ Y.obj.obj.hom) :=
    f.hom.hom.w.symm ▸ X.obj.property.1
  locallyOfFiniteType_of_comp f.hom.hom.left Y.obj.obj.hom

/-- Quasi-compactness follows by cancellation over the separated target.
Source: sk-d-setup and quasi-compact cancellation (blueprint: def-trf-geometric-comparison-data). -/
instance quasiCompactHom {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) :
    QuasiCompact f.hom.hom.left :=
  have : QuasiCompact (f.hom.hom.left ≫ Y.obj.obj.hom) :=
    f.hom.hom.w.symm ▸ X.obj.property.2
  QuasiCompact.of_comp f.hom.hom.left Y.obj.obj.hom

/-- Every map has the compactification supplied by the geometric coefficient setup.
No second choice of compactification is made.
Source: sk-d-setup, chosen compactifications (blueprint: def-trf-geometric-comparison-data). -/
def compactification
    {l : ℕ} [Fact l.Prime] {hl : l ≠ F.p}
    {E : Type u} [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {n : ℕ} {hn : 1 ≤ n} (G : TraceFormulaCoefficientSetup F l hl E n hn)
    {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) :
    Compactification f.hom.hom.left :=
  letI := HasCompactification.of_over f.hom.hom
  G.val X.obj.obj Y.obj.obj f.hom.hom

end TraceFormulaGeometricSpace

namespace GeometricOperationPackage

variable (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ)

/-- The actual ambient uncompleted pro-etale derived category at level n+1.
Source: sk-d-setup, D(X,A) (blueprint: def-trf-geometric-comparison-data). -/
abbrev Ambient (X : TraceFormulaGeometricSpace F) :=
  proEtaleDerivedCategory X.obj.obj.left (Padic.coefficientExtensionRing l E (n + 1))

/-- The recorded coefficient predicate, without another constructibility notion.
Source: sk-d-setup, D^b_ctf (blueprint: def-trf-geometric-comparison-data). -/
abbrev domain (X : TraceFormulaGeometricSpace F) :=
  finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.obj.obj.left

/-- The actual full coefficient subcategory.
Source: sk-d-setup (blueprint: def-trf-geometric-comparison-data). -/
abbrev Ctf (X : TraceFormulaGeometricSpace F) := (domain F l E n X).FullSubcategory

/-- Ambient pullback is the recorded exact derived inverse image.
Source: sk-def-sf-operations (i) (blueprint: def-trf-geometric-comparison-data). -/
abbrev pull {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) :=
  finiteDerivedPullback l E n f.hom.hom.left

/-- Restrict the recorded pullback using the geometric coefficient requirement.
Source: sk-d-setup, pullback stability (blueprint: def-trf-geometric-comparison-data). -/
def pullCtf
    (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)))
    {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) : Ctf F l E n Y ⥤ Ctf F l E n X :=
  (domain F l E n X).lift ((domain F l E n Y).ι ⋙ pull F l E n f)
    (fun K ↦ G.property.2.1 X.obj.obj Y.obj.obj f.hom.hom K.obj K.property)

/-- The chosen compactification's actual ordinary support direct image.
Source: sk-d-setup and sk-def-sf-operations (iv) (blueprint: def-trf-geometric-comparison-data). -/
def support
    (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)))
    {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) :=
  sfIntrinsicCompactSupport (TraceFormulaGeometricSpace.compactification G f)
    (Padic.coefficientExtensionRing l E (n + 1))

/-- The restriction required by the given coefficient setup.
Source: sk-d-setup, support preservation (blueprint: def-trf-geometric-comparison-data). -/
def supportCtf
    (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)))
    {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) : Ctf F l E n X ⥤ Ctf F l E n Y :=
  letI := HasCompactification.of_over f.hom.hom
  (domain F l E n Y).lift ((domain F l E n X).ι ⋙ support F l hl E n G f)
    (fun K ↦ G.property.2.2 X.obj.obj Y.obj.obj f.hom.hom K.obj K.property)

/-- The actual comparison-defined exceptional functor, restricted to D^b_ctf.
Source: sk-def-sf-operations (vi), thm-sf-ctf-stability (v) (blueprint: def-trf-geometric-compa
rison-data). -/
def exceptionalCtf
    (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)))
    {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y)
    : Ctf F l E n Y ⥤ Ctf F l E n X :=
  sfStabilityFiniteExceptional F l hl E n X.obj.obj Y.obj.obj f.hom.hom
    (TraceFormulaGeometricSpace.compactification G f)

/-- The ordinary derived direct image restricted using the recorded stability theorem.
Source: sk-def-sf-operations (ii), thm-sf-ctf-stability (iii)
(blueprint: def-trf-geometric-comparison-data). -/
def directCtf {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) :
    Ctf F l E n X ⥤ Ctf F l E n Y :=
  (domain F l E n Y).lift ((domain F l E n X).ι ⋙
    proEtaleConstantDerivedDirectImage f.hom.hom.left
      (Padic.coefficientExtensionRing l E (n + 1)))
    (fun K ↦ (finiteTor_stability F l hl E n X.obj.obj Y.obj.obj f.hom.hom).2.2.2.1
      K.obj K.property |>.1)

/-- The actual ambient tensor, restricted to the two finite-Tor inputs.
Source: thm-sf-ctf-stability (ii) (blueprint: def-trf-geometric-comparison-data). -/
def tensorCtf (X : TraceFormulaGeometricSpace F) :
    Ctf F l E n X × Ctf F l E n X ⥤ Ctf F l E n X :=
  (domain F l E n X).lift
    (((domain F l E n X).ι.prod (domain F l E n X).ι) ⋙
      finiteIntrinsicDerivedTensor l E X.obj.obj.left n)
    (fun K ↦ ((finiteTor_stability F l hl E n X.obj.obj X.obj.obj (𝟙 _)).2.1
      K.1.obj K.2.obj K.1.property K.2.property).1)

/-- The canonical identity comparison on ambient pullback, descended termwise.
Source: the canonical given-functor identity in def-trf-geometric-comparison-data
(blueprint: def-trf-geometric-comparison-data). -/
def pullId (X : TraceFormulaGeometricSpace F) :
    pull F l E n (𝟙 X) ≅ 𝟭 (Ambient F l E n X) :=
  Functor.mapDerivedCategoryNatIso
    (sfIntrinsicPullbackId (Padic.coefficientExtensionRing l E (n + 1)) X.obj.obj.left) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The canonical pullback compositor descended from the ordinary inverse-image one.
Source: given-functor composition comparisons (blueprint: def-trf-geometric-comparison-data). -/
def pullComp {X Y Z : TraceFormulaGeometricSpace F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull F l E n (f ≫ g) ≅ pull F l E n g ⋙ pull F l E n f :=
  Functor.mapDerivedCategoryNatIso
    (sfIntrinsicPullbackComp (Padic.coefficientExtensionRing l E (n + 1))
      f.hom.hom.left g.hom.hom.left) ≪≫ Functor.mapDerivedCategoryCompIso _ _

/-- The fixed ambient monoidal structure used by the recorded tensor and internal Hom.
Source: sk-def-sf-operations (i) (blueprint: def-trf-geometric-comparison-data). -/
abbrev closed (X : TraceFormulaGeometricSpace F) :=
  finiteIntrinsicClosed l E X.obj.obj.left n

/-- Tensor objects in the fixed closed structure, with the structure explicit.
Source: sk-def-sf-operations (i) (blueprint: def-trf-geometric-comparison-data). -/
abbrev tensorObj (X : TraceFormulaGeometricSpace F) (K L : Ambient F l E n X) :=
  (closed F l E n X).tensor.obj (K, L)

/-- The actual derived coefficient unit, with its monoidal structure explicit.
Source: sk-def-sf-operations (i) (blueprint: def-trf-geometric-comparison-data). -/
abbrev unitObj (X : TraceFormulaGeometricSpace F) : Ambient F l E n X :=
  (closed F l E n X).monoidal.tensorUnit

/-- Strong monoidal data between the two fixed ambient tensor structures.
Source: strong monoidal pullback (blueprint: def-trf-geometric-comparison-data). -/
abbrev PullMonoidal {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) :=
  @Functor.CoreMonoidal (Ambient F l E n Y) _ (closed F l E n Y).monoidal
    (Ambient F l E n X) _ (closed F l E n X).monoidal (pull F l E n f)

/-- The unit comparison in the specified strong monoidal pullback.
Source: strong monoidal pullback (blueprint: def-trf-geometric-comparison-data). -/
def pullUnitIso {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y)
    (m : PullMonoidal F l E n f) :
    unitObj F l E n X ≅ (pull F l E n f).obj (unitObj F l E n Y) :=
  @Functor.CoreMonoidal.εIso (Ambient F l E n Y) _ (closed F l E n Y).monoidal
    (Ambient F l E n X) _ (closed F l E n X).monoidal (pull F l E n f) m

/-- The tensor comparison in the specified strong monoidal pullback.
Source: strong monoidal pullback (blueprint: def-trf-geometric-comparison-data). -/
def pullTensorIso {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y)
    (m : PullMonoidal F l E n f) (K L : Ambient F l E n Y) :
    tensorObj F l E n X ((pull F l E n f).obj K) ((pull F l E n f).obj L) ≅
      (pull F l E n f).obj (tensorObj F l E n Y K L) :=
  @Functor.CoreMonoidal.μIso (Ambient F l E n Y) _ (closed F l E n Y).monoidal
    (Ambient F l E n X) _ (closed F l E n X).monoidal (pull F l E n f) m K L

/-- The pullback/direct-image adjunction is the canonical derived one restricted
along the two full inclusions. Source: the given adjunction in def-trf-geometric-comparison-data
(blueprint: def-trf-geometric-comparison-data). -/
def pullDirectAdjunction
    (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)))
    {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) :
    pullCtf F l hl E n G f ⊣ directCtf F l hl E n f :=
  ((sfIntrinsicConstantModuleAdjunction f.hom.hom.left
    (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryRightDerivedAdjunction
      ).restrictFullyFaithful (domain F l E n Y).fullyFaithfulι
        (domain F l E n X).fullyFaithfulι (Iso.refl _) (Iso.refl _)

/-- The identity comparison restricted to the full coefficient category.
Source: def-trf-geometric-comparison-data, canonical identity convention
(blueprint: def-trf-geometric-comparison-data). -/
def pullCtfId
    (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))) (X : TraceFormulaGeometricSpace F) :
    pullCtf F l hl E n G (𝟙 X) ≅ 𝟭 (Ctf F l E n X) :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ ((pullId F l E n X).app K.obj))
    (fun f ↦ (domain F l E n X).fullyFaithfulι.map_injective
      ((pullId F l E n X).hom.naturality f.hom))

/-- Pullback composition restricted to the full coefficient categories.
Source: def-trf-geometric-comparison-data, canonical composition convention
(blueprint: def-trf-geometric-comparison-data). -/
def pullCtfComp
    (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)))
    {X Y Z : TraceFormulaGeometricSpace F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullCtf F l hl E n G (f ≫ g) ≅
      pullCtf F l hl E n G g ⋙ pullCtf F l hl E n G f :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ ((pullComp F l E n f g).app K.obj))
    (fun h ↦ (domain F l E n X).fullyFaithfulι.map_injective
      ((pullComp F l E n f g).hom.naturality h.hom))

/-- The canonical direct-image identity, uniquely obtained by adjunction.
Source: def-trf-geometric-comparison-data, proper comparison at the identity
(blueprint: def-trf-geometric-comparison-data). -/
def directId
    (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))) (X : TraceFormulaGeometricSpace F) :
    directCtf F l hl E n (𝟙 X) ≅ 𝟭 (Ctf F l E n X) :=
  (pullDirectAdjunction F l hl E n G (𝟙 X)).rightAdjointUniq
    (Adjunction.id.ofNatIsoLeft (pullCtfId F l hl E n G X).symm)

/-- The canonical direct-image compositor, the mate of pullback composition.
Source: def-trf-geometric-comparison-data, proper comparison coherence
(blueprint: def-trf-geometric-comparison-data). -/
def directComp
    (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)))
    {X Y Z : TraceFormulaGeometricSpace F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    directCtf F l hl E n (f ≫ g) ≅ directCtf F l hl E n f ⋙ directCtf F l hl E n g :=
  (pullDirectAdjunction F l hl E n G (f ≫ g)).rightAdjointUniq
    (((pullDirectAdjunction F l hl E n G g).comp
      (pullDirectAdjunction F l hl E n G f)).ofNatIsoLeft
        (pullCtfComp F l hl E n G f g).symm)

/-- An ordinary Cartesian square of geometric schemes over the fixed base.
The chosen identification is the dependency's ChosenCartesianSquare, rather than
an arbitrary commuting diagram. Source: def-trf-geometric-comparison-data, base change
(blueprint: def-trf-geometric-comparison-data). -/
structure Square where
  X : TraceFormulaGeometricSpace F
  Y : TraceFormulaGeometricSpace F
  X' : TraceFormulaGeometricSpace F
  Y' : TraceFormulaGeometricSpace F
  f : X ⟶ Y
  g : Y' ⟶ Y
  g' : X' ⟶ X
  f' : X' ⟶ Y'
  cartesian : ChosenCartesianSquare g'.hom.hom.left f'.hom.hom.left
    f.hom.hom.left g.hom.hom.left

variable
  (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)))

/-- The exceptional adjunctions are given on the full coefficient subcategories.
Their functors are the recorded ordinary support and transported etale exceptional
operations. Source: def-trf-geometric-comparison-data, initial adjunction convention
(blueprint: def-trf-geometric-comparison-data). -/
abbrev ExceptionalAdjunctions :=
  ∀ {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y),
    supportCtf F l hl E n G f ⊣ exceptionalCtf F l hl E n G f

/-- Comparison data on the given operations. Identity/composition comparisons of
right adjoints below are always their unique adjunction mates. Koszul symmetry
is normalized on the recorded K-flat tensor models, so it is not an arbitrary swap.
Source: def-trf-geometric-comparison-data, all five data bullets
(blueprint: def-trf-geometric-comparison-data). -/
structure Comparisons (A : ExceptionalAdjunctions F l hl E n G) where
  /-- The actual coefficient unit belongs to the specified coefficient subcategory. -/
  unitDomain : domain F l E n (TraceFormulaGeometricSpace.point F)
    (unitObj F l E n (TraceFormulaGeometricSpace.point F))
  /-- The dualizing complex is an object of the actual full coefficient category. -/
  omega : ∀ X : TraceFormulaGeometricSpace F, Ctf F l E n X
  /-- Identification with the given exceptional image of A at the base. -/
  dualizing : ∀ X : TraceFormulaGeometricSpace F,
    omega X ≅ (exceptionalCtf F l hl E n G (TraceFormulaGeometricSpace.structureMap X)).obj
      ⟨unitObj F l E n (TraceFormulaGeometricSpace.point F), unitDomain⟩
  /-- Normalization at the base. Its coherence equation is imposed below. -/
  normalization : omega (TraceFormulaGeometricSpace.point F) ≅
    ⟨unitObj F l E n (TraceFormulaGeometricSpace.point F), unitDomain⟩
  /-- Dualizing composition for every geometric map. -/
  dualizingComp : ∀ {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y),
    (exceptionalCtf F l hl E n G f).obj (omega Y) ≅ omega X
  /-- Proper support/direct-image comparison on the stated full subcategories. -/
  proper : ∀ {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y)
    [IsProper f.hom.hom.left], supportCtf F l hl E n G f ≅ directCtf F l hl E n f
  /-- Support composition, oriented towards the successive images. -/
  composition : ∀ {X Y Z : TraceFormulaGeometricSpace F} (f : X ⟶ Y) (g : Y ⟶ Z),
    supportCtf F l hl E n G (f ≫ g) ≅
      supportCtf F l hl E n G f ⋙ supportCtf F l hl E n G g
  /-- Support identity. -/
  identity : ∀ X : TraceFormulaGeometricSpace F,
    supportCtf F l hl E n G (𝟙 X) ≅ 𝟭 (Ctf F l E n X)
  /-- Cartesian base change on the coefficient subcategories. -/
  baseChange : ∀ Q : Square F,
    supportCtf F l hl E n G Q.f ⋙ pullCtf F l hl E n G Q.g ≅
      pullCtf F l hl E n G Q.g' ⋙ supportCtf F l hl E n G Q.f'
  /-- Projection formula on exactly the two stated finite-Tor inputs. -/
  projection : ∀ {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y)
    (K : Ctf F l E n X) (L : Ctf F l E n Y),
    tensorObj F l E n Y ((support F l hl E n G f).obj K.obj) L.obj ≅
      (support F l hl E n G f).obj
        (tensorObj F l E n X K.obj ((pull F l E n f).obj L.obj))
  /-- Naturality in the first projection-formula variable. -/
  projection_natural_left : ∀ {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y)
    {K K' : Ctf F l E n X} (k : K ⟶ K') (L : Ctf F l E n Y),
    (closed F l E n Y).tensor.map
      (Prod.mkHom ((support F l hl E n G f).map k.hom) (𝟙 L.obj)) ≫
        (projection f K' L).hom = (projection f K L).hom ≫
      (support F l hl E n G f).map ((closed F l E n X).tensor.map
        (Prod.mkHom k.hom (𝟙 ((pull F l E n f).obj L.obj))))
  /-- Naturality in the second projection-formula variable. -/
  projection_natural_right : ∀ {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y)
    (K : Ctf F l E n X) {L L' : Ctf F l E n Y} (k : L ⟶ L'),
    (closed F l E n Y).tensor.map
      (Prod.mkHom (𝟙 ((support F l hl E n G f).obj K.obj)) k.hom) ≫
        (projection f K L').hom = (projection f K L).hom ≫
      (support F l hl E n G f).map ((closed F l E n X).tensor.map
        (Prod.mkHom (𝟙 K.obj) ((pull F l E n f).map k.hom)))
  /-- Strong monoidal structure on the actual ambient derived pullback. -/
  monoidal : ∀ {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y),
    PullMonoidal F l E n f
  /-- The ambient derived categories carry their signed symmetric braiding. -/
  symmetric : ∀ X : TraceFormulaGeometricSpace F,
    @SymmetricCategory (Ambient F l E n X) _ (closed F l E n X).monoidal
  /-- The braiding is precisely the signed swap on K-flat representatives. -/
  koszul : ∀ X : TraceFormulaGeometricSpace F,
    RingedDerivedTensorSymmetryModel.{u+1, u, u}
      (ProEt.topology X.obj.obj.left) (integralCoefficientCommRingSheaf l E X.obj.obj.left n)
      (closed F l E n X) (finiteIntrinsicTensorModels l E X.obj.obj.left n) (symmetric X)
  /-- Pullback tensorators preserve those braidings. -/
  braided : ∀ {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y)
    (K L : Ambient F l E n Y),
    (pullTensorIso F l E n f (monoidal f) K L).hom ≫
      (pull F l E n f).map ((symmetric Y).braiding K L).hom =
      ((symmetric X).braiding ((pull F l E n f).obj K) ((pull F l E n f).obj L)).hom ≫
        (pullTensorIso F l E n f (monoidal f) L K).hom

end GeometricOperationPackage
end WeilConjectures
