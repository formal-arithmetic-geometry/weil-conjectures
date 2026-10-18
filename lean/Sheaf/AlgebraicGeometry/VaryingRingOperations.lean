/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Geometric operations for varying constant coefficient rings

Source: Stacks Project, Tags 03DI, 03DJ, 07A6, 09AE and 0F7B;
Zheng, Construction 4.1 (blueprint: def-sp-varying-ring-operations).

Systems and their ordinary unbounded derived categories are the existing sequence-site
module categories. Direct image is actual continuous module pushforward. Its left adjoint,
and open extension, are selected by their universal properties; all compositors are
unit-preserving adjoint comparisons.

## Main definitions

- `Modules`, `Derived`: the existing semilinear categories.
- `push`, `pull`, `extension`, `P`, `G`, `J`: actual ordinary and derived operations.
- `modulePComp`, `gComp`, `pComp`, `jComp`: normalized composition.
- `evalG`, `evalP`, `evalJ`: canonical coefficient evaluation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- The small pro-etale site fits the coefficient universe, retaining Hom universe u.
Source: Stacks 098K (blueprint: def-sp-varying-ring-operations). -/
instance siteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The vertical sequence site has the same smallness bound.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
instance sequenceSiteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} (ℕ × X.ProEt) :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- Ring-valued sheafification with all site and value universes fixed explicitly.
Source: Stacks 00W1 (blueprint: def-sp-varying-ring-operations). -/
instance ringSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  HasSmallSiteSheafify.hasSheafify_of_essentiallySmall.{u + 2, u, u, u + 1}
    CommRingCat.{u + 1} (Scheme.ProEt.topology X)

/-- Constant coefficient sheaves, with arbitrary commutative rings.
Source: Stacks 00YV (blueprint: def-sp-varying-ring-operations). -/
abbrev coefficients (X : Scheme.{u}) (n : ℕ) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj (R n)

/-- The actual adjacent ring-sheaf maps.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def coefficientTransition (X : Scheme.{u}) (n : ℕ) :
    coefficients R X (n + 1) ⟶ coefficients R X n :=
  (constantSheaf.{u, u + 1, u + 1, u + 2}
    (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (φ n)

/-- The already constructed module category on the vertical sequence site.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
abbrev Modules (X : Scheme.{u}) :=
  Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
    (coefficientTransition R φ X)

/-- Its ordinary unbounded derived category, with no cartesianness condition.
Source: Stacks 05RU (blueprint: def-sp-varying-ring-operations). -/
abbrev Derived (X : Scheme.{u}) :=
  DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X)

/-- The functor on sequence sites leaves the coefficient index unchanged.
Source: Stacks 09AE; Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def baseChange {X Y : Scheme.{u}} (f : X ⟶ Y) : ℕ × Y.ProEt ⥤ ℕ × X.ProEt :=
  (𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)

/-- Continuity on the vertical sequence topology.
Source: Stacks 09AE; Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: the inverse image of a vertical covering sieve is the base change of its
covering slice. Pro-etale base change preserves covering families. The horizontal
coordinate is unchanged, so the vertical-slice criterion proves continuity. -/
theorem baseChange_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (baseChange f).IsContinuous (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) := by
  sorry

attribute [instance] baseChange_continuous

/-- The coefficient structure map at a sequence-site object is the canonical map on
constant sections at that same index.
Source: Stacks 00YV, 09AE (blueprint: def-sp-varying-ring-operations). -/
def ringMapApp {X Y : Scheme.{u}} (f : X ⟶ Y) (U : (ℕ × Y.ProEt)ᵒᵖ) :
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj
        ((coefficients R Y U.unop.1).obj.obj (op U.unop.2)) ⟶
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj
        ((coefficients R X U.unop.1).obj.obj
          ((Scheme.proEtaleBaseChange f).op.obj (op U.unop.2))) :=
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
    ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} f CommRingCat.{u + 1} (R U.unop.1)).hom.app
      (op U.unop.2))

/-- Naturality includes the horizontal, possibly nonflat, coefficient maps.
Source: Stacks 00YV; Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: for vertical arrows use naturality of the constant-section map on the site;
for horizontal arrows use its naturality in the coefficient ring. Every product
arrow factors into these two arrows, giving the displayed naturality equation. -/
theorem ringMapApp_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : (ℕ × Y.ProEt)ᵒᵖ} (a : U ⟶ V) :
    (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) (coefficients R Y)
        (coefficientTransition R φ Y))).obj.map a ≫ ringMapApp R f V =
      ringMapApp R f U ≫
        (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
            (coefficientTransition R φ X))).obj.map ((baseChange f).op.map a) := by
  sorry

/-- The real ring-sheaf map defining direct image on semilinear systems.
Source: Stacks 03DA; Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def ringMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) (coefficients R Y)
          (coefficientTransition R φ Y)) ⟶
      ((baseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj
          (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology X))
            (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
              (coefficientTransition R φ X))) :=
  ⟨{ app := ringMapApp R f, naturality := fun _ _ a => ringMapApp_naturality R φ f a }⟩

/-- Direct image retains sections M_n(H ×_Y X) and their semilinear transitions.
Source: Stacks 03DA; Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def push {X Y : Scheme.{u}} (f : X ⟶ Y) : Modules R φ X ⥤ Modules R φ Y :=
  SheafOfModules.pushforward (ringMap R φ f)

/-- Existence of inverse image as the left adjoint of the actual section functor.
Source: Stacks 03EK; Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: form inverse image on the product site and extend scalars along ringMap.
Constant sheaves pull back to the same constants, compatibly with φ. Thus this
module pullback is the componentwise inverse image and has the usual adjunction. -/
theorem push_isRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (push R φ f).IsRightAdjoint := by
  sorry

attribute [instance] push_isRightAdjoint

/-- Inverse image selected by its universal property, not by a noncanonical map.
Source: Stacks 03EK (blueprint: def-sp-varying-ring-operations). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) := (push R φ f).leftAdjoint

/-- The universal-property adjunction fixes every subsequent mate and compositor.
Source: Stacks 03EK (blueprint: def-sp-varying-ring-operations). -/
def moduleAdj {X Y : Scheme.{u}} (f : X ⟶ Y) : pull R φ f ⊣ push R φ f :=
  Adjunction.ofIsRightAdjoint _

/-- Inverse image is additive and exact on all systems.
Source: Zheng 4.1; Stacks 03EK (blueprint: def-sp-varying-ring-operations).
Proof: the left adjoint is canonically the componentwise abelian inverse image.
Kernels and sheafified cokernels are componentwise; inverse image preserves both.
Addition is inherited from abelian inverse image. No flatness of φ is used. -/
theorem pull_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pull R φ f).Additive ∧ PreservesFiniteLimits (pull R φ f) ∧
      PreservesFiniteColimits (pull R φ f) := by
  sorry

/-- Direct image is additive on all section modules.
Source: Stacks 03DA (blueprint: def-sp-varying-ring-operations).
Proof: continuous module pushforward preserves the underlying maps and their
pointwise sums. Extensionality on all sections gives additivity. -/
theorem push_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (push R φ f).Additive := by
  sorry

attribute [instance] push_additive

/-- Additivity needed for the actual exact derived inverse image.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
instance pullAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) : (pull R φ f).Additive :=
  (pull_exact R φ f).1

/-- Left exactness of the actual inverse image.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
instance pullLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (pull R φ f) := (pull_exact R φ f).2.1

/-- Right exactness of the actual inverse image.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
instance pullColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (pull R φ f) := (pull_exact R φ f).2.2

/-- K-injective resolutions on the actual ringed sequence site.
Source: Stacks 079P; Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: the category is modules over systemRing on the small vertical sequence site.
Apply the recorded Grothendieck abelianness and K-injective resolution theorem to
that ringed site. This does not assert that evaluation preserves K-injectives. -/
theorem modules_kInjective (X : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (Modules R φ X) := by
  sorry

attribute [instance] modules_kInjective

/-- Exact inverse image on the ordinary derived system category.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
abbrev G {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived R φ Y ⥤ Derived R φ X :=
  (pull R φ f).mapDerivedCategory

/-- Total right derived direct image, computed on the system category itself.
Source: Stacks 079P (blueprint: def-sp-varying-ring-operations). -/
abbrev P {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived R φ X ⥤ Derived R φ Y :=
  (push R φ f).rightDerivedFunctor

/-- The canonical derived adjunction is induced from the ordinary one.
Source: Stacks 07A6 (blueprint: def-sp-varying-ring-operations). -/
def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : G R φ f ⊣ P R φ f :=
  (moduleAdj R φ f).mapDerivedCategoryRightDerivedAdjunction


/-- Ordinary direct-image composition is fixed on every section and coefficient index.
Source: Stacks 0D6D (blueprint: def-sp-varying-ring-operations).
Proof: restriction along the canonical fibre-product pasting isomorphism is linear,
natural in test objects, and compatible with every coefficient transition. Its
inverse is restriction along the inverse isomorphism. Sections determine uniqueness. -/
theorem modulePComp_existsUnique {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! d : push R φ f ⋙ push R φ g ≅ push R φ (f ≫ g),
      ∀ (N : Modules R φ X) (n : ℕ) (U : Z.ProEt)
        (x : ((push R φ f ⋙ push R φ g).obj N).val.obj (op (n, U))),
        (d.hom.app N).val.app (op (n, U)) x =
          N.val.map (Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackComp f g).hom.app U)).op x := by
  sorry

/-- The section-normalized compositor for ordinary direct image.
Source: Stacks 0D6D (blueprint: def-sp-varying-ring-operations). -/
def modulePComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (modulePComp_existsUnique R φ f g).choose

/-- Inverse-image composition is its unit-preserving conjugate.
Source: Stacks 0D6D (blueprint: def-sp-varying-ring-operations). -/
def moduleGComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull R φ (f ≫ g) ≅ pull R φ g ⋙ pull R φ f :=
  (Adjunction.leftAdjointCompIso (moduleAdj R φ g) (moduleAdj R φ f)
    (moduleAdj R φ (f ≫ g)) (modulePComp R φ f g)).symm

/-- Derived inverse-image composition is localized from the actual system comparison.
Source: Stacks 0D6D (blueprint: def-sp-varying-ring-operations). -/
def gComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    G R φ (f ≫ g) ≅ G R φ g ⋙ G R φ f :=
  Functor.mapDerivedCategoryNatIso (moduleGComp R φ f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Proper direct-image composition is the conjugate of inverse-image composition.
Source: Stacks 0D6D (blueprint: def-sp-varying-ring-operations). -/
def pComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P R φ f ⋙ P R φ g ≅ P R φ (f ≫ g) :=
  conjugateIsoEquiv ((adj R φ g).comp (adj R φ f)) (adj R φ (f ≫ g)) (gComp R φ f g)

/-- The identity comparison for ordinary direct image is the pullback graph map.
Source: Stacks 07A7 (blueprint: def-sp-varying-ring-operations).
Proof: restriction along the graph of the identity base change is a linear isomorphism
at every index. The inverse graph gives its inverse. These maps commute with the
semilinear transitions, and the section formula determines them uniquely. -/
theorem modulePId_existsUnique (X : Scheme.{u}) :
    ∃! d : push R φ (𝟙 X) ≅ 𝟭 (Modules R φ X),
      ∀ (N : Modules R φ X) (n : ℕ) (U : X.ProEt)
        (x : ((push R φ (𝟙 X)).obj N).val.obj (op (n, U))),
        (d.hom.app N).val.app (op (n, U)) x =
          N.val.map (Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U)).op x := by
  sorry

/-- The uniquely normalized ordinary identity comparison.
Source: Stacks 07A7 (blueprint: def-sp-varying-ring-operations). -/
def modulePId (X : Scheme.{u}) := (modulePId_existsUnique R φ X).choose

/-- The inverse-image identity is localized from the adjoint identity comparison.
Source: Stacks 07A7 (blueprint: def-sp-varying-ring-operations). -/
def gId (X : Scheme.{u}) : G R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  Functor.mapDerivedCategoryNatIso
    (Adjunction.leftAdjointIdIso (moduleAdj R φ (𝟙 X)) (modulePId R φ X)) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The right-adjoint identity is fixed by the same unit normalization.
Source: Stacks 07A7 (blueprint: def-sp-varying-ring-operations). -/
def pId (X : Scheme.{u}) : P R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  (conjugateIsoEquiv Adjunction.id (adj R φ (𝟙 X)) (gId R φ X)).symm

/-- Open restriction has the extension-by-zero left adjoint.
Source: Stacks 03DI, 09AE (blueprint: def-sp-varying-ring-operations).
Proof: localization identifies the open pro-etale site with the slice site. On each
coefficient level use localizedSystemExtension and localizedSystemAdjunction. Their
direct-sum lift formula commutes with φ, so the adjunction assembles on the actual
sequence site. It identifies its right adjoint with pull along the open immersion. -/
theorem pull_isRightAdjoint {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (pull R φ j).IsRightAdjoint := by
  sorry

attribute [instance] pull_isRightAdjoint

/-- Open extension chosen by the localized module universal property.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-operations). -/
abbrev extension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (pull R φ j).leftAdjoint

/-- The actual ordinary open-extension adjunction.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-operations). -/
def moduleJAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    extension R φ j ⊣ pull R φ j := Adjunction.ofIsRightAdjoint _

/-- Exactness of extension by zero, including the empty open.
Source: Stacks 03DJ (blueprint: def-sp-varying-ring-operations).
Proof: the localized direct-sum extension has at most one lift at every test object.
Its underlying abelian sheaf is exact extension by zero. Sheafification is exact,
and componentwise kernels and cokernels give exactness on systems. The canonical
unit-preserving comparison with the chosen left adjoint transfers this assertion. -/
theorem extension_exact {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (extension R φ j).Additive ∧ PreservesFiniteLimits (extension R φ j) ∧
      PreservesFiniteColimits (extension R φ j) := by
  sorry

/-- Additivity of extension by zero.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-operations). -/
instance extensionAdditive {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (extension R φ j).Additive := (extension_exact R φ j).1

/-- Left exactness of extension by zero.
Source: Stacks 03DJ (blueprint: def-sp-varying-ring-operations). -/
instance extensionLimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteLimits (extension R φ j) := (extension_exact R φ j).2.1

/-- Right exactness of extension by zero.
Source: Stacks 03DJ (blueprint: def-sp-varying-ring-operations). -/
instance extensionColimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteColimits (extension R φ j) := (extension_exact R φ j).2.2

/-- Exact extension on the ordinary derived category of systems.
Source: Stacks 03DJ (blueprint: def-sp-varying-ring-operations). -/
abbrev J {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (extension R φ j).mapDerivedCategory

/-- The derived open adjunction retains the ordinary units and counits.
Source: Stacks 03DI, 07A6 (blueprint: def-sp-varying-ring-operations). -/
def jAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : J R φ j ⊣ G R φ j :=
  Adjunction.ofNatIsoRight ((moduleJAdj R φ j).mapDerivedCategoryRightDerivedAdjunction)
    (pull R φ j).rightDerivedFunctorIsoMapDerivedCategory

/-- Ordinary open composition has the inverse-image composition as its conjugate.
Source: Stacks 03DI, 0F7D (blueprint: def-sp-varying-ring-operations). -/
def moduleJComp {U V X : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    extension R φ i ⋙ extension R φ j ≅ extension R φ (i ≫ j) :=
  Adjunction.leftAdjointCompIso (moduleJAdj R φ i) (moduleJAdj R φ j)
    (moduleJAdj R φ (i ≫ j)) (moduleGComp R φ i j).symm

/-- Derived open composition is localized from that ordinary comparison.
Source: Stacks 0F7D (blueprint: def-sp-varying-ring-operations). -/
def jComp {U V X : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] : J R φ i ⋙ J R φ j ≅ J R φ (i ≫ j) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleJComp R φ i j)

/-- Identity extension with its canonical adjoint normalization.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-operations). -/
def jId (X : Scheme.{u}) : J R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  Adjunction.leftAdjointIdIso (jAdj R φ (𝟙 X)) (gId R φ X)


/-- Exact ordinary evaluation of a semilinear system.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
abbrev eval (X : Scheme.{u}) (n : ℕ) :=
  SemilinearSections.evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients R X)
    (coefficientTransition R φ X) n

/-- Evaluation on the ordinary unbounded derived category.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
abbrev ev (X : Scheme.{u}) (n : ℕ) := (eval R φ X n).mapDerivedCategory

/-- Ordinary pushforward evaluation is identity on every section carrier.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: both sides have sections N_n(H ×_Y X), maps induced by the same restrictions,
and the same constant scalar map. The identity is linear and natural. Equality on
all sections proves uniqueness. -/
theorem moduleEvalP_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! d : push R φ f ⋙ eval R φ Y n ≅
        eval R φ X n ⋙ StrictTower.moduleDirectImage (R n) f,
      ∀ (N : Modules R φ X) (U : Y.ProEt)
        (x : ((push R φ f).obj N).val.obj (op (n, U))),
        (d.hom.app N).val.app (op U) x = x := by
  sorry

/-- The actual componentwise direct-image identification.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def moduleEvalP {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (moduleEvalP_existsUnique R φ f n).choose

/-- Inverse-image evaluation is uniquely fixed by the ordinary unit equation.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations).
Proof: the componentwise ordinary inverse-image adjunction identifies the left
adjoint with level inverse image. Its unit is the displayed system unit. The Hom
bijection forces the comparison uniquely, and inverse images of the same constant
rings make it invertible. This includes all semilinear transitions. -/
theorem moduleEvalG_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! d : pull R φ f ⋙ eval R φ X n ≅
        eval R φ Y n ⋙ StrictTower.modulePullback (R n) f,
      ∀ N : Modules R φ Y,
        (eval R φ Y n).map ((moduleAdj R φ f).unit.app N) ≫
          (moduleEvalP R φ f n).hom.app ((pull R φ f).obj N) ≫
          (StrictTower.moduleDirectImage (R n) f).map (d.hom.app N) =
        (Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
          (coefficients R X n) (StrictTower.constantRingIso (R n) f)).unit.app
            ((eval R φ Y n).obj N) := by
  sorry

/-- The normalized ordinary pullback evaluation comparison.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def moduleEvalG {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (moduleEvalG_existsUnique R φ f n).choose

/-- Derived evaluation is localization of the actual ordinary comparison.
Source: Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def evalG {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    G R φ f ⋙ ev R φ X n ≅
      ev R φ Y n ⋙ (StrictTower.modulePullback (R n) f).mapDerivedCategory :=
  letI : (StrictTower.modulePullback (R n) f).Additive :=
    StrictTower.modulePullback_additive (R n) f
  letI : PreservesFiniteLimits (StrictTower.modulePullback (R n) f) :=
    StrictTower.modulePullback_finiteLimits (R n) f
  letI : PreservesFiniteColimits (StrictTower.modulePullback (R n) f) :=
    StrictTower.modulePullback_finiteColimits (R n) f
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleEvalG R φ f n) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The ordinary exact-level adjunction, derived with its original unit.
Source: Stacks 07A6 (blueprint: def-sp-varying-ring-operations). -/
def levelAdj {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
    (coefficients R X n)
      (StrictTower.constantRingIso (R n) f)).mapDerivedCategoryRightDerivedAdjunction

/-- Evaluation of total direct image is the canonical mate, before inversion.
Source: Zheng 4.1, Lemma 4.10 (blueprint: def-sp-varying-ring-operations). -/
def evalPMate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    P R φ f ⋙ ev R φ Y n ⟶
      ev R φ X n ⋙ (StrictTower.moduleDirectImage (R n) f).rightDerivedFunctor :=
  mateEquiv (adj R φ f) (levelAdj R f n) (evalG R φ f n).inv

/-- The canonical direct-image evaluation mate is invertible on all systems.
Source: Zheng 4.10; semilinear derived sections (blueprint: def-sp-varying-ring-operations).
Proof: apply the simultaneous-section direct-image evaluation of
lem-coef-semilinear-derived-sections. Its ordinary realization is the same identity
on sections and its derived adjunction is the canonical ordinary-derived one.
The unit normalization therefore identifies its comparison with evalPMate. No
assertion that evaluated K-injectives are K-injective is used. -/
theorem evalPMate_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (evalPMate R φ f n) := by
  sorry

/-- The normalized derived direct-image evaluation.
Source: Zheng 4.10 (blueprint: def-sp-varying-ring-operations). -/
def evalP {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  @asIso _ _ _ _ (evalPMate R φ f n) (evalPMate_isIso R φ f n)

/-- The exact-level open-extension adjunction.
Source: Stacks 03DI, 07A6 (blueprint: def-sp-varying-ring-operations). -/
def levelJAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :=
  Adjunction.ofNatIsoRight
    ((StrictTower.moduleJAdj (R n) j).mapDerivedCategoryRightDerivedAdjunction)
      (StrictTower.modulePullback (R n) j).rightDerivedFunctorIsoMapDerivedCategory

/-- The open-extension evaluation comparison is fixed by the pullback comparison.
Source: Stacks 03DI; Zheng 4.1 (blueprint: def-sp-varying-ring-operations). -/
def evalJInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    ev R φ U n ⋙ (StrictTower.moduleJ (R n) j).mapDerivedCategory ⟶
      J R φ j ⋙ ev R φ X n :=
  (mateEquiv (jAdj R φ j) (levelJAdj R j n)).symm (evalG R φ j n).hom

/-- The open-extension mate is the localization of the coefficientwise lift map.
Source: Stacks 03DI, 03DJ (blueprint: def-sp-varying-ring-operations).
Proof: in the localized direct-sum extension each lift keeps its label and section.
Evaluation at n commutes with this presheaf and with sheafification. The resulting
ordinary isomorphism descends termwise, and its adjoint comparison is moduleEvalG,
so the derived mate is evalJInv. -/
theorem evalJInv_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    IsIso (evalJInv R φ j n) := by
  sorry

/-- Derived open evaluation with its specified unit normalization.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-operations). -/
def evalJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :=
  (@asIso _ _ _ _ (evalJInv R φ j n) (evalJInv_isIso R φ j n)).symm

end AlgebraicGeometry.ProEtale.VaryingRing
