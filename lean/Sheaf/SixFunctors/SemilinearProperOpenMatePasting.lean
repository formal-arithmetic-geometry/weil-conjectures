/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import all Sheaf.Paper.CoefficientRingedSequenceSite
import all Sheaf.Paper.SemilinearSystemModels
import all Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
import Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Intrinsic proper/open mates for semilinear coefficient systems

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D and 0F7F, open cases; blueprint
`fix-prop-coherence`, coefficient-system realization, step 2
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).

## Main definitions and statements

- `Modules`, `Derived`, `P`, `R`, `J`: the actual ordinary and derived system operations.
- `alpha`, `gamma`, `lambda`: the intrinsic clopen mate and its open restriction.
- `semilinearProperOpenMatePasting`: vertical, horizontal and base-change equations.
- `gamma_adjunct`, `gamma_identities`, `compositor_associativity`: normalization and coherence.
- `gamma_scalarRestriction`, `gamma_evaluation`, `gamma_finite`: coefficient comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

-- Compare the canonical constructions through their APIs, without unfolding their data.
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf

private theorem map_iso_transport
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y Z W : A} (a : X ≅ Y) (b : Z ≅ W) (f : X ⟶ Z) (g : Y ⟶ W)
    (h : f ≫ b.hom = a.hom ≫ g) {V : B} (c : V ⟶ F.obj Y) :
    c ≫ F.map a.inv ≫ F.map f ≫ F.map b.hom = c ≫ F.map g := by
  rw [← F.map_comp, h, F.map_comp, ← Category.assoc (F.map a.inv),
    ← F.map_comp, a.inv_hom_id, F.map_id, Category.id_comp]

private theorem chosen_unit_isIso_congr
    {A B : Type*} [Category A] [Category B] (F G : A ⥤ B)
    [F.IsRightAdjoint] [G.IsRightAdjoint] (h : F = G)
    (hi : IsIso (Adjunction.ofIsRightAdjoint G).unit) :
    IsIso (Adjunction.ofIsRightAdjoint F).unit := by
  subst G
  exact hi

private theorem exact_derived_congr
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (h : F = G) :
    F.mapDerivedCategory = G.mapDerivedCategory := by
  subst G
  rfl

private theorem right_derived_congr
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (h : F = G) :
    F.rightDerivedFunctor = G.rightDerivedFunctor := by
  subst G
  rfl

private def constant_diagram_square
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ E) (I : E ⥤ D)
    (e : F ⋙ G ≅ H ⋙ I) :
    F ⋙ (G ⋙ Functor.const ℕᵒᵖ) ≅
      (H ⋙ Functor.const ℕᵒᵖ) ⋙ (Functor.whiskeringRight ℕᵒᵖ E D).obj I :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents (fun _ ↦ e.app M) (by intros; simp))
    (by
      intro M N f
      apply NatTrans.ext
      funext n
      exact e.hom.naturality f)

private theorem mate_of_unit_normalization
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {R : B ⥤ A} {l : D ⥤ E} {r : E ⥤ D}
    (a : L ⊣ R) (b : l ⊣ r) (F : A ⥤ D) (G : B ⥤ E)
    (e : L ⋙ G ≅ F ⋙ l) (d : R ⋙ F ≅ G ⋙ r)
    (h : ∀ M : A, F.map (a.unit.app M) ≫ d.hom.app (L.obj M) ≫
      r.map (e.hom.app M) = b.unit.app (F.obj M)) :
    mateEquiv a b e.inv = d.hom := by
  apply mateEquiv_eq_of_unit a b _ _
  intro M
  have hh := congrArg (fun t ↦ t ≫ r.map (e.inv.app M)) (h M)
  simp only [Category.assoc, ← Functor.map_comp] at hh
  rw [e.hom_inv_id_app] at hh
  have hi : r.map (𝟙 ((L ⋙ G).obj M)) = 𝟙 _ := r.map_id _
  rw [hi] at hh
  erw [Category.comp_id] at hh
  exact hh

private theorem constant_diagram_mate
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {R : B ⥤ A} {l : D ⥤ E} {r : E ⥤ D}
    (a : L ⊣ R) (b : l ⊣ r) (F : A ⥤ D) (G : B ⥤ E)
    (e : L ⋙ G ≅ F ⋙ l) (d : R ⋙ F ≅ G ⋙ r)
    (h : ∀ M : A, F.map (a.unit.app M) ≫ d.hom.app (L.obj M) ≫
      r.map (e.hom.app M) = b.unit.app (F.obj M)) :
    mateEquiv a (b.whiskerRight ℕᵒᵖ) (constant_diagram_square L G F l e).inv =
      (constant_diagram_square R F G r d).hom := by
  apply mate_of_unit_normalization a (b.whiskerRight ℕᵒᵖ)
    (F ⋙ Functor.const ℕᵒᵖ) (G ⋙ Functor.const ℕᵒᵖ)
    (constant_diagram_square L G F l e) (constant_diagram_square R F G r d)
  intro M
  apply NatTrans.ext
  funext m
  simpa [constant_diagram_square] using h M

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

/-- Ring sheafification in the fixed coefficient universe, using the recorded transport.
Source: Stacks 00W1 (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
instance constantRingSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u + 1} X

/-- The original site is essentially small in the coefficient universe.
Source: the small-site convention
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
instance proEtSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The sequence site has the same fixed smallness universe.
Source: Zheng 4.1 (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
instance sequenceSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} (ℕ × X.ProEt) :=
  essentiallySmallSelf.{0, u, u + 1} _

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- The coefficient sheaves are the existing constant sheaves, at every level.
Source: Stacks 0F7B, coefficient-system extension
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
abbrev coefficients (X : Scheme.{u}) (n : ℕ) :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (ProEt.topology X) CommRingCat.{u + 1}).obj (C n)

/-- The given ring transitions, with no flatness condition.
Source: Stacks 0F7B, coefficient-system extension
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
abbrev transition (X : Scheme.{u}) (n : ℕ) :
    coefficients C X (n + 1) ⟶ coefficients C X n :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (ProEt.topology X) CommRingCat.{u + 1}).map (τ n)

/-- The actual ring on the vertical sequence site from the recorded section model.
Source: Zheng 4.1; Stacks 0F7B, coefficient-system extension
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
abbrev ringSystem (X : Scheme.{u}) :=
  systemRing.{u + 1, u, u + 1} (ProEt.topology X) (coefficients C X) (transition C τ X)

/-- Strict semilinear module systems, using the recorded ringed-site model.
Source: Zheng 4.1; Stacks 0F7B, coefficient-system extension
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
abbrev Modules (X : Scheme.{u}) :=
  Systems.{u + 1, u, u + 1} (ProEt.topology X) (coefficients C X) (transition C τ X)

/-- The standard derived-category instance at its specified localization size.
Source: Stacks 05RU (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
instance derived (X : Scheme.{u}) : HasDerivedCategory.{u + 2} (Modules C τ X) :=
  HasDerivedCategory.standard _

/-- Ordinary unbounded derived systems; this is not a diagram of derived categories.
Source: Zheng 4.1; Stacks 0F7B, coefficient-system extension
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
abbrev Derived (X : Scheme.{u}) :=
  DerivedCategory (Modules C τ X)

/-- Base change acts at the same index on the existing sequence site.
Source: Stacks 09A5 and 0F7B (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
abbrev siteMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (𝟭 ℕ).prod (proEtaleBaseChange f)

/-- Continuity on the vertical topology.
Source: Stacks 09A5 and Zheng 4.1
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: the inverse image of a vertical covering sieve is a vertical covering sieve,
by continuity of pro-etale base change. The index functor is the identity. -/
theorem siteMap_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (siteMap f).IsContinuous (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X)) := by
  exact VaryingRing.baseChange_continuous f

attribute [instance] siteMap_continuous

/-- The system coefficient map is uniquely fixed by the constant-section maps.
Source: Stacks 09A5 and 0F7B
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: at (n,U) use the canonical constant-section ring map at level n. Naturality
in U is its ordinary naturality; naturality in n is naturality in the ring C_n.
The vertical sheaf condition supplies a sheaf map. Components determine uniqueness. -/
theorem coefficientMap_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! a : ringSystem C τ Y ⟶ ((siteMap f).sheafPushforwardContinuous
      CommRingCat.{u + 1} (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj (ringSystem C τ X),
      ∀ (n : ℕ) (U : Y.ProEt), HEq (a.hom.app (op (n, U)))
        ((proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (C n)).hom.app (op U)) := by
  let a : ringSystem C τ Y ⟶ ((siteMap f).sheafPushforwardContinuous
      CommRingCat.{u + 1} (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj (ringSystem C τ X) :=
    ⟨{ app := fun U ↦
        (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (C U.unop.1)).hom.app
          (op U.unop.2)
       naturality := fun U V h ↦ by
        apply (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map_injective
        exact VaryingRing.ringMapApp_naturality C τ f h }⟩
  refine ⟨a, fun n U ↦ HEq.rfl, ?_⟩
  intro b hb
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact eq_of_heq (hb U.unop.1 U.unop.2)

/-- The unique componentwise constant-section structural ring map.
Source: Stacks 09A5 and 0F7B
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def coefficientMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (coefficientMap_existsUnique C τ f).choose

private theorem coefficientMap_forget_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (coefficientMap C τ f) = VaryingRing.ringMap C τ f := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact congrArg (fun a ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map a)
    (eq_of_heq ((coefficientMap_existsUnique C τ f).choose_spec.1 U.unop.1 U.unop.2))

/-- Actual module direct image on the ringed sequence site, including transitions.
Source: Stacks 03D7 and 0F7B
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def push {X Y : Scheme.{u}} (f : X ⟶ Y) : Modules C τ X ⥤ Modules C τ Y :=
  SheafOfModules.pushforward (F := siteMap f)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (coefficientMap C τ f))

private theorem push_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push C τ f = VaryingRing.push C τ f := by
  unfold push VaryingRing.push
  rw [coefficientMap_forget_eq]

/-- Sectionwise direct image is additive.
Source: Stacks 03D7 (blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: direct image keeps the additive maps of sections and restricts their scalar
actions. Addition of system morphisms is componentwise. -/
theorem push_additive {X Y : Scheme.{u}} (f : X ⟶ Y) : (push C τ f).Additive := by
  constructor
  intros M N f g
  ext U x
  rfl

attribute [instance] push_additive

/-- Inverse image is the left adjoint to the actual system direct image.
Source: Stacks 03D7; Zheng 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: use identified-coefficient inverse image at each level; naturality of the
constant-section comparisons gives the semilinear transitions. The componentwise
Hom bijections assemble into an adjunction on strict systems. -/
theorem push_isRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (push C τ f).IsRightAdjoint := by
  rw [push_eq]
  exact VaryingRing.push_isRightAdjoint C τ f

attribute [instance] push_isRightAdjoint

/-- The inverse image specified by its module-sheaf adjunction universal property.
Source: Stacks 03D7; Zheng 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) := (push C τ f).leftAdjoint

/-- The ordinary system adjunction; its unit and counit fix the mate normalization.
Source: Stacks 03D7; Zheng 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def ordinaryAdj {X Y : Scheme.{u}} (f : X ⟶ Y) : pull C τ f ⊣ push C τ f :=
  Adjunction.ofIsRightAdjoint _

private theorem pull_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull C τ f = VaryingRing.pull C τ f := by
  unfold pull VaryingRing.pull
  congr 1
  exact push_eq C τ f

/-- Inverse image is exact, since its coefficients are identified constant sheaves.
Source: Stacks 03EK; Zheng 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: the adjunction uniquely identifies pull with componentwise inverse image.
Kernels and cokernels of systems are componentwise. Each inverse image is exact;
no scalar extension along the transition C_(n+1) -> C_n is being assumed exact. -/
theorem pull_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pull C τ f).Additive ∧ PreservesFiniteLimits (pull C τ f) ∧
      PreservesFiniteColimits (pull C τ f) := by
  rw [pull_eq]
  exact VaryingRing.pull_exact C τ f


/-- Exact inverse-image additivity. Source: Stacks 03EK
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
instance pull_additive {X Y : Scheme.{u}} (f : X ⟶ Y) : (pull C τ f).Additive :=
  (pull_exact C τ f).1

/-- Left exact inverse image. Source: Stacks 03EK
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
instance pull_limits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (pull C τ f) := (pull_exact C τ f).2.1

/-- Right exact inverse image. Source: Stacks 03EK
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
instance pull_colimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (pull C τ f) := (pull_exact C τ f).2.2

/-- Simultaneous K-injectives exist on the ringed sequence site.
Source: Stacks 079P; Zheng 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: apply Grothendieck abelianness and K-injective resolutions to module sheaves
on the small ringed sequence site, not separately to its evaluated components. -/
theorem systems_kInjective (X : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (Modules C τ X) := by
  have := (Classical.choice (semilinearDerivedSections.{u + 1, u, u + 1}
    (ProEt.topology X) (coefficients C X) (transition C τ X))).systems.grothendieck
  exact Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian

attribute [instance] systems_kInjective

/-- Exact termwise inverse image on the ordinary derived category of systems.
Source: Zheng 4.10; Stacks 07A4
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def P {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived C τ Y ⥤ Derived C τ X :=
  (pull C τ f).mapDerivedCategory

/-- Total derived direct image on systems.
Source: Zheng 4.10; Stacks 07A4
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def R {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived C τ X ⥤ Derived C τ Y :=
  (push C τ f).rightDerivedFunctor

/-- The canonical derived adjunction of the actual ordinary system adjunction.
Source: Zheng 4.10; Stacks 07A4
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : P C τ f ⊣ R C τ f :=
  (ordinaryAdj C τ f).mapDerivedCategoryRightDerivedAdjunction


/-- The direct-image compositor is determined by restriction along fibre-product pasting.
Source: Stacks 03D8, 0D6D (blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: evaluate on (n,U). Both modules are sections over the two canonically isomorphic
iterated fibre products. Restriction along that isomorphism is linear and commutes
with semilinear transitions, and its inverse is restriction along the inverse.
All sections determine uniqueness. -/
theorem pushComp_existsUnique {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! d : push C τ f ⋙ push C τ g ≅ push C τ (f ≫ g),
      ∀ (N : Modules C τ X) (n : ℕ) (U : Z.ProEt)
        (x : ((push C τ f ⋙ push C τ g).obj N).val.obj (op (n, U))),
        (d.hom.app N).val.app (op (n, U)) x =
          N.val.map (Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackComp
              (P := @WeaklyEtale.{u}) (Q := ⊤) f g).hom.app U)).op x := by
  unfold push
  rw [coefficientMap_forget_eq, coefficientMap_forget_eq, coefficientMap_forget_eq]
  exact VaryingRing.modulePComp_existsUnique C τ f g

/-- The uniquely section-normalized ordinary direct-image compositor.
Source: Stacks 03D8, 0D6D (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def pushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (pushComp_existsUnique C τ f g).choose

/-- Inverse-image composition, conjugate to the specified sectionwise compositor.
Source: Stacks 07A7 (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def pullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull C τ (f ≫ g) ≅ pull C τ g ⋙ pull C τ f :=
  (Adjunction.leftAdjointCompIso (ordinaryAdj C τ g) (ordinaryAdj C τ f)
    (ordinaryAdj C τ (f ≫ g)) (pushComp C τ f g)).symm

/-- Derived pullback composition is the localization of the ordinary compositor.
Source: Zheng 4.10; Stacks 07A7 (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def pComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P C τ (f ≫ g) ≅ P C τ g ⋙ P C τ f :=
  Functor.mapDerivedCategoryNatIso (pullComp C τ f g) ≪≫
    Functor.mapDerivedCategoryCompIso (pull C τ g) (pull C τ f)

/-- Direct-image composition is precisely the mate of inverse-image composition.
Source: Stacks 07A7 (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def sComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    R C τ f ⋙ R C τ g ≅ R C τ (f ≫ g) :=
  conjugateIsoEquiv ((adj C τ g).comp (adj C τ f)) (adj C τ (f ≫ g)) (pComp C τ f g)

/-- The direct-image identity is fixed by restriction along the pullback identity.
Source: Stacks 07A7 (blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: restrict along the graph U -> U ×_X X at every level; its inverse gives the
inverse comparison, and sectionwise equality proves uniqueness. -/
theorem pushId_existsUnique (X : Scheme.{u}) :
    ∃! e : push C τ (𝟙 X) ≅ 𝟭 (Modules C τ X),
      ∀ (M : Modules C τ X) (n : ℕ) (U : X.ProEt)
        (x : ((push C τ (𝟙 X)).obj M).val.obj (op (n, U))),
        (e.hom.app M).val.app (op (n, U)) x =
          M.val.map (Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackId @WeaklyEtale.{u} ⊤ X).inv.app U)).op x := by
  unfold push
  rw [coefficientMap_forget_eq]
  exact VaryingRing.modulePId_existsUnique C τ X

/-- The unit-normalized inverse-image identity, localized from ordinary modules.
Source: Stacks 07A7 (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def pId (X : Scheme.{u}) : P C τ (𝟙 X) ≅ 𝟭 (Derived C τ X) :=
  Functor.mapDerivedCategoryNatIso (Adjunction.leftAdjointIdIso
    (ordinaryAdj C τ (𝟙 X)) (pushId_existsUnique C τ X).choose) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The derived direct-image identity is its adjunction conjugate.
Source: Stacks 07A7 (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def sId (X : Scheme.{u}) : R C τ (𝟙 X) ≅ 𝟭 (Derived C τ X) :=
  (conjugateIsoEquiv Adjunction.id (adj C τ (𝟙 X)) (pId C τ X)).symm

/-- Open inverse image is a right adjoint by localized-site extension by zero.
Source: Stacks 03DI, 03DJ (blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: use the direct-sum extension presheaf on the localized ringed sequence site,
then sheafify. The summand Hom correspondence is the extension/restriction adjunction.
The identified constant-ring inverse image is restriction on that localization. -/
theorem openPull_isRightAdjoint {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (pull C τ j).IsRightAdjoint := by
  rw [pull_eq]
  exact VaryingRing.pull_isRightAdjoint C τ j

attribute [instance] openPull_isRightAdjoint

/-- Ordinary extension by zero, specified by its localization universal property.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
abbrev extension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (pull C τ j).leftAdjoint

/-- The ordinary open adjunction, retaining its actual unit and counit.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def ordinaryOpenAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    extension C τ j ⊣ pull C τ j := Adjunction.ofIsRightAdjoint _

private theorem extension_eq {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    extension C τ j = VaryingRing.extension C τ j := by
  unfold extension VaryingRing.extension
  congr 1
  exact pull_eq C τ j

/-- Open extension is exact, also for the empty open.
Source: Stacks 03DI, 03DJ (blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: after localization its stalks are the original module on the open and zero
outside; equivalently its extension presheaf has at most one nonzero lift summand.
Sheafification is exact. This argument works at every index simultaneously. -/
theorem extension_exact {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (extension C τ j).Additive ∧ PreservesFiniteLimits (extension C τ j) ∧
      PreservesFiniteColimits (extension C τ j) := by
  rw [extension_eq]
  exact VaryingRing.extension_exact C τ j

/-- Additivity of open extension. Source: Stacks 03DI (blueprint:
lem-sf-semilinear-proper-open-mate-pasting). -/
instance extension_additive {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (extension C τ j).Additive := (extension_exact C τ j).1

/-- Left exactness of open extension. Source: Stacks 03DJ (blueprint:
lem-sf-semilinear-proper-open-mate-pasting). -/
instance extension_limits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteLimits (extension C τ j) := (extension_exact C τ j).2.1

/-- Right exactness of open extension. Source: Stacks 03DJ (blueprint:
lem-sf-semilinear-proper-open-mate-pasting). -/
instance extension_colimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteColimits (extension C τ j) := (extension_exact C τ j).2.2

/-- Exact extension by zero on ordinary derived systems.
Source: Stacks 03DI; Zheng 4.10 (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def J {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Derived C τ U ⥤ Derived C τ X :=
  (extension C τ j).mapDerivedCategory

/-- The open adjunction is the exact localization of the ordinary open adjunction.
Source: Stacks 03DI; Zheng 4.10 (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def jAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J C τ j ⊣ P C τ j :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (ordinaryOpenAdj C τ j)

/-- Canonical open-extension composition is adjoint to pullback composition.
Source: Stacks 0F7D (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def jComp {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] : J C τ j ⋙ J C τ k ≅ J C τ (j ≫ k) :=
  Adjunction.leftAdjointCompIso (jAdj C τ j) (jAdj C τ k) (jAdj C τ (j ≫ k))
    (pComp C τ j k).symm

/-- Equality transport respects proof-irrelevant open-immersion instances.
Source: Stacks 0F7D (blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: substitute the equality of the underlying arrows and use proof irrelevance. -/
theorem J_congr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) : J C τ f = J C τ g := by
  subst g
  rfl

/-- Open-extension transport along an equality of arrows.
Source: Stacks 0F7D (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def jCongr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) : J C τ f ≅ J C τ g :=
  eqToIso (J_congr C τ h)

/-- The canonical open-extension identity, adjoint to inverse-image identity.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def jId (X : Scheme.{u}) : J C τ (𝟙 X) ≅ 𝟭 (Derived C τ X) :=
  Adjunction.leftAdjointIdIso (jAdj C τ (𝟙 X)) (pId C τ X)

/-- Canonical comparison of the two iterated inverse images around any commutative square.
Source: Stacks, Tag 07A7 (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
noncomputable def squareP {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    P C τ i ⋙ P C τ r ≅ P C τ p ⋙ P C τ k :=
  (pComp C τ r i).symm ≪≫ eqToIso (congrArg (P C τ) h.symm) ≪≫ pComp C τ k p

/-- The inverse cartesian open comparison is defined by precisely the open-unit transpose.
Source: Stacks, Tags 09AE and 07A7
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
noncomputable def betaInvApp {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (M : Derived C τ U) :
    (J C τ j').obj ((P C τ gU).obj M) ⟶ (P C τ g).obj ((J C τ j).obj M) :=
  ((jAdj C τ j').homEquiv _ _).symm
    ((P C τ gU).map ((jAdj C τ j).unit.app M) ≫
      (squareP C τ gU j' j g h).inv.app ((J C τ j).obj M))

/-- Naturality of the specified open-unit transpose. Source: Stacks, Tag 09AE
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: use naturality of the open unit, the pullback compositor and the adjunction
Hom equivalence. The transposes of both sides are the same naturality square. -/
theorem betaInvApp_naturality {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (M N : Derived C τ U) (f : M ⟶ N) :
    (P C τ gU ⋙ J C τ j').map f ≫ betaInvApp C τ gU j' j g h N =
      betaInvApp C τ gU j' j g h M ≫ (J C τ j ⋙ P C τ g).map f := by
  dsimp only [betaInvApp, Functor.comp_map]
  let t := Functor.whiskerRight (jAdj C τ j).unit (P C τ gU) ≫
    Functor.whiskerLeft (J C τ j) (squareP C τ gU j' j g h).inv
  exact (jAdj C τ j').homEquiv_naturality_right_square
    ((P C τ gU).map f) (t.app N) (t.app M)
    ((J C τ j ⋙ P C τ g).map f) (t.naturality f)

/-- The inverse comparison as a natural transformation with the specified transpose.
Source: Stacks, Tag 09AE (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
noncomputable def betaInv {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g) :
    P C τ gU ⋙ J C τ j' ⟶ J C τ j ⋙ P C τ g where
  app := betaInvApp C τ gU j' j g h
  naturality := betaInvApp_naturality C τ gU j' j g h

private theorem P_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P C τ f = VaryingRing.G C τ f := by
  have ha := VaryingRing.pullAdditive C τ f
  have hl := VaryingRing.pullLimits C τ f
  have hc := VaryingRing.pullColimits C τ f
  exact exact_derived_congr (pull_eq C τ f)

private theorem J_eq {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J C τ j = VaryingRing.J C τ j := by
  have ha := VaryingRing.extensionAdditive C τ j
  have hl := VaryingRing.extensionLimits C τ j
  have hc := VaryingRing.extensionColimits C τ j
  exact exact_derived_congr (extension_eq C τ j)

private theorem R_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R C τ f = VaryingRing.P C τ f := by
  have ha := VaryingRing.push_additive C τ f
  exact right_derived_congr (push_eq C τ f)

/-- The open-extension unit is invertible. Source: Stacks, Tags 03DI and 09AE
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: on an object lying over the open there is exactly one lift to it, so restriction
of the extension presheaf is the original module. This survives sheafification,
termwise extension to strict towers, and exact localization. -/
theorem jAdj_unit_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (jAdj C τ j).unit := by
  have : (VaryingRing.pull C τ j).IsRightAdjoint :=
    VaryingRing.pull_isRightAdjoint C τ j
  have hu : IsIso (ordinaryOpenAdj C τ j).unit :=
    chosen_unit_isIso_congr (pull C τ j) (VaryingRing.pull C τ j)
      (pull_eq C τ j) (VaryingRing.moduleJAdj_unit_isIso C τ j)
  have hf := (jAdj C τ j).fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryCompIso (extension C τ j) (pull C τ j)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso (ordinaryOpenAdj C τ j).unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso _)
  have := hf.full
  have := hf.faithful
  infer_instance

/-- The unit-normalized comparison is invertible for a cartesian open square and
arbitrary B. Source: Stacks, Tag 09AE and blueprint, second proof step
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: restriction commutes with direct image on the same pulled-back test object.
The two routes are left adjoint to these canonically identified right adjoints.
Their unique unit-preserving comparison is invertible and its inverse has exactly
the displayed transpose. The equalities descend from strict complexes. -/
theorem betaInv_isIso {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : IsIso (betaInv C τ gU j' j g h) := by
  have hu : IsIso (jAdj C τ j).unit := jAdj_unit_isIso C τ j
  have := jAdj_unit_isIso C τ j'
  let ff := (jAdj C τ j').fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have hi (M : Derived C τ U) : IsIso ((betaInv C τ gU j' j g h).app M) := by
    have := VaryingRing.derived_basechange_counit C τ gU j' j g h hsq M
    have hm := (VaryingRing.jAdj C τ j').mem_essImage_of_counit_isIso
      ((VaryingRing.G C τ g).obj ((VaryingRing.J C τ j).obj M))
    have hm' : (J C τ j').essImage ((P C τ g).obj ((J C τ j).obj M)) := by
      rw [P_eq, J_eq, J_eq]
      exact hm
    have := (jAdj C τ j').isIso_counit_app_iff_mem_essImage.mpr hm'
    change IsIso (betaInvApp C τ gU j' j g h M)
    unfold betaInvApp
    rw [Adjunction.homEquiv_counit]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Cartesian open base change, oriented as G_g j_! → j'_! G_gU.
Source: Stacks, Tag 09AE (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
noncomputable def beta {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : J C τ j ⋙ P C τ g ≅ P C τ gU ⋙ J C τ j' :=
  (@asIso _ _ _ _ (betaInv C τ gU j' j g h)
    (betaInv_isIso C τ gU j' j g h hsq)).symm

/-- The canonical map from open extension to direct image is the counit mate of the
inverse open unit. Source: Stacks, Tags 03DI and 09AE
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
noncomputable def openToS {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J C τ j ⟶ R C τ j :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft (J C τ j) (adj C τ j).unit ≫
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (@inv _ _ _ _ (jAdj C τ j).unit (jAdj_unit_isIso C τ j)) (R C τ j) ≫
          (Functor.leftUnitor _).hom

/-- For a clopen immersion the canonical open-to-direct-image comparison is invertible.
Source: Stacks, Tag 09AE and blueprint, fourth proof step
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: over each pro-etale test object split sections into the product of sections on
the inverse image of the clopen image and on its complement. Both extension and direct
image give the first factor with zero second factor. The specified comparison is the
identity on the first factor. The same formula acts termwise on towers and complexes. -/
theorem openToS_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsClosedImmersion j] : IsIso (openToS C τ j) := by
  obtain ⟨e⟩ := VaryingRing.derived_clopen_iso C τ j
  have he : Nonempty (J C τ j ≅ R C τ j) := by
    rw [J_eq, R_eq]
    exact ⟨e⟩
  obtain ⟨e⟩ := he
  have hu : IsIso (jAdj C τ j).unit := jAdj_unit_isIso C τ j
  let ff := (jAdj C τ j).fullyFaithfulLOfIsIsoUnit
  let fp := ff.ofIso e
  have := fp.full
  have := fp.faithful
  have hi (M : Derived C τ U) : IsIso ((openToS C τ j).app M) := by
    have hunit : IsIso ((adj C τ j).unit.app ((J C τ j).obj M)) :=
      (adj C τ j).isIso_unit_app_of_iso (e.app M)
    have hinv : IsIso ((inv (jAdj C τ j).unit).app M) := by infer_instance
    have himap : IsIso ((R C τ j).map ((inv (jAdj C τ j).unit).app M)) := by
      infer_instance
    let e' := asIso ((adj C τ j).unit.app ((J C τ j).obj M)) ≪≫
      (R C τ j).mapIso (asIso ((inv (jAdj C τ j).unit).app M))
    have he' : (openToS C τ j).app M = e'.hom := by
      simp only [openToS, NatTrans.comp_app, Functor.rightUnitor_inv_app,
        Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
        Functor.leftUnitor_hom_app, Category.id_comp, e',
        Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
      erw [Category.comp_id]
    rw [he']
    exact e'.isIso_hom
  exact NatIso.isIso_of_isIso_app _

/-- The intrinsic clopen component projection, with no arbitrary splitting choice.
Source: Stacks, Tag 09AE and blueprint, fourth proof step
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
noncomputable def pi {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
    [IsClosedImmersion s] : 𝟭 (Derived C τ X) ⟶ P C τ s ⋙ J C τ s :=
  (adj C τ s).unit ≫ Functor.whiskerLeft (P C τ s)
    (@inv _ _ _ _ (openToS C τ s) (openToS_isIso C τ s))

/-- The normalized non-cartesian open comparison uses beta and the intrinsic clopen
projection, followed by the open and pullback compositors. Source: Stacks, Tag 0F7B
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
noncomputable def alpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : J C τ i ⋙ P C τ p ⟶ P C τ r ⋙ J C τ k :=
  (beta C τ (pullback.snd p i) (pullback.fst p i) i p
    (pullback.condition.symm) (IsPullback.of_hasPullback p i).flip).hom ≫
  Functor.whiskerRight (Functor.whiskerLeft (P C τ (pullback.snd p i))
    (pi C τ (StrictTower.squareLift k r p i h))) (J C τ (pullback.fst p i)) ≫
  Functor.whiskerRight
    (Functor.associator (P C τ (pullback.snd p i)) (P C τ (StrictTower.squareLift k r p i h))
      (J C τ (StrictTower.squareLift k r p i h))).inv (J C τ (pullback.fst p i)) ≫
  (Functor.associator (P C τ (pullback.snd p i) ⋙ P C τ (StrictTower.squareLift k r p i h))
    (J C τ (StrictTower.squareLift k r p i h)) (J C τ (pullback.fst p i))).hom ≫
  Functor.whiskerLeft (P C τ (pullback.snd p i) ⋙ P C τ (StrictTower.squareLift k r p i h))
    ((jComp C τ (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom ≫
      (jCongr C τ (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((pComp C τ (StrictTower.squareLift k r p i h) (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (P C τ) (pullback.lift_snd k r h))).hom) (J C τ k)

/-- The proper/open comparison is exactly the proper-adjunction mate of alpha.
Source: Stacks, Tags 0F7B and 07A7
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
noncomputable def gamma {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : R C τ r ⋙ J C τ i ⟶ J C τ k ⋙ R C τ p :=
  mateEquiv (adj C τ r) (adj C τ p) (alpha C τ k r p i h)

/-- The base-change arrow is the mate of the canonical pullback-square isomorphism.
Source: Stacks, Tag 07A7 (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
noncomputable def exchange {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    R C τ p ⋙ P C τ i ⟶ P C τ k ⋙ R C τ r :=
  mateEquiv (adj C τ p) (adj C τ r) (squareP C τ k r p i h).hom



/-- The cartesian open comparison conjugated as an isomorphism of right adjoints.
Source: Stacks 0F7B; the conjugate-unit equation of Mathlib.Adjunction.Mates
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def cartesianConjugate {W S T : Scheme.{u}} (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion i] :
    R C τ p ⋙ P C τ i ≅ P C τ (pullback.fst p i) ⋙ R C τ (pullback.snd p i) :=
  conjugateIsoEquiv ((jAdj C τ i).comp (adj C τ p))
    ((adj C τ (pullback.snd p i)).comp (jAdj C τ (pullback.fst p i)))
    (beta C τ (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).symm

/-- Restricting k-extension to the pulled-back open leaves s-extension.
Source: Stacks 0F7B and 03DI, via the inverse open unit
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def restrictFactor {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    J C τ k ⋙ P C τ (pullback.fst p i) ≅ J C τ (StrictTower.squareLift k r p i h) :=
  Functor.isoWhiskerRight
    ((jComp C τ (StrictTower.squareLift k r p i h) (pullback.fst p i)) ≪≫
      jCongr C τ (pullback.lift_fst k r h)).symm (P C τ (pullback.fst p i)) ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (J C τ (StrictTower.squareLift k r p i h))
    (@asIso _ _ _ _ (jAdj C τ (pullback.fst p i)).unit
      (jAdj_unit_isIso C τ (pullback.fst p i))).symm ≪≫
  Functor.rightUnitor _

/-- The specified lambda isomorphism: conjugate beta, inverse open unit, the clopen
section comparison, and direct-image composition. No isomorphism is chosen after
coefficient evaluation. Source: Stacks 0F7B, open case
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def lambda {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : (J C τ k ⋙ R C τ p) ⋙ P C τ i ≅ R C τ r :=
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (J C τ k) (cartesianConjugate C τ p i) ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight (restrictFactor C τ k r p i h) (R C τ (pullback.snd p i)) ≪≫
  Functor.isoWhiskerRight
    (@asIso _ _ _ _ (openToS C τ (StrictTower.squareLift k r p i h))
      (openToS_isIso C τ (StrictTower.squareLift k r p i h))) (R C τ (pullback.snd p i)) ≪≫
  sComp C τ (StrictTower.squareLift k r p i h) (pullback.snd p i) ≪≫
  eqToIso (congrArg (R C τ) (pullback.lift_snd k r h))

/-- Gamma is the open adjunct of inverse lambda, and its restriction is inverse lambda
under the open unit. Source: Stacks 0F7B; Mathlib unit_conjugateEquiv_symm
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: transport P_i Gamma along the right-adjoint conjugate of beta. Mate pasting
turns the transported square into pi_s P_q. The clopen section formula identifies
pi_s with eta_s. The mate word is therefore the unit of the composite adjunction
P_s P_q followed by its counit. Triangle identities make it the inverse of the
S_q S_s compositor. This gives the restriction equation. The open Hom bijection
then gives the adjunct equation; no equality is inferred from evaluations. -/
theorem gamma_adjunct {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Derived C τ V) :
    (jAdj C τ i).homEquiv _ _ ((gamma C τ k r p i h).app M) =
      (lambda C τ k r p i h).inv.app M ∧
    (jAdj C τ i).unit.app ((R C τ r).obj M) ≫
      (P C τ i).map ((gamma C τ k r p i h).app M) ≫
        (lambda C τ k r p i h).hom.app M = 𝟙 _ := by
  sorry

/-- Vertical, horizontal and base-change coherence for every commutative proper/open
square, as equalities in derived semilinear-system categories, without assuming evaluation
faithful. Source: Stacks, Tags 0F7C, 0F7D and 0F7F, and blueprint, steps 5, 6, 10, 11
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: for alpha, pull the clopen decompositions to each test object. In a vertical
or horizontal pasting the selected opens are nested, so successive component
projections equal the outer component projection. Base change pulls both clopen
components and the identity/zero projector to the corresponding components. Verify
these equations on their intersections using sheaf uniqueness. Apply the exact
functors termwise to towers and complexes, then use localization uniqueness to
descend the equations. Take proper-adjunction mates with composition adjunctions.
Mate pasting gives the two composition laws; the pullback cube gives the base-change
law. Associativity of normalized compositors makes all parenthesizations agree. -/
theorem semilinearProperOpenMatePasting :
    (∀ {A C₀ E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C₀ ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C₀) (r₂ : C₀ ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : Derived C τ A),
      (J C τ j).map ((sComp C τ r₁ r₂).hom.app M) ≫
          (gamma C τ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (sComp C τ p₁ p₂).inv.app ((J C τ k).obj M) =
        (gamma C τ i r₂ p₂ j h₂).app ((R C τ r₁).obj M) ≫
          (R C τ p₂).map ((gamma C τ k r₁ p₁ i h₁).app M)) ∧
    (∀ {A C₀ E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C₀ ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C₀) (p : B₀ ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : Derived C τ A),
      (jComp C τ i j).hom.app ((R C τ r).obj M) ≫
          (gamma C τ (k ≫ l) r q (i ≫ j) h).app M ≫
          (R C τ q).map ((jComp C τ k l).inv.app M) =
        (J C τ j).map ((gamma C τ k r p i h₁).app M) ≫
          (gamma C τ l p q j h₂).app ((J C τ k).obj M)) ∧
    (∀ {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
      (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
      (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
      (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
      (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c) (M : Derived C τ V),
      (P C τ b).map ((gamma C τ k r p i h).app M) ≫
          (exchange C τ a p₁ p b wp).app ((J C τ k).obj M) ≫
          (R C τ p₁).map ((beta C τ d k₁ k a wk sk).hom.app M) =
        (beta C τ c i₁ i b wi si).hom.app ((R C τ r).obj M) ≫
          (J C τ i₁).map ((exchange C τ d r₁ r c wr).app M) ≫
          (gamma C τ k₁ r₁ p₁ i₁ h₁).app ((P C τ d).obj M)) := by
  sorry

/-- Identity normalizations of gamma in both directions.
Source: Stacks, Tags 0F7B and 07A7, blueprint, steps 6 and 10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: the clopen projection is identity for either identity square. Its alpha is the
canonical inverse-image/open-extension identity; taking the mate and using the
triangle identities gives the corresponding identity on direct image or extension. -/
theorem gamma_identities :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived C τ U),
      (gamma C τ j (𝟙 U) (𝟙 X) j h).app M ≫
          (sId C τ X).hom.app ((J C τ j).obj M) =
        (J C τ j).map ((sId C τ U).hom.app M)) ∧
    (∀ {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived C τ U),
      (gamma C τ (𝟙 U) p p (𝟙 X) h).app M ≫
          (R C τ p).map ((jId C τ U).hom.app M) =
        (jId C τ X).hom.app ((R C τ p).obj M)) := by
  sorry


section ScalarRestriction

variable (B : Type (u + 1)) [CommRing B]
  (φ : ∀ n : ℕ, B →+* C n)
  (hφ : ∀ n : ℕ, (τ n).hom.comp (φ (n + 1)) = φ n)

/-- The actual level scalar restriction along the supplied B -> C_n.
Source: Stacks 03CZ; ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
abbrev levelRestriction (X : Scheme.{u}) (n : ℕ) :=
  SemilinearSections.res.{u + 1, u, u + 1}
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom (φ n)))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 400000 in
-- Constructing the entire scalar-restriction functor requires sectionwise transports.
/-- Termwise scalar restriction to ordinary constant-B towers, uniquely characterized
on objects, transitions, and morphisms. Source: Stacks 03CZ; Zheng 4.1
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: keep the component sheaves and restrict their scalar actions along phi_n.
The equation hphi makes each horizontal restriction B-linear. Functor identities
and composition are those of the system presheaf. The evaluated functor equations
fix all objects and morphisms, and the section formula fixes every transition;
thus this is a unique actual functor, rather than an arbitrary comparison map. -/
theorem rhoOrdinary_existsUnique (X : Scheme.{u})
    (compatible : ∀ n : ℕ, (τ n).hom.comp (φ (n + 1)) = φ n) :
    ∃! F : Modules C τ X ⥤ StrictTower.Towers B X,
      (∀ n : ℕ, F ⋙ (CategoryTheory.evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) =
        SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology X) (coefficients C X)
          (transition C τ X) n ⋙ levelRestriction C B φ X n) ∧
      (∀ (M : Modules C τ X) (n m : ℕ) (h : n ≤ m) (U : X.ProEt),
        HEq (fun x ↦ ((((F.obj M).map (homOfLE h).op).val.app (op U)) x))
          (fun x : M.val.obj (op (m, U)) ↦
            M.val.map (Prod.mkHom (homOfLE h) (𝟙 U)).op x)) := by
  let J₀ := ProEt.topology X
  let A := StrictTower.coefficients B X
  let R₀ := SemilinearSections.ring (coefficientSequenceTopology J₀) (ringSystem C τ X)
  let α (n : ℕ) : A ⟶ coefficients C X n :=
    (constantSheaf J₀ CommRingCat.{u + 1}).map (CommRingCat.ofHom (φ n))
  let a : (Functor.const ℕᵒᵖ).obj A ⟶
      SemilinearSections.rings J₀ (coefficients C X) (transition C τ X) :=
    NatTrans.ofOpSequence α (fun n ↦ by
      simp only [Functor.const_obj_map,
        SemilinearSections.rings, Functor.ofOpSequence_map_homOfLE_succ]
      change _ = (constantSheaf J₀ CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (φ (n + 1))) ≫
          (constantSheaf J₀ CommRingCat.{u + 1}).map (τ n)
      rw [← Functor.map_comp]
      exact congrArg ((constantSheaf J₀ CommRingCat.{u + 1}).map)
        (CommRingCat.hom_ext (compatible n)).symm)
  let p (n : ℕ) := (sheafCompose J₀ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (α n)
  let ψ (n : ℕ) := eqToHom
    (SemilinearSections.evaluation_ring J₀ (coefficients C X) (transition C τ X) n).symm
  let ρ (n : ℕ) := p n ≫ ψ n
  have hρ {m n : ℕ} (h : n ≤ m) :
      ρ m ≫ (Functor.sheafPushforwardContinuousNatTrans
        (WeilConjectures.verticalNat h) RingCat J₀ (coefficientSequenceTopology J₀)).app
          R₀ = ρ n := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have hm : (ψ m).hom.app U = 𝟙 _ := by
      dsimp only [ψ]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    have hn : (ψ n).hom.app U = 𝟙 _ := by
      dsimp only [ψ]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    dsimp only [ρ, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
    simp only [hm, hn]
    change (p m).hom.app U ≫ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((SemilinearSections.ringPresheaf J₀ (coefficients C X) (transition C τ X)).map
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op) = _
    dsimp only [SemilinearSections.ringPresheaf]
    rw [SemilinearSections.horizontal_map']
    have hh := congrArg (fun t ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (t.hom.app U)) (a.naturality (homOfLE h).op)
    change (p m).hom.app U ≫ _ = (p n).hom.app U ≫ 𝟙 _
    rw [Category.comp_id]
    change (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((a.app (op m)).hom.app U) ≫ _ =
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map ((a.app (op n)).hom.app U)
    simp only [Functor.const_obj_map, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.id_hom, NatTrans.comp_app, NatTrans.id_app,
      Functor.map_comp] at hh
    have hi : (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        (𝟙 (A.obj.obj U)) = 𝟙 _ := (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map_id _
    rw [hi] at hh
    erw [Category.id_comp] at hh
    exact hh.symm
  obtain ⟨F, hF⟩ := WeilConjectures.towers_generic J₀ R₀
    (SemilinearSections.ring J₀ A) ρ (fun h ↦ hρ h)
  have hobj (M : Modules C τ X) (n : ℕ) :
      (F.obj M).obj (op n) =
      (levelRestriction C B φ X n).obj
        ((SemilinearSections.evaluation J₀ (coefficients C X) (transition C τ X) n).obj M) :=
    (hF.1 M n).trans (WeilConjectures.pushforward_restrict_obj J₀ R₀ n (p n) (ψ n) M)
  have he (n : ℕ) :
      F ⋙ (CategoryTheory.evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) =
      SemilinearSections.evaluation J₀ (coefficients C X) (transition C τ X) n ⋙
        levelRestriction C B φ X n := by
    refine CategoryTheory.Functor.ext (fun M ↦ hobj M n) ?_
    intro M N f
    apply WeilConjectures.moduleSheaf_hom_eq_of_heq (hobj M n) (hobj N n)
    intro U
    exact hF.2.2 f n U
  refine ⟨F, ⟨he, fun M n m h U ↦ hF.2.1 M m n h (op U)⟩, ?_⟩
  intro G hG
  have hGF (n : ℕ) := (hG.1 n).trans (he n).symm
  have hobjGF (M : Modules C τ X) : G.obj M = F.obj M := by
    refine CategoryTheory.Functor.ext (fun n ↦ Functor.congr_obj (hGF n.unop) M) ?_
    intro m n f
    apply WeilConjectures.moduleSheaf_hom_eq_of_heq
      (Functor.congr_obj (hGF m.unop) M) (Functor.congr_obj (hGF n.unop) M)
    intro U
    exact (hG.2 M n.unop m.unop (leOfHom f.unop) U.unop).trans
      (hF.2.1 M m.unop n.unop (leOfHom f.unop) U).symm
  refine CategoryTheory.Functor.ext hobjGF ?_
  intro M N f
  apply NatTrans.ext
  funext n
  simpa only [NatTrans.comp_app, eqToHom_app, Functor.comp_obj, Functor.comp_map,
    CategoryTheory.evaluation_obj_obj, CategoryTheory.evaluation_obj_map, op_unop] using
      Functor.congr_hom (hGF n.unop) f

/-- The unique ordinary restriction functor with the prescribed section formulas.
Source: Stacks 03CZ (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def rhoOrdinary (X : Scheme.{u}) :=
  (rhoOrdinary_existsUnique C τ B φ X hφ).choose

/-- Scalar restriction is exact without coefficient flatness.
Source: Stacks 03CZ (blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: the ordinary functor leaves underlying additive sheaves and all transition
maps unchanged. Kernels and sheafified cokernels therefore have the same restricted
actions. Componentwise exactness gives additivity and both preservation assertions. -/
theorem rhoOrdinary_exact (X : Scheme.{u}) :
    (rhoOrdinary C τ B φ hφ X).Additive ∧
      PreservesFiniteLimits (rhoOrdinary C τ B φ hφ X) ∧
        PreservesFiniteColimits (rhoOrdinary C τ B φ hφ X) := by
  have he (n : ℕ) : rhoOrdinary C τ B φ hφ X ⋙
      (CategoryTheory.evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) =
      SemilinearSections.evaluation (ProEt.topology X) (coefficients C X)
        (transition C τ X) n ⋙ levelRestriction C B φ X n :=
    (rhoOrdinary_existsUnique C τ B φ X hφ).choose_spec.1.1 n
  have hl : PreservesFiniteLimits (rhoOrdinary C τ B φ hφ X) :=
    preservesFiniteLimits_of_evaluation _ fun n ↦ by rw [he n.unop]; infer_instance
  have hc : PreservesFiniteColimits (rhoOrdinary C τ B φ hφ X) :=
    preservesFiniteColimits_of_evaluation _ fun n ↦ by rw [he n.unop]; infer_instance
  exact ⟨Functor.additive_of_preserves_binary_products _, hl, hc⟩

/-- Additivity of scalar restriction. Source: Stacks 03CZ
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
instance rho_additive (X : Scheme.{u}) : (rhoOrdinary C τ B φ hφ X).Additive :=
  (rhoOrdinary_exact C τ B φ hφ X).1

/-- Left exactness of scalar restriction. Source: Stacks 03CZ
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
instance rho_limits (X : Scheme.{u}) :
    PreservesFiniteLimits (rhoOrdinary C τ B φ hφ X) :=
  (rhoOrdinary_exact C τ B φ hφ X).2.1

/-- Right exactness of scalar restriction. Source: Stacks 03CZ
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
instance rho_colimits (X : Scheme.{u}) :
    PreservesFiniteColimits (rhoOrdinary C τ B φ hφ X) :=
  (rhoOrdinary_exact C τ B φ hφ X).2.2

/-- Exact scalar restriction on ordinary derived systems.
Source: Stacks 03CZ (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
abbrev rho (X : Scheme.{u}) := (rhoOrdinary C τ B φ hφ X).mapDerivedCategory

/-- Direct image and scalar restriction commute by the identity on component sections.
Source: the ring-sheaf change adjunction; Stacks 03CZ and 03D7
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: both composites evaluate to M_n(U ×_Y X), with the B action through phi_n.
The identity is linear, natural in U, n and M, and invertible. Its components on
all sections uniquely determine the comparison. -/
theorem rhoPushOrdinary_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : rhoOrdinary C τ B φ hφ X ⋙ StrictTower.towerDirectImage B f ≅
      push C τ f ⋙ rhoOrdinary C τ B φ hφ Y,
      ∀ (M : Modules C τ X) (n : ℕ) (U : Y.ProEt),
        HEq (fun x ↦ ((((e.hom.app M).app (op n)).val.app (op U)) x))
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x) := by
  sorry

/-- The ordinary inverse-image scalar comparison is the transpose of the uniquely
section-normalized direct-image comparison. Source: the ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def rhoPullInv {X Y : Scheme.{u}} (f : X ⟶ Y) :
    rhoOrdinary C τ B φ hφ Y ⋙ StrictTower.towerPullback B f ⟶
      pull C τ f ⋙ rhoOrdinary C τ B φ hφ X :=
  (mateEquiv (ordinaryAdj C τ f)
    ((proEtaleRingModuleAdjunction f (StrictTower.coefficients B Y)
      (StrictTower.coefficients B X) (StrictTower.constantRingIso B f)).whiskerRight ℕᵒᵖ)).symm
    (rhoPushOrdinary_existsUnique C τ B φ hφ f).choose.inv

/-- The identified-coefficient inverse-image scalar comparison is invertible.
Source: the ring-sheaf change adjunction; Stacks 03EK
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: on underlying inverse-image additive sheaves this transpose is the identity.
The scalar action is restricted along the identified constant maps, so the identity
has an inverse, simultaneously in the coefficient index. -/
theorem rhoPullInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (rhoPullInv C τ B φ hφ f) := by
  sorry

/-- The canonical scalar-restriction inverse-image comparison after exact localization.
Source: the ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def rhoP {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P C τ f ⋙ rho C τ B φ hφ X ≅ rho C τ B φ hφ Y ⋙ StrictTower.G B f :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
  Functor.mapDerivedCategoryNatIso
    (@asIso _ _ _ _ (rhoPullInv C τ B φ hφ f) (rhoPullInv_isIso C τ B φ hφ f)).symm ≪≫
  Functor.mapDerivedCategoryCompIso _ _

/-- The direct-image comparison is the actual derived mate of rhoP inverse.
Source: the ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def rhoR {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R C τ f ⋙ rho C τ B φ hφ Y ⟶ rho C τ B φ hφ X ⋙ StrictTower.R B f :=
  mateEquiv (adj C τ f) (StrictTower.adj B f) (rhoP C τ B φ hφ f).inv

/-- The specified derived direct-image mate is invertible.
Source: the ring-sheaf change adjunction; Zheng 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: evaluation of this mate is the canonical scalar-restriction direct-image
comparison of the ring-sheaf adjunction, by its adjunct clause. Each is invertible.
Levelwise detection of quasi-isomorphisms then gives invertibility on towers.
This uses detection of isomorphisms and never faithfulness on morphisms. -/
theorem rhoR_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (rhoR C τ B φ hφ f) := by
  sorry

/-- The open scalar comparison is fixed by the open-adjunction transpose of rhoP.
Source: Stacks 03DI and the ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def rhoJInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    rho C τ B φ hφ U ⋙ StrictTower.J B j ⟶ J C τ j ⋙ rho C τ B φ hφ X :=
  (mateEquiv (jAdj C τ j) (StrictTower.jAdj B j)).symm (rhoP C τ B φ hφ j).hom

/-- Open extension commutes with scalar restriction under its ordinary section units.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: localized extension is the same module on the open and zero on its complement.
Scalar restriction keeps both pieces, and its open-adjunction transpose is the
identity on the original sections. Exact localization preserves this comparison. -/
theorem rhoJInv_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (rhoJInv C τ B φ hφ j) := by
  sorry

/-- The invertible, open-unit-normalized scalar-restriction comparison.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def rhoJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J C τ j ⋙ rho C τ B φ hφ X ≅ rho C τ B φ hφ U ⋙ StrictTower.J B j :=
  (@asIso _ _ _ _ (rhoJInv C τ B φ hφ j) (rhoJInv_isIso C τ B φ hφ j)).symm

/-- Scalar restriction identifies the intrinsic mate with the normalized constant-tower
mate before evaluation. Source: Stacks 0F7B and the ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: scalar restriction preserves the section-normalized beta and the clopen
identity/zero projection, so it preserves alpha. Paste this equality with the
inverse-image scalar squares for p and r and take their adjunction mates. The
result is exactly the displayed equation with the canonical rhoR and rhoJ factors.
The argument is an equality of specified system maps, not detection by evaluation. -/
theorem gamma_scalarRestriction {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Derived C τ V) :
    (rho C τ B φ hφ T).map ((gamma C τ k r p i h).app M) ≫
      (rhoR C τ B φ hφ p).app ((J C τ k).obj M) ≫
      (StrictTower.R B p).map ((rhoJ C τ B φ hφ k).hom.app M) =
    (rhoJ C τ B φ hφ i).hom.app ((R C τ r).obj M) ≫
      (StrictTower.J B i).map ((rhoR C τ B φ hφ r).app M) ≫
      (StrictTower.gamma B k r p i h).app ((rho C τ B φ hφ V).obj M) := by
  sorry

end ScalarRestriction

/-- Evaluation at n followed by the actual constant strict diagram. This construction
retains the input module, without choices of maps or coefficient lifts.
Source: Zheng 4.1 and 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
abbrev levelTower (n : ℕ) (X : Scheme.{u}) :
    Modules C τ X ⥤ StrictTower.Towers (C n) X :=
  SemilinearSections.evaluation.{u + 1, u, u + 1}
    (ProEt.topology X) (coefficients C X) (transition C τ X) n ⋙
      Functor.const ℕᵒᵖ

/-- Exact localization of evaluation followed by a constant diagram. Evaluation at
any tower index recovers the actual n-th module, with its C_n action.
Source: Zheng 4.1 and 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
abbrev E (n : ℕ) (X : Scheme.{u}) := (levelTower C τ n X).mapDerivedCategory

section Evaluation
variable (n : ℕ)

private theorem constant_direct_image_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingDirectImageMap f (coefficients C Y n) (coefficients C X n)
      (StrictTower.constantRingIso (C n) f) =
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (C n) := by
  exact ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _

attribute [local irreducible] proEtaleRingDirectImageMap proEtaleConstantDirectImageMap
attribute [local irreducible] coefficientMap VaryingRing.moduleEvalP

private theorem sequence_push_evaluation_normalized
    {A B : Type (u + 1)} [Category.{u} A] [Category.{u} B]
    (J : GrothendieckTopology A) (K : GrothendieckTopology B) (F : A ⥤ B)
    [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)]
    [(Prod.sectR n A).IsContinuous J (coefficientSequenceTopology J)]
    [(Prod.sectR n B).IsContinuous K (coefficientSequenceTopology K)]
    [(Prod.sectR n A ⋙ (𝟭 ℕ).prod F).IsContinuous J (coefficientSequenceTopology K)]
    [(F ⋙ Prod.sectR n B).IsContinuous J (coefficientSequenceTopology K)]
    {R : Sheaf (coefficientSequenceTopology J) RingCat.{u + 1}}
    {S : Sheaf (coefficientSequenceTopology K) RingCat.{u + 1}}
    {r : Sheaf J RingCat.{u + 1}} {s : Sheaf K RingCat.{u + 1}}
    (a : r ⟶ ((Prod.sectR n A).sheafPushforwardContinuous RingCat.{u + 1}
      J (coefficientSequenceTopology J)).obj R)
    (b : s ⟶ ((Prod.sectR n B).sheafPushforwardContinuous RingCat.{u + 1}
      K (coefficientSequenceTopology K)).obj S)
    (φ₀ : R ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{u + 1}
      (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj S)
    (ψ : r ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj s)
    (he : a ≫ ((Prod.sectR n A).sheafPushforwardContinuous RingCat.{u + 1}
      J (coefficientSequenceTopology J)).map φ₀ =
      ψ ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map b) :
    ∃ d : SheafOfModules.pushforward.{u + 1} φ₀ ⋙ SheafOfModules.pushforward a ≅
        SheafOfModules.pushforward b ⋙ SheafOfModules.pushforward ψ,
      (∀ (M : SheafOfModules.{u + 1} S) (U : A),
        HEq (fun x ↦ (d.hom.app M).val.app (op U) x)
          (fun x : M.val.obj (op (n, F.obj U)) ↦ x)) ∧
      (∀ (M : SheafOfModules.{u + 1} S) (U : A),
        HEq (fun x ↦ (d.inv.app M).val.app (op U) x)
          (fun x : M.val.obj (op (n, F.obj U)) ↦ x)) := by
  let d : SheafOfModules.pushforward.{u + 1} φ₀ ⋙ SheafOfModules.pushforward a ≅
        SheafOfModules.pushforward b ⋙ SheafOfModules.pushforward ψ :=
    SheafOfModules.pushforwardComp a φ₀ ≪≫
      SheafOfModules.pushforwardCongr he ≪≫ (SheafOfModules.pushforwardComp ψ b).symm
  exact ⟨d, fun _ _ ↦ HEq.rfl, fun _ _ ↦ HEq.rfl⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- The section normalization checks two continuous module pushforward composites.
private theorem level_push_evaluation_normalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Modules C τ X ⥤ Modules C τ Y) (hF : F = VaryingRing.push C τ f) :
    ∃ d : F ⋙ VaryingRing.eval C τ Y n ≅
        VaryingRing.eval C τ X n ⋙ StrictTower.moduleDirectImage (C n) f,
      (∀ (M : Modules C τ X) (U : Y.ProEt),
        HEq (fun x ↦ (d.hom.app M).val.app (op U) x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) ∧
      (∀ (M : Modules C τ X) (U : Y.ProEt),
        HEq (fun x ↦ (d.inv.app M).val.app (op U) x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) := by
  subst F
  let := SemilinearSections.evaluationContinuous.{u + 1, u, u + 1}
    (ProEt.topology Y) n
  let := SemilinearSections.evaluationContinuous.{u + 1, u, u + 1}
    (ProEt.topology X) n
  have : ((𝟭 ℕ).prod (proEtaleBaseChange f)).IsContinuous
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X)) :=
    VaryingRing.baseChange_continuous f
  have := Functor.isContinuous_comp (Prod.sectR n Y.ProEt)
    ((𝟭 ℕ).prod (proEtaleBaseChange f))
    (ProEt.topology Y) (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceTopology (ProEt.topology X))
  have := Functor.isContinuous_comp (proEtaleBaseChange f) (Prod.sectR n X.ProEt)
    (ProEt.topology Y) (ProEt.topology X)
    (coefficientSequenceTopology (ProEt.topology X))
  let a := eqToHom (SemilinearSections.evaluation_ring.{u + 1, u, u + 1}
    (ProEt.topology Y) (coefficients C Y) (transition C τ Y) n).symm
  let b := eqToHom (SemilinearSections.evaluation_ring.{u + 1, u, u + 1}
    (ProEt.topology X) (coefficients C X) (transition C τ X) n).symm
  let φ₀ := VaryingRing.ringMap C τ f
  let ψ := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (proEtaleRingDirectImageMap f (coefficients C Y n) (coefficients C X n)
        (StrictTower.constantRingIso (C n) f))
  have he : a ≫ ((Prod.sectR n Y.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology Y)
        (coefficientSequenceTopology (ProEt.topology Y))).map φ₀ =
      ψ ≫ ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).map b := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have ha : a.hom.app U = 𝟙 _ := by
      dsimp only [a]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    have hb : b.hom.app ((proEtaleBaseChange f).op.obj U) = 𝟙 _ := by
      dsimp only [b]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    change a.hom.app U ≫ φ₀.hom.app (op (n, U.unop)) =
      ψ.hom.app U ≫ b.hom.app ((proEtaleBaseChange f).op.obj U)
    rw [ha, hb]
    erw [Category.id_comp, Category.comp_id]
    have hψ := constant_direct_image_map C n f
    exact congrArg (fun t ↦
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map (t.hom.app U)) hψ.symm
  exact sequence_push_evaluation_normalized n (ProEt.topology Y) (ProEt.topology X)
    (proEtaleBaseChange f) a b φ₀ ψ he

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 400000 in
-- The uniqueness proof compares the section carriers of both composite functors.
/-- Direct image and evaluation commute by the identity on component sections.
Source: the ring-sheaf change adjunction; Stacks 03CZ and 03D7
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: both composites evaluate to M_n(U ×_Y X), with the C_n action.
The identity is linear, natural in U, n and M, and invertible. Its components on
all sections uniquely determine the comparison. -/
theorem evalPushOrdinary_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : levelTower C τ n X ⋙ StrictTower.towerDirectImage (C n) f ≅
      push C τ f ⋙ levelTower C τ n Y,
      ∀ (M : Modules C τ X) (m : ℕ) (U : Y.ProEt),
        HEq (fun x ↦ ((((e.hom.app M).app (op m)).val.app (op U)) x))
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x) := by
  obtain ⟨d, _, hd⟩ := level_push_evaluation_normalized C τ n f (push C τ f)
    (push_eq C τ f)
  let e : levelTower C τ n X ⋙ StrictTower.towerDirectImage (C n) f ≅
      push C τ f ⋙ levelTower C τ n Y :=
    (constant_diagram_square (push C τ f) (VaryingRing.eval C τ Y n)
      (VaryingRing.eval C τ X n) (StrictTower.moduleDirectImage (C n) f) d).symm
  refine ⟨e, ?_, ?_⟩
  · intro M m U
    change HEq (fun x ↦ (d.inv.app M).val.app (op U) x)
      (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)
    exact hd M U
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext m
    ext U x
    change ((e'.hom.app M).app m).val.app U x = (d.inv.app M).val.app U x
    exact congrFun (eq_of_heq ((he' M m.unop U.unop).trans (hd M U.unop).symm)) x

/-- The ordinary inverse-image scalar comparison is the transpose of the uniquely
section-normalized direct-image comparison. Source: the ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def evalPullInv {X Y : Scheme.{u}} (f : X ⟶ Y) :
    levelTower C τ n Y ⋙ StrictTower.towerPullback (C n) f ⟶
      pull C τ f ⋙ levelTower C τ n X :=
  (mateEquiv (ordinaryAdj C τ f)
    ((proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
      (StrictTower.coefficients (C n) X)
      (StrictTower.constantRingIso (C n) f)).whiskerRight ℕᵒᵖ)).symm
    (evalPushOrdinary_existsUnique C τ n f).choose.inv

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Compare normalized component isomorphisms before lifting the adjunction unit.
private theorem eval_pull_mate_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Modules C τ X ⥤ Modules C τ Y) [F.IsRightAdjoint]
    (hF : F = VaryingRing.push C τ f)
    (e : levelTower C τ n X ⋙ StrictTower.towerDirectImage (C n) f ≅
      F ⋙ levelTower C τ n Y)
    (he : ∀ (M : Modules C τ X) (m : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op m)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) :
    IsIso ((mateEquiv (Adjunction.ofIsRightAdjoint F)
      ((proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
        (StrictTower.coefficients (C n) X)
        (StrictTower.constantRingIso (C n) f)).whiskerRight ℕᵒᵖ)).symm e.inv) := by
  dsimp only [Modules, VaryingRing.Modules, VaryingRing.coefficientTransition] at *
  subst F
  obtain ⟨d, hd, hi⟩ := level_push_evaluation_normalized C τ n f
    (VaryingRing.push C τ f) rfl
  have hd' : d = VaryingRing.moduleEvalP C τ f n := by
    unfold VaryingRing.moduleEvalP
    apply (VaryingRing.moduleEvalP_existsUnique C τ f n).choose_spec.2
    intro M U x
    exact congrFun (eq_of_heq (hd M U)) x
  obtain ⟨g, hg, _⟩ := VaryingRing.moduleEvalG_existsUnique C τ f n
  let D := constant_diagram_square (VaryingRing.push C τ f)
    (VaryingRing.eval C τ Y n) (VaryingRing.eval C τ X n)
    (StrictTower.moduleDirectImage (C n) f) d
  let G := constant_diagram_square (VaryingRing.pull C τ f)
    (VaryingRing.eval C τ X n) (VaryingRing.eval C τ Y n)
    (StrictTower.modulePullback (C n) f) g
  have he' : e = D.symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext m
    ext U x
    change ((e.hom.app M).app m).val.app U x = (d.inv.app M).val.app U x
    exact congrFun (eq_of_heq ((he M m.unop U.unop).trans (hi M U.unop).symm)) x
  have hm : mateEquiv (VaryingRing.moduleAdj C τ f)
      ((proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
        (StrictTower.coefficients (C n) X)
        (StrictTower.constantRingIso (C n) f)).whiskerRight ℕᵒᵖ) G.inv = D.hom := by
    apply constant_diagram_mate (VaryingRing.moduleAdj C τ f)
      (proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
        (StrictTower.coefficients (C n) X) (StrictTower.constantRingIso (C n) f))
      (VaryingRing.eval C τ Y n) (VaryingRing.eval C τ X n) g d
    intro M
    rw [hd']
    exact hg M
  rw [he']
  change IsIso ((mateEquiv (VaryingRing.moduleAdj C τ f)
    ((proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
      (StrictTower.coefficients (C n) X)
      (StrictTower.constantRingIso (C n) f)).whiskerRight ℕᵒᵖ)).symm D.hom)
  rw [← hm]
  erw [Equiv.symm_apply_apply]
  exact G.isIso_inv

/-- The identified-coefficient inverse-image scalar comparison is invertible.
Source: the ring-sheaf change adjunction; Stacks 03EK
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: on component n the transpose is the identity inverse-image comparison.
The constant diagram retains that identity at every index, giving its inverse. -/
theorem evalPullInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (evalPullInv C τ n f) := by
  exact eval_pull_mate_isIso C τ n f (push C τ f) (push_eq C τ f)
    (evalPushOrdinary_existsUnique C τ n f).choose
    (evalPushOrdinary_existsUnique C τ n f).choose_spec.1

/-- The canonical evaluation inverse-image comparison after exact localization.
Source: the ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def evalP {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P C τ f ⋙ E C τ n X ≅ E C τ n Y ⋙ StrictTower.G (C n) f :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
  Functor.mapDerivedCategoryNatIso
    (@asIso _ _ _ _ (evalPullInv C τ n f) (evalPullInv_isIso C τ n f)).symm ≪≫
  Functor.mapDerivedCategoryCompIso _ _

/-- The direct-image comparison is the actual derived mate of evalP inverse.
Source: the ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def evalR {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R C τ f ⋙ E C τ n Y ⟶ E C τ n X ⋙ StrictTower.R (C n) f :=
  mateEquiv (adj C τ f) (StrictTower.adj (C n) f) (evalP C τ n f).inv

/-- The specified derived direct-image mate is invertible.
Source: the ring-sheaf change adjunction; Zheng 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: the simultaneous section model computes direct images after evaluation by
the identical section complexes. The derived adjunction identifies this comparison
with the displayed mate. The constant diagram preserves its inverse.
This uses detection of isomorphisms and never faithfulness on morphisms. -/
theorem evalR_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (evalR C τ n f) := by
  sorry

/-- The open scalar comparison is fixed by the open-adjunction transpose of evalP.
Source: Stacks 03DI and the ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def evalJInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    E C τ n U ⋙ StrictTower.J (C n) j ⟶ J C τ j ⋙ E C τ n X :=
  (mateEquiv (jAdj C τ j) (StrictTower.jAdj (C n) j)).symm (evalP C τ n j).hom

/-- Open extension commutes with evaluation under its ordinary section units.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: localized extension is the same module on the open and zero on its complement.
Evaluation keeps both pieces, and its open-adjunction transpose is the
identity on the original sections. Exact localization preserves this comparison. -/
theorem evalJInv_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (evalJInv C τ n j) := by
  sorry

/-- The invertible, open-unit-normalized evaluation comparison.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def evalJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J C τ j ⋙ E C τ n X ≅ E C τ n U ⋙ StrictTower.J (C n) j :=
  (@asIso _ _ _ _ (evalJInv C τ n j) (evalJInv_isIso C τ n j)).symm

/-- Evaluating the intrinsic comparison gives the same normalized mate over C_n.
The constant-diagram presentation merely reuses the existing constant-ring API.
Source: Stacks 0F7B; Zheng 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: evaluation preserves the exact section-normalized open comparison and the
clopen projection. The direct-image comparison is the mate of the evaluated
pullback comparison. Mate pasting gives the equation directly, before any use of
levelwise detection; no faithfulness of evaluation is required. -/
theorem gamma_evaluation {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Derived C τ V) :
    (E C τ n T).map ((gamma C τ k r p i h).app M) ≫
      (evalR C τ n p).app ((J C τ k).obj M) ≫
      (StrictTower.R (C n) p).map ((evalJ C τ n k).hom.app M) =
    (evalJ C τ n i).hom.app ((R C τ r).obj M) ≫
      (StrictTower.J (C n) i).map ((evalR C τ n r).app M) ≫
      (StrictTower.gamma (C n) k r p i h).app ((E C τ n V).obj M) := by
  sorry

end Evaluation

/-- The projector selects the clopen image: identity there, zero on its complement.
Source: Stacks 09AE and the proof of 0F7B
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: split each test object into its intersections with the two clopen components.
The direct-image unit keeps precisely the image factor. The inverse open-to-direct
comparison identifies it with extension by zero. Thus restriction to the image is
the open unit, and restriction to the complement is zero, also on complexes. -/
theorem pi_components {U X D : Scheme.{u}} (s : U ⟶ X) (c : D ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) (M : Derived C τ X) :
    (P C τ s).map ((pi C τ s).app M) = (jAdj C τ s).unit.app ((P C τ s).obj M) ∧
      (P C τ c).map ((pi C τ s).app M) = 0 := by
  constructor
  · have hu := jAdj_unit_isIso C τ s
    let t : Adjunction.Triple (J C τ s) (P C τ s) (R C τ s) :=
      ⟨jAdj C τ s, adj C τ s⟩
    let ff := (jAdj C τ s).fullyFaithfulLOfIsIsoUnit
    have := ff.full
    have := ff.faithful
    have he : openToS C τ s = t.leftToRight := by
      ext N
      simp [openToS, t, Adjunction.Triple.leftToRight]
    have ho := openToS_isIso C τ s
    simp only [pi, NatTrans.comp_app, Functor.whiskerLeft_app, NatIso.isIso_inv_app]
    rw [Functor.map_comp]
    apply (cancel_mono ((P C τ s).map ((openToS C τ s).app ((P C τ s).obj M)))).1
    simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
      Category.comp_id]
    rw [he, t.leftToRight_app_obj, Functor.map_comp]
    change _ = (jAdj C τ s).unit.app _ ≫
      (P C τ s).map ((jAdj C τ s).counit.app M) ≫ _
    rw [← Category.assoc, (jAdj C τ s).right_triangle_components]
    exact (Category.id_comp _).symm
  · have hz (N : VaryingRing.Modules C τ U) :
        IsZero ((VaryingRing.pull C τ c).obj ((VaryingRing.extension C τ s).obj N)) := by
      obtain ⟨e⟩ := VaryingRing.ordinary_clopen_iso C τ s
      have := VaryingRing.moduleJAdj_unit_isIso C τ s
      let ff := (VaryingRing.moduleJAdj C τ s).fullyFaithfulLOfIsIsoUnit
      let fp := ff.ofIso e
      have := fp.full
      have := fp.faithful
      have := (VaryingRing.moduleAdj C τ s).isIso_unit_app_of_iso (e.app N)
      have := VaryingRing.moduleOpenToP_isIso C τ s
      have hi : IsIso ((VaryingRing.modulePi C τ s).app
          ((VaryingRing.extension C τ s).obj N)) := by
        dsimp only [VaryingRing.modulePi, NatTrans.comp_app, Functor.whiskerLeft_app]
        infer_instance
      have hii := (VaryingRing.pull C τ c).map_isIso
        ((VaryingRing.modulePi C τ s).app ((VaryingRing.extension C τ s).obj N))
      rw [(VaryingRing.modulePi_components C τ s c hc _).2] at hii
      exact ((isIsoZero_iff_source_target_isZero _ _).mp hii).1
    let F := extension C τ s ⋙ pull C τ c
    have hz' (N : Modules C τ U) : IsZero (F.obj N) := by
      change IsZero ((pull C τ c).obj ((extension C τ s).obj N))
      rw [pull_eq, extension_eq]
      exact hz N
    have hzD := F.isZero_mapDerivedCategory_obj ((P C τ s).obj M) (fun q ↦ hz' _)
    have hzT := hzD.of_iso
      ((Functor.mapDerivedCategoryCompIso (extension C τ s) (pull C τ c)).app
        ((P C τ s).obj M)).symm
    exact hzT.eq_of_tgt _ _

section FiniteEvaluation
variable (n : ℕ)

/-- The canonical source comparison, assembled from evaluation of J and its R mate.
Source: Stacks 0F7B; Zheng 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def evalSource {V S T : Scheme.{u}} (r : V ⟶ S) (i : S ⟶ T)
    [IsOpenImmersion i] (M : Derived C τ V) :
    (E C τ n T).obj ((J C τ i).obj ((R C τ r).obj M)) ≅
      (StrictTower.J (C n) i).obj
        ((StrictTower.R (C n) r).obj ((E C τ n V).obj M)) :=
  (evalJ C τ n i).app ((R C τ r).obj M) ≪≫
    (StrictTower.J (C n) i).mapIso
      ((@asIso _ _ _ _ (evalR C τ n r) (evalR_isIso C τ n r)).app M)

/-- The canonical target comparison, assembled from the R mate and evaluation of J.
Source: Stacks 0F7B; Zheng 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def evalTarget {V W T : Scheme.{u}} (k : V ⟶ W) (p : W ⟶ T)
    [IsOpenImmersion k] (M : Derived C τ V) :
    (E C τ n T).obj ((R C τ p).obj ((J C τ k).obj M)) ≅
      (StrictTower.R (C n) p).obj
        ((StrictTower.J (C n) k).obj ((E C τ n V).obj M)) :=
  (@asIso _ _ _ _ (evalR C τ n p) (evalR_isIso C τ n p)).app ((J C τ k).obj M) ≪≫
    (StrictTower.R (C n) p).mapIso ((evalJ C τ n k).app M)

/-- At a finite coefficient level with its specified bounded-below etale origin, the
intrinsic mate is the specified finite proper/open comparison, via canonical arrows.
The retained origin is the existing bundled witness; its coefficient carrier and
scalar map are required to be exactly C_n and its identity, respectively. Thus no
coefficient lift, extension of scalars, or extra etale-origin assumption is supplied.
The zero-th tower index evaluates a constant diagram, hence the original n-th level.
Source: Stacks 0F7B and 099R; strict-tower finite comparison
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: apply gamma_evaluation, whose source and target comparisons are evalSource
and evalTarget. Evaluate this equation at index zero of the constant diagram. Apply
the finite comparison clause of normalizedProperOpenCalculus with the supplied
origin w. The equalities hC and hscalar identify its coefficient ring and scalar
map with C_n and identity. Its finiteSource and finiteTarget give the displayed
equation, retaining w.origin and w.iso. No equality is inferred by detecting it
after evaluation. -/
theorem gamma_finite {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) [Finite (C n)] (M : Derived C τ V)
    (w : StrictTower.ScalarEtaleOrigin (C n) V
      ((StrictTower.ev (C n) V 0).obj ((E C τ n V).obj M)))
    (hC : w.Λ = (C n : Type (u + 1)))
    (hscalar : HEq w.φ (RingHom.id (C n))) :
    (StrictTower.finiteSource (C n) r i ((E C τ n V).obj M) 0 w).hom ≫
      (StrictTower.ev (C n) T 0).map ((evalSource C τ n r i M).inv) ≫
      (StrictTower.ev (C n) T 0).map ((E C τ n T).map ((gamma C τ k r p i h).app M)) ≫
      (StrictTower.ev (C n) T 0).map ((evalTarget C τ n k p M).hom) =
    (StrictTower.HD (C n) T w.Λ w.φ).map
      ((StrictTower.finiteGamma w.Λ k r p i h).hom.app w.origin.L) ≫
      (StrictTower.finiteTarget (C n) k p ((E C τ n V).obj M) 0 w).hom := by
  have _hC := hC
  have _hscalar := hscalar
  have he := gamma_evaluation C τ n k r p i h M
  have ht : (E C τ n T).map ((gamma C τ k r p i h).app M) ≫
      (evalTarget C τ n k p M).hom =
      (evalSource C τ n r i M).hom ≫
        (StrictTower.gamma (C n) k r p i h).app ((E C τ n V).obj M) := by
    simpa only [evalSource, evalTarget, Iso.trans_hom, Functor.mapIso_hom,
      Functor.comp_obj,
      Iso.app_hom, asIso_hom, Category.assoc] using he
  exact (map_iso_transport (StrictTower.ev (C n) T 0)
    (evalSource C τ n r i M) (evalTarget C τ n k p M)
    ((E C τ n T).map ((gamma C τ k r p i h).app M))
    ((StrictTower.gamma (C n) k r p i h).app ((E C τ n V).obj M)) ht
    (StrictTower.finiteSource (C n) r i ((E C τ n V).obj M) 0 w).hom).trans
      (StrictTower.gamma_evaluation (C n) k r p i h ((E C τ n V).obj M) 0 w)

end FiniteEvaluation

/-- Coherence of the specified compositors makes iterated pasting independent of
parenthesization, for inverse image, its right-adjoint mate, and open extension.
Source: Stacks 0F7C--0F7F; Mathlib mateEquiv_hcomp and mateEquiv_vcomp
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: the ordinary direct-image compositor is restriction along the canonical
iterated-fibre-product isomorphism. Both threefold composites send a section to
its restriction along the same map, by the fibre-product universal property.
Conjugate this equality to the inverse-image adjoints and localize. This proves
the first assertion. Right-adjoint conjugation and mate pasting prove the second.
Conjugation using the open adjunctions proves the third. Repeated associativity
reduces every finite parenthesization to the same one; the binary gamma pasting
laws therefore identify every parenthesization with the outer-square gamma. -/
theorem compositor_associativity :
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (M : Derived C τ T),
      (pComp C τ (f ≫ g) h).hom.app M ≫
        (pComp C τ f g).hom.app ((P C τ h).obj M) =
      (eqToIso (congrArg (P C τ) (Category.assoc f g h))).hom.app M ≫
        (pComp C τ f (g ≫ h)).hom.app M ≫
        (P C τ f).map ((pComp C τ g h).hom.app M)) ∧
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (M : Derived C τ X),
      (R C τ h).map ((sComp C τ f g).hom.app M) ≫
        (sComp C τ (f ≫ g) h).hom.app M =
      (sComp C τ g h).hom.app ((R C τ f).obj M) ≫
        (sComp C τ f (g ≫ h)).hom.app M ≫
        (eqToIso (congrArg (R C τ) (Category.assoc f g h))).inv.app M) ∧
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
      (M : Derived C τ X),
      (J C τ h).map ((jComp C τ f g).hom.app M) ≫
        (jComp C τ (f ≫ g) h).hom.app M =
      (jComp C τ g h).hom.app ((J C τ f).obj M) ≫
        (jComp C τ f (g ≫ h)).hom.app M ≫
        (jCongr C τ (Category.assoc f g h)).inv.app M) := by
  sorry

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
