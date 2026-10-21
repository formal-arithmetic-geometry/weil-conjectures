/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.SixFunctors.OpenTensorNormalization
public import WeilConjectures.Compactification.Defs

/-!
# Compact-support projection and arbitrary base change

Source: blueprint main-20261015, `det-sp-purity-bc-factors`, proof (2);
Stacks 0E48 and 0GL1 (blueprint: lem-sp-compact-projection-base-change).
The presentations retain the sectionwise direct images, exact inverse images,
K-flat tensor comparisons and adjunction mates. Both ordinary coefficients and
varying coefficient systems use ordinary unbounded derived categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CompactProjectionBaseChange

/-- Ring coefficients on the ordinary or vertical site, with their structural maps.
These data are pinned to the constant finite ring or the recorded quotient-ring system
in the final statement. Source: blueprint proof (2); Stacks 0E48
(blueprint: lem-sp-compact-projection-base-change). -/
structure Coefficients (m : Mode) where
  ring : ∀ T : Scheme.{u}, Sheaf (topology m T) CommRingCat.{u + 1}
  map : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), ring Y ⟶
    ((baseChange m f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m Y) (topology m X)).obj (ring X)

/-- The coefficient map after forgetting only commutativity.
Source: Stacks 03D7 (blueprint: lem-sp-compact-projection-base-change). -/
def Coefficients.moduleMap {m : Mode} (c : Coefficients.{u} m)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sheafCompose (topology m Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (c.ring Y) ⟶
      ((baseChange m f).sheafPushforwardContinuous RingCat.{u + 1}
        (topology m Y) (topology m X)).obj
          ((sheafCompose (topology m X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (c.ring X)) :=
  ⟨Functor.whiskerRight (c.map f).hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- The canonical iterated fibre-product comparison on the site.
Its factors are the existing pullback-composition comparisons and the square equation.
Source: Stacks 09A5, 0E48 (blueprint: lem-sp-compact-projection-base-change). -/
def siteSquare (m : Mode) {X' X Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (s : CommSq a b f g) : baseChange m g ⋙ baseChange m b ≅
      baseChange m f ⋙ baseChange m a := by
  let e : proEtaleBaseChange g ⋙ proEtaleBaseChange b ≅
      proEtaleBaseChange f ⋙ proEtaleBaseChange a :=
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b g).symm ≪≫
      eqToIso (congrArg (fun h => proEtaleBaseChange h) s.w.symm) ≪≫
        MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) a f
  cases m with
  | ordinary => exact e
  | systems => exact NatIso.prod (Iso.refl (𝟭 ℕ)) e

/-- Exact open extension as the left adjoint to the actual module inverse image.
The adjunction determines it up to its unique compatible isomorphism. This is
termwise extension by zero, including the vertical site of varying ring systems.
Source: Stacks 03DI, 0F6Z (blueprint: lem-sp-compact-projection-base-change). -/
structure OpenModel {m : Mode} {c : Coefficients.{u} m}
    {U T : Scheme.{u}} (j : U ⟶ T)
    (o : Operation (baseChange m j) (c.ring T) (c.ring U)) where
  functor : Mod (c.ring U) ⥤ Mod (c.ring T)
  adjunction : functor ⊣ o.pullback
  [additive : functor.Additive]
  [limits : PreservesFiniteLimits functor]
  [colimits : PreservesFiniteColimits functor]
  unit : ∀ M, IsIso (adjunction.unit.app M)

attribute [instance] OpenModel.additive OpenModel.limits OpenModel.colimits

/-- Canonical operations on the fixed ringed sites. The ordinary direct image is
literal sectionwise direct image with the specified coefficient map. Inverse image
is its module left adjoint, and its exact localization and K-injective right derived
functor are the existing constructions `Operation.left` and `Operation.right`.
Tensor comparisons retain their pure-section and K-flat total-complex normalizations.
The right squares are fixed on every section by the actual fibre-product comparison;
no derived exchange/projection coherence is assumed here.
Source: Stacks 03D7, 07A4, 07A5, 0E48, 0GL1
(blueprint: lem-sp-compact-projection-base-change). -/
structure Presentation {m : Mode} (c : Coefficients.{u} m) where
  operation : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    Operation (baseChange m f) (c.ring Y) (c.ring X)
  coefficient : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (operation f).coefficient = c.moduleMap f
  tensor : ∀ T : Scheme.{u}, TensorModel (c.ring T)
  ordinaryTensor : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    Operation.OrdinaryTensor (operation f)
  tensorComparison : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    TensorComparison (operation f).pullback (operation f).leftModel
      (tensor Y) (tensor X) (ordinaryTensor f).iso
  openModel : ∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j],
    OpenModel j (operation j)
  rightSquare : ∀ {X' X Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (_s : CommSq a b f g),
    (operation b).pushforward ⋙ (operation g).pushforward ≅
      (operation a).pushforward ⋙ (operation f).pushforward
  rightSections : ∀ {X' X Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (s : CommSq a b f g) (M : Mod (c.ring X')) (W : (Site m Y)ᵒᵖ),
    HEq (fun x => ((rightSquare s).hom.app M).val.app W x)
      (fun x => M.val.map ((siteSquare m s).inv.app W.unop).op x)

/-- The ordinary inverse-image square is the conjugate of the sectionwise direct-image
square. Source: Stacks 04J0, 0E48 (blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.ordinarySquare {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (s : CommSq a b f g) :
    (o.operation g).pullback ⋙ (o.operation b).pullback ≅
      (o.operation f).pullback ⋙ (o.operation a).pullback :=
  (conjugateIsoEquiv ((o.operation f).moduleAdjunction.comp (o.operation a).moduleAdjunction)
    ((o.operation g).moduleAdjunction.comp (o.operation b).moduleAdjunction)).symm
      (o.rightSquare s).symm

/-- Exact termwise localization of that very ordinary square.
Source: Stacks 0735, 0E48 (blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.square {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (s : CommSq a b f g) :
    (o.operation g).left ⋙ (o.operation b).left ≅
      (o.operation f).left ⋙ (o.operation a).left :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (o.ordinarySquare s) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The actual termwise open extension on unbounded complexes.
Source: Stacks 015F, 03DI (blueprint: lem-sp-compact-projection-base-change). -/
abbrev Presentation.shriek {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (o.openModel j).functor.mapDerivedCategory

/-- Localization of the ordinary open adjunction, retaining its unit normalization.
Source: Stacks 015F (blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.openAdjunction {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    o.shriek j ⊣ (o.operation j).left :=
  exactDerivedAdjunction (o.openModel j).adjunction

/-- Identity-component comparison between postcomposition and currying.
Source: Mathlib currying conventions (blueprint: lem-sp-compact-projection-base-change). -/
def curryPostIso {C D B H : Type v} [Category.{w} C] [Category.{w} D]
    [Category.{w} B] [Category.{w} H] (T : C × D ⥤ B) (F : B ⥤ H) :
    (Functor.postcompose₂.obj F).obj (Functor.curry.obj T) ≅
      Functor.curry.obj (T ⋙ F) :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _))

/-- Identity-component comparison between precomposition and currying.
Source: Mathlib currying conventions (blueprint: lem-sp-compact-projection-base-change). -/
def curryPreIso {C D B H Z : Type v} [Category.{w} C] [Category.{w} D]
    [Category.{w} B] [Category.{w} H] [Category.{w} Z]
    (F : C ⥤ B) (G : D ⥤ H) (T : B × H ⥤ Z) :
    Functor.curry.obj ((F.prod G) ⋙ T) ≅
      (((Functor.whiskeringLeft₂ Z).obj F).obj G).obj (Functor.curry.obj T) :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _))

/-- The normalized tensor comparison in the curried interface of the dependency.
Source: Stacks 07A4 (blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.curriedTensorComparison {m : Mode} {c : Coefficients.{u} m}
    (o : Presentation c) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  curryPostIso (o.tensor Y).functor (o.operation f).left ≪≫
    Functor.curry.mapIso (o.tensorComparison f).comparison ≪≫
      curryPreIso (o.operation f).left (o.operation f).left (o.tensor X).functor

/-- Natural inverse open tensor comparison, constructed by the existing projection-map
adjunction interface. Source: Stacks 0GL1, 0E8I
(blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.gammaInvNat {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (o.openAdjunction j).projectionMap (o.operation j).left
    (Functor.curry.obj (o.tensor U).functor) (Functor.curry.obj (o.tensor T).functor)
    (o.curriedTensorComparison j).inv

/-- Component of the canonical inverse open tensor comparison.
Source: Stacks 0GL1, 0E8I (blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.gammaInv {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (M : Der (c.ring U)) (N : Der (c.ring T)) :=
  ((o.gammaInvNat j).app M).app N

/-- The natural inverse open base-change map is the mate of the canonical square.
Source: Stacks 03S6 (blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.betaInvNat {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
    {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'} {j : X ⟶ B} {h : B' ⟶ B}
    [IsOpenImmersion j] [IsOpenImmersion j'] (s : IsPullback a j' j h) :=
  ((mateEquiv (o.openAdjunction j) (o.openAdjunction j')).symm
    (TwoSquare.mk _ _ _ _ (o.square s.toCommSq).inv)).natTrans

/-- Component of the canonical inverse open base-change comparison.
Source: Stacks 03S6 (blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.betaInv {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
    {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'} {j : X ⟶ B} {h : B' ⟶ B}
    [IsOpenImmersion j] [IsOpenImmersion j'] (s : IsPullback a j' j h)
    (M : Der (c.ring X)) :=
  (o.betaInvNat s).app M

/-- Only open comparison invertibility is recorded here, not the compact-support
projection formula or proper exchange invertibility. These are the open-normalization
conclusions, equally for strict varying coefficient systems.
Source: Stacks 03S6, 0GL1 (blueprint: lem-sp-compact-projection-base-change). -/
structure OpenComparisons {m : Mode} {c : Coefficients.{u} m} (o : Presentation c) : Prop where
  gamma : ∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (M : Der (c.ring U)) (N : Der (c.ring T)), IsIso (o.gammaInv j M N)
  beta : ∀ {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) (M : Der (c.ring X)), IsIso (o.betaInv s M)

/-- The canonical open tensor isomorphism with both variables retained.
Source: Stacks 0GL1 (blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.gammaIso {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
    (h : OpenComparisons o) {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    (o.shriek j).prod (𝟭 _) ⋙ (o.tensor T).functor ≅
      (𝟭 _).prod (o.operation j).left ⋙ (o.tensor U).functor ⋙ o.shriek j := by
  let t := Functor.uncurry.map (o.gammaInvNat j)
  letI : ∀ Z, IsIso (t.app Z) := fun Z => h.gamma j Z.1 Z.2
  letI : IsIso t := NatIso.isIso_of_isIso_app t
  refine ?_ ≪≫ (asIso t).symm ≪≫ ?_
  · exact NatIso.ofComponents (fun _ => Iso.refl _)
  · exact NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro Z W f
      dsimp
      simp only [Category.comp_id, Category.id_comp, ← Functor.map_comp, prod_comp])

/-- The canonical natural open base-change isomorphism.
Source: Stacks 03S6 (blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.betaIso {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
    (h : OpenComparisons o) {X' X B' B : Scheme.{u}}
    {a : X' ⟶ X} {j' : X' ⟶ B'} {j : X ⟶ B} {b : B' ⟶ B}
    [IsOpenImmersion j] [IsOpenImmersion j'] (s : IsPullback a j' j b) :
    o.shriek j ⋙ (o.operation b).left ≅ (o.operation a).left ⋙ o.shriek j' := by
  letI : ∀ M, IsIso ((o.betaInvNat s).app M) := h.beta s
  letI : IsIso (o.betaInvNat s) := NatIso.isIso_of_isIso_app _
  exact (asIso (o.betaInvNat s)).symm

/-- Restrict the open tensor comparison to the proper pullback input, in precisely
that dependency's supplied-domain interface. Source: Stacks 0GL1
(blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.openProjectionIso {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
    (h : OpenComparisons o) {X B Y : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j]
    (p : B ⟶ Y) :
    (((Functor.whiskeringLeft₂ (Der (c.ring B))).obj (o.shriek j)).obj
      (o.operation p).left).obj (Functor.curry.obj (o.tensor B).functor) ≅
    (Functor.postcompose₂.obj (o.shriek j)).obj
      ((((Functor.whiskeringLeft₂ (Der (c.ring X))).obj (𝟭 _)).obj
        ((o.operation p).left ⋙ (o.operation j).left)).obj
          (Functor.curry.obj (o.tensor X).functor)) :=
  NatIso.ofComponents
    (fun M => NatIso.ofComponents
      (fun K => (o.gammaIso h j).app (M, (o.operation p).left.obj K))
      (by
        intro K L z
        simpa using (o.gammaIso h j).hom.naturality
          (CategoryTheory.Prod.mkHom (𝟙 M) ((o.operation p).left.map z))))
    (by
      intro M N r
      ext K
      simpa using (o.gammaIso h j).hom.naturality
        (CategoryTheory.Prod.mkHom r (𝟙 ((o.operation p).left.obj K))))

/-- The proper counit-defined projection, followed by open tensor comparison.
The pullback in the target is literally `j^* p^*`, implementing the stipulated
composition identification with `f^*`. Source: blueprint proof (2); Stacks 0GL1, 0E48
(blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.projection {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
    (h : OpenComparisons o) {X B Y : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j]
    (p : B ⟶ Y) (M : Der (c.ring X)) (K : Der (c.ring Y)) :
    (o.tensor Y).functor.obj (((o.shriek j) ⋙ (o.operation p).right).obj M, K) ⟶
      ((o.shriek j) ⋙ (o.operation p).right).obj
        ((o.tensor X).functor.obj (M, (o.operation j).left.obj ((o.operation p).left.obj K))) :=
  ((CategoryTheory.SuppliedExchangeProjection.compactificationProjectionFromData
    (o.shriek j) ((o.operation p).left ⋙ (o.operation j).left)
    (o.operation p).left (o.operation p).right (o.operation p).derivedAdjunction
    (Functor.curry.obj (o.tensor X).functor) (Functor.curry.obj (o.tensor B).functor)
    (Functor.curry.obj (o.tensor Y).functor)
    (o.curriedTensorComparison p) (o.openProjectionIso h j p)).app M).app K

/-- Proper exchange followed by the canonical open comparison. Both factors are
actual mates of the specified squares. Source: blueprint proof (2); Stacks 0E48, 03S6
(blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.exchange {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
    (h : OpenComparisons o) {X' X B' B Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {j' : X' ⟶ B'} {j : X ⟶ B} {b : B' ⟶ B}
    {p' : B' ⟶ Y'} {p : B ⟶ Y} {v : Y' ⟶ Y}
    [IsOpenImmersion j] [IsOpenImmersion j']
    (so : IsPullback a j' j b) (sp : CommSq b p' p v) (M : Der (c.ring X)) :
    (o.operation v).left.obj (((o.shriek j) ⋙ (o.operation p).right).obj M) ⟶
      ((o.shriek j') ⋙ (o.operation p').right).obj ((o.operation a).left.obj M) :=
  (CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
    (o.shriek j) (o.shriek j')
    (o.operation p).left (o.operation p).right (o.operation p).derivedAdjunction
    (o.operation p').left (o.operation p').right (o.operation p').derivedAdjunction
    (o.operation v).left (o.operation a).left (o.operation b).left
    (o.square sp) (o.betaIso h so)).app M

section Diagram
variable {m : Mode} {c : Coefficients.{u} m} (o : Presentation c) (h : OpenComparisons o)
  {X' X B' B Y' Y : Scheme.{u}}
  {a : X' ⟶ X} {j' : X' ⟶ B'} {j : X ⟶ B} {b : B' ⟶ B}
  {p' : B' ⟶ Y'} {p : B ⟶ Y} {v : Y' ⟶ Y}
  [IsOpenImmersion j] [IsOpenImmersion j']
  (so : IsPullback a j' j b) (sp : CommSq b p' p v)

/-- Target identification: inverse-image tensor comparison, followed by the open
and proper pullback squares. Source: blueprint proof (2); Stacks 0E48
(blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.targetIso (M : Der (c.ring X)) (K : Der (c.ring Y)) :
    (o.operation a).left.obj
        ((o.tensor X).functor.obj (M, (o.operation j).left.obj ((o.operation p).left.obj K))) ≅
      (o.tensor X').functor.obj ((o.operation a).left.obj M,
        (o.operation j').left.obj ((o.operation p').left.obj ((o.operation v).left.obj K))) :=
  (o.tensorComparison a).comparison.app (M, (o.operation j).left.obj
      ((o.operation p).left.obj K)) ≪≫
    (o.tensor X').functor.mapIso (Iso.prod (Iso.refl _)
      ((o.square so.toCommSq).symm.app ((o.operation p).left.obj K) ≪≫
        (o.operation j').left.mapIso ((o.square sp).symm.app K)))

/-- The source tensor identification followed by pulled-back compact projection.
Source: blueprint proof (2); Stacks 0E48
(blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.pulledProjection (M : Der (c.ring X)) (K : Der (c.ring Y)) :
    (o.tensor Y').functor.obj
        ((o.operation v).left.obj (((o.shriek j) ⋙ (o.operation p).right).obj M),
          (o.operation v).left.obj K) ⟶
      (o.operation v).left.obj (((o.shriek j) ⋙ (o.operation p).right).obj
        ((o.tensor X).functor.obj (M, (o.operation j).left.obj ((o.operation p).left.obj K)))) :=
  (o.tensorComparison v).comparison.inv.app
      (((o.shriek j) ⋙ (o.operation p).right).obj M, K) ≫
    (o.operation v).left.map (o.projection h j p M K)

/-- Exchange at the tensor input, followed by the specified target identification.
Source: blueprint proof (2); Stacks 0E48
(blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.tensorTargetExchange (M : Der (c.ring X)) (K : Der (c.ring Y)) :
    (o.operation v).left.obj (((o.shriek j) ⋙ (o.operation p).right).obj
        ((o.tensor X).functor.obj (M, (o.operation j).left.obj ((o.operation p).left.obj K)))) ⟶
      ((o.shriek j') ⋙ (o.operation p').right).obj
        ((o.tensor X').functor.obj ((o.operation a).left.obj M,
          (o.operation j').left.obj ((o.operation p').left.obj ((o.operation v).left.obj K)))) :=
  o.exchange h so sp
      ((o.tensor X).functor.obj (M, (o.operation j).left.obj ((o.operation p).left.obj K))) ≫
    ((o.shriek j') ⋙ (o.operation p').right).map (o.targetIso so sp M K).hom

/-- Exchange tensored with the identity of the pulled-back coefficient.
Source: blueprint proof (2); Stacks 0E48
(blueprint: lem-sp-compact-projection-base-change). -/
def Presentation.tensorExchange (M : Der (c.ring X)) (K : Der (c.ring Y)) :=
  (o.tensor Y').functor.map
    (CategoryTheory.Prod.mkHom (o.exchange h so sp M) (𝟙 ((o.operation v).left.obj K)))

/-- Forward projection/base-change compatibility, its simultaneous naturality, and
its inverse form under exactly the four isomorphism assumptions in the node.
The latter includes the two source/target identifications explicitly.
Source: blueprint proof (2); Stacks 0E48, 0GL1
(blueprint: lem-sp-compact-projection-base-change). -/
def DiagramAssertion : Prop :=
  (∀ (M : Der (c.ring X)) (K : Der (c.ring Y)),
    o.pulledProjection h (v := v) M K ≫ o.tensorTargetExchange h so sp M K =
      o.tensorExchange h so sp M K ≫
        o.projection h j' p' ((o.operation a).left.obj M) ((o.operation v).left.obj K)) ∧
  (∀ (M N : Der (c.ring X)) (K L : Der (c.ring Y)) (r : M ⟶ N) (z : K ⟶ L),
    (o.tensor Y').functor.map
        (CategoryTheory.Prod.mkHom
          ((o.operation v).left.map (((o.shriek j) ⋙ (o.operation p).right).map r))
          ((o.operation v).left.map z)) ≫
      (o.pulledProjection h (v := v) N L ≫ o.tensorTargetExchange h so sp N L) =
    (o.pulledProjection h (v := v) M K ≫ o.tensorTargetExchange h so sp M K) ≫
      ((o.shriek j') ⋙ (o.operation p').right).map
        ((o.tensor X').functor.map
          (CategoryTheory.Prod.mkHom ((o.operation a).left.map r)
            ((o.operation j').left.map
              ((o.operation p').left.map ((o.operation v).left.map z)))))) ∧
  ∀ (M : Der (c.ring X)) (K : Der (c.ring Y))
    [IsIso (o.exchange h so sp M)]
    [IsIso (o.exchange h so sp
      ((o.tensor X).functor.obj (M, (o.operation j).left.obj ((o.operation p).left.obj K))))]
    [IsIso (o.projection h j p M K)]
    [IsIso (o.projection h j' p' ((o.operation a).left.obj M) ((o.operation v).left.obj K))],
    ((o.shriek j') ⋙ (o.operation p').right).map (o.targetIso so sp M K).inv ≫
      inv (o.exchange h so sp
        ((o.tensor X).functor.obj (M, (o.operation j).left.obj ((o.operation p).left.obj K)))) ≫
      (o.operation v).left.map (inv (o.projection h j p M K)) ≫
      (o.tensorComparison v).comparison.hom.app
        (((o.shriek j) ⋙ (o.operation p).right).obj M, K) ≫
      o.tensorExchange h so sp M K =
    inv (o.projection h j' p' ((o.operation a).left.obj M) ((o.operation v).left.obj K))

end Diagram

/-- The constant-ring family and its constant-section structure maps.
Source: Stacks 0H7J (blueprint: lem-sp-compact-projection-base-change). -/
def finiteCoefficients (A : Type (u + 1)) [CommRing A] : Coefficients.{u} .ordinary where
  ring T := (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).obj (CommRingCat.of A)
  map f := proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A)

/-- The ring system is exactly the recorded ell-power system. Its structural map
is fixed on every section at every level by the constant-section direct-image map.
The normalized equivalence retains entire module presheaves and linear morphisms,
so it retains all semilinear transitions, including nonflat coefficient reductions.
Source: blueprint coefficient-tower definition and proof (2); Stacks 00Z4
(blueprint: lem-sp-compact-projection-base-change). -/
def TowerCoefficients (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems) : Prop :=
  (∀ T : Scheme.{u},
    ((sheafCompose (topology .systems T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (c.ring T)).obj = spCoefficientPresheaf l E T) ∧
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) (W : Y.ProEtᵒᵖ),
    HEq (((c.map f).hom.app (op (n, W.unop))).hom)
      (((proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1}
          (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))).hom.app W).hom)) ∧
  ∀ T : Scheme.{u}, ∃ e : spCoefficientTowers l E T ≌ Mod (c.ring T),
    e.functor.Additive ∧
      (∀ M : spCoefficientTowers l E T, HEq (e.functor.obj M).val M.obj) ∧
      (∀ (M N : spCoefficientTowers l E T) (r : M ⟶ N), HEq (e.functor.map r).val r.hom)

/-- The prescribed field-base geometry, the chosen compactification, and arbitrary
base change. The open and proper squares name their universal properties, permitting
any chosen realization of the fibre products; neither arrow on the horizontal base
is required to be flat, smooth or proper.
Source: blueprint proof (2) (blueprint: lem-sp-compact-projection-base-change). -/
def GeometricAssertion (D : WeilConjectures.FiniteFieldDatum.{u})
    {m : Mode} {c : Coefficients.{u} m} (o : Presentation c) (h : OpenComparisons o) : Prop :=
  ∀ (X Y Y' : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [Y.Over (Spec (CommRingCat.of D.k))] [Y'.Over (Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y' ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) (v : Y' ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [v.IsOver (Spec (CommRingCat.of D.k))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (q : Compactification f)
    (X' B' : Scheme.{u}) (a : X' ⟶ X) (f' : X' ⟶ Y')
    (b : B' ⟶ q.Z) (p' : B' ⟶ Y') (j' : X' ⟶ B') [IsOpenImmersion j']
    (_sx : IsPullback a f' f v) (sb : IsPullback b p' q.g v)
    (sj : IsPullback a j' q.i b) (_hf' : j' ≫ p' = f'),
    DiagramAssertion o h sj sb.toCommSq

end AlgebraicGeometry.ProEtale.CompactProjectionBaseChange
