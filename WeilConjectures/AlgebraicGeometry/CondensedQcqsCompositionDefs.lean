/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedShriekBoundedQcqs
public import WeilConjectures.AlgebraicGeometry.ZlShriekComposition
public import WeilConjectures.AlgebraicGeometry.CondensedProperOpenQcqsCalculus
/-! # Condensed compact-support composition over quasi-separated bases

Definition interface (blueprint: def-zl-qcqs-composition-defs).

Source: latest blueprint, lem-zl-shriek-composition.proof, and
sk-thm-sf-comp-composition (1),(2); Stacks Tag 0F7J, lemma-shriek-composition
(blueprint: lem-zl-condensed-shriek-composition-qcqs).

The witnesses below retain the actual compactification functors, proper-refinement maps,
normalized proper/open compositor, and the proper/open isomorphism exchange. All categories
are full subcategories of the ordinary derived category with the pulled-back condensed ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

open CompactSupportComposition

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The existing ordinary bounded constructible category with finite constant local models.
Source: latest blueprint, coefficient/category convention
(blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
abbrev C (X : Scheme.{u}) :=
  ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X

/-- The existing bounded constructible object predicate, with no completion condition.
Source: latest blueprint, coefficient/category convention
(blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
abbrev bc (X : Scheme.{u}) :=
  constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X

/-- A coherent compactification system for the given morphism. The comparison is fixed
on every proper refinement and satisfies identity and cocycle equations.
Source: Stacks 0F7J, refinement comparisons in the source proof, Step 3
(blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
structure System {X Y : Scheme.{u}} (f : X ⟶ Y) where
  preserves : ∀ (c : Compactification f) (K : C ℓ X),
    bc ℓ Y ((rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) c).obj
      K.obj)
  comparison : ∀ c d : Compactification f,
    (bc ℓ X).ι ⋙ rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) c ≅
      (bc ℓ X).ι ⋙ rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) d
  refinement : ∀ (c d : Compactification f) (r : d.Refinement c) (K : C ℓ X),
    (comparison c d).hom.app K =
      (CompactificationReindexing.refinement (Profinite.padicAlgClRingObj ℓ) r).app K.obj
  comparison_id : ∀ c : Compactification f, comparison c c = Iso.refl _
  comparison_cocycle : ∀ c d e : Compactification f,
    comparison c d ≪≫ comparison d e = comparison c e

/-- The actual restriction of Rp_* j_! to bounded constructible objects.
Source: source proof, Steps 2--3 (blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
abbrev System.support {X Y : Scheme.{u}} {f : X ⟶ Y} (S : System ℓ f)
    (c : Compactification f) : C ℓ X ⥤ C ℓ Y :=
  (bc ℓ Y).lift ((bc ℓ X).ι ⋙
    rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) c) (S.preserves c)

/-- The exact derived inverse image along a scheme automorphism, restricted to Dbc.
The preservation proof is precisely the existing reindexing theorem of strict Weil complexes.
Source: source proof, Step 4 (blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
abbrev pull {X : Scheme.{u}} (a : X ≅ X) : C ℓ X ⥤ C ℓ X :=
  (bc ℓ X).lift ((bc ℓ X).ι ⋙ StrictWeil.action (Profinite.padicAlgClRingObj ℓ) a)
    (fun K ↦ ((StrictWeil.action_preserves (Profinite.padicAlgClRingObj ℓ) a K.obj).1).2
      K.property)

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
/-- The canonical proper/open exchange, followed by the prescribed refinement comparison.
Exact-to-total-derived comparison maps retain the canonical coefficient identifications.
Source: source proof, Step 5 (blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
@[irreducible] def exchangeComponent {X Y : Scheme.{u}} {f : X ⟶ Y} (S : System ℓ f)
    (a : X ≅ X) (b : Y ≅ Y) (sq : IsPullback a.hom f f b.hom)
    (c : Compactification f) (K : C ℓ X) :
    (StrictWeil.action (Profinite.padicAlgClRingObj ℓ) b).obj
        ((rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) c).obj
          K.obj) ⟶
      (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) c).obj
        ((StrictWeil.action (Profinite.padicAlgClRingObj ℓ) a).obj K.obj) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ℓ) b.hom).inv.app
      ((rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) c).obj
        K.obj) ≫
    (CompactificationReindexing.squareExchange (Profinite.padicAlgClRingObj ℓ)
      (c := c) (c' := c.ofIsPullback sq) (w := a.hom) (v := b.hom)
      { middle := pullback.fst c.g b.hom
        openSquare := c.isPullback_i_ofIsPullback sq
        properSquare := (c.isPullback_g_ofIsPullback sq).flip.toCommSq }).app K.obj ≫
    (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ)
      (c.ofIsPullback sq)).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ℓ) a.hom).hom.app
          K.obj) ≫
    (S.comparison (c.ofIsPullback sq) c).hom.app ((pull ℓ a).obj K)

/-- Exchange is the specified proper/open map, simultaneously for every compactification.
Source: source proof, Step 5 (blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
structure Exchange {X Y : Scheme.{u}} {f : X ⟶ Y} (S : System ℓ f)
    (a : X ≅ X) (b : Y ≅ Y) (sq : IsPullback a.hom f f b.hom) where
  iso : ∀ c : Compactification f, S.support ℓ c ⋙ pull ℓ b ≅ pull ℓ a ⋙ S.support ℓ c
  normalized : ∀ (c : Compactification f) (K : C ℓ X),
    ((iso c).hom.app K).hom = exchangeComponent ℓ S a b sq c K

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
/-- The specified compositor on a compatible compactification tower. Its middle map
is the unique identity-on-open normalized proper/open interchange, not an arbitrary map.
Source: source proof, Step 2 (blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
def TowerNormalized {X Z Y : Scheme.{u}} {h : X ⟶ Z} {g : Z ⟶ Y}
    (Sh : System ℓ h) (Sg : System ℓ g) (Sgh : System ℓ (h ≫ g))
    (α : ∀ (c : Compactification h) (d : Compactification g)
      (e : Compactification (h ≫ g)), Sh.support ℓ c ⋙ Sg.support ℓ d ≅ Sgh.support ℓ e) :
    Prop :=
  ∀ (T : Compactification.Triangle h g) [QuasiCompact (T.cf.g ≫ T.cg.i)] (K : C ℓ X),
    ∃ m, compositionInterchangeIsNormalized (Profinite.padicAlgClRingObj ℓ) T.cf.g T.cg.i
        (detSfBoundaryCompactification (middle T))
        (D((T.cf.i)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj) m ∧
      ((α T.cf T.cg T.cfg).hom.app K).hom =
        R((T.cg.g)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          (m ≫ R((T.p)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
            ((openFactor (Profinite.padicAlgClRingObj ℓ) T.cf.i T.q T.cfg.i T.i_q).hom.app
              K.obj)) ≫
          (rightDerivedLowerStarComp (Profinite.padicAlgClRingObj ℓ) T.p T.cg.g).hom.app
            (D((T.cfg.i)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj) ≫
          (Functor.rightDerivedFunctorNatIso
            (eqToIso (congrArg (fun t ↦ lowerStar (Profinite.padicAlgClRingObj ℓ) t)
              T.p_g))).hom.app (D((T.cfg.i)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj)

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
/-- Composition, refinement independence, and the isomorphism-exchange equation.
Source: source proof, Steps 2--6 (blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
structure Comparisons {X Z Y : Scheme.{u}} (h : X ⟶ Z) (g : Z ⟶ Y) where
  sh : System ℓ h
  sg : System ℓ g
  sgh : System ℓ (h ≫ g)
  alpha : ∀ (c : Compactification h) (d : Compactification g)
    (e : Compactification (h ≫ g)), sh.support ℓ c ⋙ sg.support ℓ d ≅ sgh.support ℓ e
  tower_normalized : TowerNormalized ℓ sh sg sgh alpha
  independent : ∀ (c c' : Compactification h) (d d' : Compactification g)
    (e e' : Compactification (h ≫ g)) (K : C ℓ X),
    ((alpha c d e).hom.app K).hom ≫ (sgh.comparison e e').hom.app K =
      (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) d).map
          ((sh.comparison c c').hom.app K) ≫
        (sg.comparison d d').hom.app ((sh.support ℓ c').obj K) ≫
        ((alpha c' d' e').hom.app K).hom
  exchange : ∀ (a : X ≅ X) (b : Z ≅ Z) (v : Y ≅ Y)
    (shsq : IsPullback a.hom h h b.hom) (sgsq : IsPullback b.hom g g v.hom),
    Exchange ℓ sh a b shsq × Exchange ℓ sg b v sgsq ×
      Exchange ℓ sgh a v (shsq.paste_vert sgsq)
  comp_exchange : ∀ (a : X ≅ X) (b : Z ≅ Z) (v : Y ≅ Y)
    (shsq : IsPullback a.hom h h b.hom) (sgsq : IsPullback b.hom g g v.hom)
    (c : Compactification h) (d : Compactification g) (e : Compactification (h ≫ g))
    (K : C ℓ X),
    (pull ℓ v).map ((alpha c d e).hom.app K) ≫
        ((exchange a b v shsq sgsq).2.2.iso e).hom.app K =
      ((exchange a b v shsq sgsq).2.1.iso d).hom.app ((sh.support ℓ c).obj K) ≫
        (sg.support ℓ d).map (((exchange a b v shsq sgsq).1.iso c).hom.app K) ≫
        (alpha c d e).hom.app ((pull ℓ a).obj K)

/-- Strict-pair structures and equivariant maps are transported by the normalized exchange.
This is precisely the morphism equation in the recorded fixed-pair category.
Source: source proof, Step 7 (blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
def WeilMaps {X Y : Scheme.{u}} {f : X ⟶ Y} {S : System ℓ f}
    {a : X ≅ X} {b : Y ≅ Y} {sq : IsPullback a.hom f f b.hom}
    (E : Exchange ℓ S a b sq) : Prop :=
  ∀ (c : Compactification f) (K L : C ℓ X)
    (φ : (pull ℓ a).obj K ≅ K) (ψ : (pull ℓ a).obj L ≅ L) (t : K ⟶ L),
    (pull ℓ a).map t ≫ ψ.hom = φ.hom ≫ t →
      (pull ℓ b).map ((S.support ℓ c).map t) ≫
          (E.iso c).hom.app L ≫ (S.support ℓ c).map ψ.hom =
        (E.iso c).hom.app K ≫ (S.support ℓ c).map φ.hom ≫ (S.support ℓ c).map t

/-- The compositor is an isomorphism of strict pairs for every input Weil structure.
The displayed equation also makes its inverse equivariant.
Source: source proof, Step 7 (blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
def WeilCompatibility {X Z Y : Scheme.{u}} {h : X ⟶ Z} {g : Z ⟶ Y}
    (H : Comparisons ℓ h g) (a : X ≅ X) (b : Z ≅ Z) (v : Y ≅ Y)
    (shsq : IsPullback a.hom h h b.hom) (sgsq : IsPullback b.hom g g v.hom) : Prop :=
  WeilMaps ℓ (H.exchange a b v shsq sgsq).1 ∧
    WeilMaps ℓ (H.exchange a b v shsq sgsq).2.1 ∧
    WeilMaps ℓ (H.exchange a b v shsq sgsq).2.2 ∧
    ∀ (c : Compactification h) (d : Compactification g) (e : Compactification (h ≫ g))
      (K : C ℓ X) (φ : (pull ℓ a).obj K ≅ K),
      (pull ℓ v).map ((H.alpha c d e).hom.app K) ≫
          ((H.exchange a b v shsq sgsq).2.2.iso e).hom.app K ≫
          (H.sgh.support ℓ e).map φ.hom =
        ((H.exchange a b v shsq sgsq).2.1.iso d).hom.app ((H.sh.support ℓ c).obj K) ≫
          (H.sg.support ℓ d).map
            (((H.exchange a b v shsq sgsq).1.iso c).hom.app K ≫
              (H.sh.support ℓ c).map φ.hom) ≫ (H.alpha c d e).hom.app K

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
/-- Exact, t-exact equivalences and shift/triangle compatibility for the specified maps.
The vanishing equivalence in every degree expresses t-exactness in both directions
for the inherited ordinary t-structure.
Source: source proof, Steps 2,4,5 (blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
def ExactCompatibility {X Z Y : Scheme.{u}} {h : X ⟶ Z} {g : Z ⟶ Y}
    [(bc ℓ X).IsTriangulated] [(bc ℓ Z).IsTriangulated] [(bc ℓ Y).IsTriangulated]
    (H : Comparisons ℓ h g) : Prop :=
  (∀ (c : Compactification h) (d : Compactification g) (e : Compactification (h ≫ g)),
    CondensedOpenProper.ShiftTriangleCompatibility (H.alpha c d e).hom) ∧
  (∀ (a : X ≅ X), (pull ℓ a).IsEquivalence ∧ (pull ℓ a).IsTriangulated ∧
    ∀ (K : C ℓ X) (n : ℤ),
      IsZero ((DerivedCategory.homologyFunctor _ n).obj (((pull ℓ a).obj K).obj)) ↔
        IsZero ((DerivedCategory.homologyFunctor _ n).obj K.obj)) ∧
  (∀ (b : Z ≅ Z), (pull ℓ b).IsEquivalence ∧ (pull ℓ b).IsTriangulated ∧
    ∀ (K : C ℓ Z) (n : ℤ),
      IsZero ((DerivedCategory.homologyFunctor _ n).obj (((pull ℓ b).obj K).obj)) ↔
        IsZero ((DerivedCategory.homologyFunctor _ n).obj K.obj)) ∧
  (∀ (v : Y ≅ Y), (pull ℓ v).IsEquivalence ∧ (pull ℓ v).IsTriangulated ∧
    ∀ (K : C ℓ Y) (n : ℤ),
      IsZero ((DerivedCategory.homologyFunctor _ n).obj (((pull ℓ v).obj K).obj)) ↔
        IsZero ((DerivedCategory.homologyFunctor _ n).obj K.obj)) ∧
  (∀ (a : X ≅ X) (b : Z ≅ Z) (v : Y ≅ Y)
    (shsq : IsPullback a.hom h h b.hom) (sgsq : IsPullback b.hom g g v.hom),
    (∀ c : Compactification h,
      CondensedOpenProper.ShiftTriangleCompatibility
        ((H.exchange a b v shsq sgsq).1.iso c).hom) ∧
    (∀ d : Compactification g,
      CondensedOpenProper.ShiftTriangleCompatibility
        ((H.exchange a b v shsq sgsq).2.1.iso d).hom) ∧
    (∀ e : Compactification (h ≫ g),
      CondensedOpenProper.ShiftTriangleCompatibility
        ((H.exchange a b v shsq sgsq).2.2.iso e).hom) ∧
    WeilCompatibility ℓ H a b v shsq sgsq)

/-- The map on geometric fibres is the actual base-change functor's map.
Source: finite-field geometric-fibre convention and source proof, Step 1
(blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
def modelMap (D : WeilConjectures.FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
/-- Agreement of each exchange with the recorded separated-scheme exchange, after the
canonical exact-to-total-derived identification. The existential compactification and
input identifications ensure that agreement is asserted on every object and model.
Source: source proof, Step 7 (blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
def SeparatedExchangeAgreement (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) {f : (D.geometricFiber X₀).left ⟶ (D.geometricFiber Y₀).left}
    {S : System ℓ f}
    {a : (D.geometricFiber X₀).left ≅ (D.geometricFiber X₀).left}
    {b : (D.geometricFiber Y₀).left ≅ (D.geometricFiber Y₀).left}
    {sq : IsPullback a.hom f f b.hom} (E : Exchange ℓ S a b sq) : Prop :=
  ∀ (c : Compactification f) (K : C ℓ (D.geometricFiber X₀).left),
    ∃ (c' : Compactification (zlGeometricHom D (SepFinType.homMk f₀)).hom.left)
      (K' : (localizingClosureProEtale (Profinite.padicAlgClRingObj ℓ)
        (zlGeometricScheme D (SepFinType.mk X₀)).obj.left).FullSubcategory)
      (sq' : IsPullback a.hom (zlGeometricHom D (SepFinType.homMk f₀)).hom.left
        (zlGeometricHom D (SepFinType.homMk f₀)).hom.left b.hom),
      HEq c c' ∧ HEq K.obj K'.obj ∧
      HEq (((E.iso c).hom.app K).hom)
        ((leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ℓ)
            b.hom).inv.app
            ((rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ)
              c').obj K'.obj) ≫
          ((zlComparisonData D ℓ hℓ).exchange sq' c' c').hom.app K' ≫
          (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ)
            c').map ((leftDerivedUpperStarIsoMapDerivedCategory
              (Profinite.padicAlgClRingObj ℓ) a.hom).hom.app K'.obj))

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
/-- Agreement with all three recorded separated-scheme comparisons and exchanges.
HEq transports only between the existing encodings of the same geometric fibre.
Source: source proof, Step 7 (blueprint: lem-zl-condensed-shriek-composition-qcqs). -/
def SeparatedAgreement (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p)
    {X₀ Z₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [IsSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    (H : Comparisons ℓ (modelMap D h₀) (modelMap D g₀)) : Prop :=
  (∀ (c : Compactification (modelMap D h₀)) (d : Compactification (modelMap D g₀))
    (e : Compactification (modelMap D h₀ ≫ modelMap D g₀))
    (K : C ℓ (D.geometricFiber X₀).left),
    ∃ (K' : (localizingClosureProEtale (Profinite.padicAlgClRingObj ℓ)
        (zlGeometricScheme D (SepFinType.mk X₀)).obj.left).FullSubcategory)
      (c' : Compactification (zlGeometricHom D (SepFinType.homMk h₀)).hom.left)
      (d' : Compactification (zlGeometricHom D (SepFinType.homMk g₀)).hom.left)
      (e' : Compactification ((zlGeometricHom D (SepFinType.homMk h₀)).hom.left ≫
        (zlGeometricHom D (SepFinType.homMk g₀)).hom.left)),
      HEq K.obj K'.obj ∧ HEq c c' ∧ HEq d d' ∧ HEq e e' ∧
      HEq (((H.alpha c d e).hom.app K).hom)
        (((zlComparisonData D ℓ hℓ).comp
          (zlGeometricHom D (SepFinType.homMk h₀))
          (zlGeometricHom D (SepFinType.homMk g₀)) c' d' e').hom.app K')) ∧
  (∀ (a : (D.geometricFiber X₀).left ≅ (D.geometricFiber X₀).left)
    (b : (D.geometricFiber Z₀).left ≅ (D.geometricFiber Z₀).left)
    (v : (D.geometricFiber Y₀).left ≅ (D.geometricFiber Y₀).left)
    (shsq : IsPullback a.hom (modelMap D h₀) (modelMap D h₀) b.hom)
    (sgsq : IsPullback b.hom (modelMap D g₀) (modelMap D g₀) v.hom),
    SeparatedExchangeAgreement ℓ D hℓ h₀ (H.exchange a b v shsq sgsq).1 ∧
      SeparatedExchangeAgreement ℓ D hℓ g₀ (H.exchange a b v shsq sgsq).2.1 ∧
      SeparatedExchangeAgreement ℓ D hℓ (h₀ ≫ g₀) (H.exchange a b v shsq sgsq).2.2)

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
