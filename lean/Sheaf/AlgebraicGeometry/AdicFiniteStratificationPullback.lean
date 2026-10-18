/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.Paper.LocalizeRingedSiteMorphism
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
import Sheaf.SixFunctors.GeometricInverseImageConstantModule

/-!
# Common finite stratifications and pullback of chosen module trivializations

Source: Stacks Project, Modules on Sites, Tag 093R, and the common-strata argument
in the finite-reductions proof, Step 6
(blueprint: lem-sfb-adic-finite-stratification-pullback).

The Boolean site parameter is false for the small etale site and true for the small
pro-etale site. `AsSmall` enlarges only the arrow universe to the object universe;
it retains every original site object. Coefficients are arbitrary commutative rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The two sites in Stacks 093R, before the harmless small-model transport.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationSite (pro : Bool) (X : Scheme.{u}) : Type (u + 1) :=
  match pro with
  | false => X.Etale
  | true => X.ProEt

/-- Original arrow universes of the sites in Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
instance adicStratificationSiteCategory (pro : Bool) (X : Scheme.{u}) :
    Category.{u} (adicStratificationSite pro X) :=
  match pro with
  | false => inferInstanceAs (Category.{u} X.Etale)
  | true => inferInstanceAs (Category.{u} X.ProEt)

/-- The specified topology, Stacks 093R and 09A5.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationTopology (pro : Bool) (X : Scheme.{u}) :
    GrothendieckTopology (adicStratificationSite pro X) :=
  match pro with
  | false => X.smallEtaleTopology
  | true => ProEt.topology X

/-- Genuine scheme-theoretic base change, Stacks 093R and 09A5.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationBaseChange (pro : Bool) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    adicStratificationSite pro Y ⥤ adicStratificationSite pro X :=
  match pro with
  | false => MorphismProperty.Over.pullback @Etale ⊤ f
  | true => proEtaleBaseChange f

/-- Continuity transported from the existing scheme sites, Stacks 093R and 09A5.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
instance adicStratificationBaseChangeContinuous (pro : Bool) {X Y : Scheme.{u}}
    (f : X ⟶ Y) : (adicStratificationBaseChange pro f).IsContinuous
      (adicStratificationTopology pro Y) (adicStratificationTopology pro X) :=
  match pro with
  | false => AlgebraicGeometry.Etale.isContinuous_overPullback f
  | true => proEtaleBaseChange_isContinuous f

/-- An equivalent small site retaining every original object, Stacks size convention.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
abbrev adicStratificationModel (pro : Bool) (X : Scheme.{u}) :=
  AsSmall.{u + 1} (adicStratificationSite pro X)

/-- Transported topology, Stacks size convention and Tag 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
abbrev adicStratificationModelTopology (pro : Bool) (X : Scheme.{u}) :=
  (AsSmall.down : adicStratificationModel pro X ⥤ adicStratificationSite pro X).inducedTopology
    (adicStratificationTopology pro X)

/-- Base change transported to the equivalent small sites, Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
abbrev adicStratificationModelBaseChange (pro : Bool) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    adicStratificationModel pro Y ⥤ adicStratificationModel pro X :=
  AsSmall.down ⋙ adicStratificationBaseChange pro f ⋙ AsSmall.up

/-- The inverse transport is continuous by the equivalence of sites, Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
instance adicStratificationModelUpContinuous (pro : Bool) (X : Scheme.{u}) :
    (AsSmall.up : adicStratificationSite pro X ⥤ adicStratificationModel pro X).IsContinuous
      (adicStratificationTopology pro X) (adicStratificationModelTopology pro X) :=
  inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1}
    (C := adicStratificationSite pro X)).functor.IsContinuous
      (adicStratificationTopology pro X)
      ((AsSmall.equiv.{u, u + 1, u + 1}
        (C := adicStratificationSite pro X)).inverse.inducedTopology
          (adicStratificationTopology pro X)))

/-- Continuity on the small model, Stacks 093R and the size convention.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
instance adicStratificationModelBaseChangeContinuous (pro : Bool) {X Y : Scheme.{u}}
    (f : X ⟶ Y) : (adicStratificationModelBaseChange pro f).IsContinuous
      (adicStratificationModelTopology pro Y) (adicStratificationModelTopology pro X) :=
  haveI := Functor.isContinuous_comp (adicStratificationBaseChange pro f) AsSmall.up
    (adicStratificationTopology pro Y) (adicStratificationTopology pro X)
    (adicStratificationModelTopology pro X)
  Functor.isContinuous_comp AsSmall.down (adicStratificationBaseChange pro f ⋙ AsSmall.up)
    (adicStratificationModelTopology pro Y) (adicStratificationTopology pro Y)
    (adicStratificationModelTopology pro X)

/-- Constant-ring module sheaves on the chosen site, Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
abbrev adicStratificationModules (pro : Bool) (X : Scheme.{u})
    (R : Type (u + 1)) [CommRing R] :=
  ringedSiteModules.{u + 1} ((constantSheaf (adicStratificationModelTopology pro X)
    RingCat.{u + 1}).obj (RingCat.of R))

/-- The specified constant-section map rho, Stacks 0H7J and 093R.
Its adjoint is the canonical constant-ring inverse-image comparison.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationRho (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (constantSheaf (adicStratificationModelTopology pro Y) RingCat.{u + 1}).obj (RingCat.of R) ⟶
      ((adicStratificationModelBaseChange pro f).sheafPushforwardContinuous RingCat.{u + 1}
        (adicStratificationModelTopology pro Y) (adicStratificationModelTopology pro X)).obj
          ((constantSheaf (adicStratificationModelTopology pro X) RingCat.{u + 1}).obj
            (RingCat.of R)) :=
  ((sheafificationAdjunction (adicStratificationModelTopology pro Y) RingCat.{u + 1}).homEquiv
    _ _).symm (Functor.whiskerLeft (adicStratificationModelBaseChange pro f).op
      (toSheafify (adicStratificationModelTopology pro X)
        ((Functor.const (adicStratificationModel pro X)ᵒᵖ).obj (RingCat.of R))))

/-- Canonical module pullback along rho, Stacks 03D2 and 093R.
This is the existing sheafified module Kan extension, not an arbitrary functor.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
abbrev adicStratificationPullback (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    adicStratificationModules pro Y R ⥤ adicStratificationModules pro X R :=
  SheafOfModules.pullback.{u + 1} (adicStratificationRho pro R f)

/-- The ring comparison adjoint to constant sections, Stacks 0H7J.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationRingMap (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (adicStratificationModelBaseChange pro f) RingCat.{u + 1}
    (adicStratificationModelTopology pro Y) (adicStratificationModelTopology pro X)).homEquiv
    _ _).symm (adicStratificationRho pro R f)

/-- The specified ring comparison is invertible, Stacks 0H7J and proof Step 5.
(blueprint: lem-sfb-adic-finite-stratification-pullback).
Proof: inverse image preserves coproducts and the terminal sheaf. Thus it sends the
coproduct of terminal sheaves indexed by R to the same coproduct. Finite-product
preservation transports the ring operations. Both this comparison and the adjoint of
rho send each constant scalar to itself, so sheafification uniqueness identifies them.
Neither finiteness nor a Noetherian hypothesis on R enters the argument. -/
theorem adicStratificationRingMap_isIso (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : IsIso (adicStratificationRingMap pro R f) := by
  sorry

/-- Actual constant sections of the existing module sheafification, Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationConstantSection (pro : Bool) (R : Type (u + 1)) [CommRing R]
    (X : Scheme.{u}) (M : ModuleCat.{u + 1} R)
    (W : (adicStratificationModel pro X)ᵒᵖ) (m : M) :
    ((SheafOfModules.strictPerfectConstantSheaf
      (adicStratificationModelTopology pro X) R).obj M).val.obj W :=
  (((PresheafOfModules.sheafificationAdjunction.{u + 1, u + 1, u + 1, u + 1}
    (toSheafify (adicStratificationModelTopology pro X)
      ((Functor.const (adicStratificationModel pro X)ᵒᵖ).obj (RingCat.of R)))).unit.app
        ((SheafOfModules.strictPerfectConstantPresheaf
          (C := adicStratificationModel pro X) R).obj M)).app W) m

/-- The uniquely normalized comparison for constant modules, Stacks 093R and proof Steps 5–7.
(blueprint: lem-sfb-adic-finite-stratification-pullback).
Proof: send each constant generator m to the constant section m after base change.
Naturality and R-linearity give a map of constant module presheaves; sheafification and
the module adjunction give c. Uniqueness follows from sheafification's universal property:
every section is locally a constant generator. This specifies actual module maps, with
the scalar action from rho, for arbitrary modules and rings. -/
theorem adicStratificationConstantMap_existsUnique
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleCat.{u + 1} R) :
    ∃! c : (adicStratificationPullback pro R f).obj
        ((SheafOfModules.strictPerfectConstantSheaf
          (adicStratificationModelTopology pro Y) R).obj M) ⟶
        (SheafOfModules.strictPerfectConstantSheaf
          (adicStratificationModelTopology pro X) R).obj M,
      ∀ (W : (adicStratificationModel pro Y)ᵒᵖ) (m : M),
        (((SheafOfModules.pullbackPushforwardAdjunction (adicStratificationRho pro R f)).homEquiv
          _ _ c).val.app W) (adicStratificationConstantSection pro R Y M W m) =
            adicStratificationConstantSection pro R X M
              ((adicStratificationModelBaseChange pro f).op.obj W) m := by
  sorry

/-- The map determined uniquely by its constant sections, Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationConstantMap (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : ModuleCat.{u + 1} R) :=
  Classical.choose (adicStratificationConstantMap_existsUnique pro R f M).exists

/-- Constant-module inverse image is invertible, Stacks 093R and proof Step 7.
(blueprint: lem-sfb-adic-finite-stratification-pullback).
Proof: on underlying sets the comparison is the inverse image of the coproduct of
terminal sheaves indexed by M, identified with the same coproduct on the target site.
The canonical coefficient comparison transports the module structure. The comparison
and its inverse preserve addition and scalar multiplication, as checked on constants
and then locally. This proves invertibility without assuming M finitely presented. -/
theorem adicStratificationConstantMap_isIso
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleCat.{u + 1} R) : IsIso (adicStratificationConstantMap pro R f M) := by
  sorry

/-- Pasting of the original base-change functors, Stacks fibre-product universal property.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationBaseChangeComp (pro : Bool) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    adicStratificationBaseChange pro (f ≫ g) ≅
      adicStratificationBaseChange pro g ⋙ adicStratificationBaseChange pro f :=
  match pro with
  | false => MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g
  | true => MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g

/-- The same fibre-product pasting on the small models, Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationModelBaseChangeComp (pro : Bool) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    adicStratificationModelBaseChange pro (f ≫ g) ≅
      adicStratificationModelBaseChange pro g ⋙ adicStratificationModelBaseChange pro f :=
  Functor.isoWhiskerLeft AsSmall.down
    (Functor.isoWhiskerRight (adicStratificationBaseChangeComp pro f g) AsSmall.up)

/-- Module direct image with the specified scalar action, Stacks 03D1 and 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
abbrev adicStratificationPushforward (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.pushforward.{u + 1} (adicStratificationRho pro R f)

/-- The uniquely specified sectionwise direct-image composition, Stacks 093R, proof Step 7.
(blueprint: lem-sfb-adic-finite-stratification-pullback).
Proof: pullback pasting identifies the two evaluation objects. Restrict sections along
that canonical isomorphism. Naturality gives a map of sheaves, and its inverse comes from
inverse pasting. The rho maps agree on constants, hence on all scalar sections locally;
the comparison is therefore linear. A sheaf map is determined by its section maps,
which proves uniqueness. -/
theorem adicStratificationPushforwardComp_existsUnique
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! e : adicStratificationPushforward pro R f ⋙ adicStratificationPushforward pro R g ≅
        adicStratificationPushforward pro R (f ≫ g),
      ∀ (G : adicStratificationModules pro X R)
        (W : (adicStratificationModel pro Z)ᵒᵖ)
        (x : G.val.obj ((adicStratificationModelBaseChange pro f).op.obj
          ((adicStratificationModelBaseChange pro g).op.obj W))),
        ((e.hom.app G).val.app W) x = G.val.map
          ((adicStratificationModelBaseChangeComp pro f g).hom.app W.unop).op x := by
  sorry

/-- Canonical direct-image pasting, uniquely determined on sections, Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationPushforwardComp (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  Classical.choose (adicStratificationPushforwardComp_existsUnique pro R f g).exists

/-- The inverse-image composition isomorphism, defined as the adjunction mate of the
specified sectionwise direct-image pasting, Stacks 093R and proof Step 7.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationPullbackComp (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    adicStratificationPullback pro R (f ≫ g) ≅
      adicStratificationPullback pro R g ⋙ adicStratificationPullback pro R f :=
  ((conjugateIsoEquiv
    (SheafOfModules.pullbackPushforwardAdjunction (adicStratificationRho pro R (f ≫ g)))
    ((SheafOfModules.pullbackPushforwardAdjunction (adicStratificationRho pro R g)).comp
      (SheafOfModules.pullbackPushforwardAdjunction (adicStratificationRho pro R f)))).symm
        (adicStratificationPushforwardComp pro R f g).symm).symm

/-- Constant sections commute with the specified inverse-image composition,
Stacks 0H7J and 093R, proof Step 7.
(blueprint: lem-sfb-adic-finite-stratification-pullback).
Proof: take adjuncts under the composite module adjunction. Both sides send the
constant generator m to the same constant section m on the iterated fibre product;
the specified pasting identifies that section with the direct pullback section.
Equality follows from the defining uniqueness of the constant-module comparison.
The coefficient maps agree by the identical argument with scalars. -/
theorem adicStratificationConstantMap_comp
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : ModuleCat.{u + 1} R) :
    adicStratificationConstantMap pro R (f ≫ g) M =
      (adicStratificationPullbackComp pro R f g).hom.app
          ((SheafOfModules.strictPerfectConstantSheaf
            (adicStratificationModelTopology pro Z) R).obj M) ≫
        (adicStratificationPullback pro R f).map (adicStratificationConstantMap pro R g M) ≫
          adicStratificationConstantMap pro R f M := by
  sorry

/-- The canonical comparison along a projection whose composite is the stratum map,
Stacks 093R, proof Steps 4 and 7. Equality transport is followed by the adjunction mate.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationProjectionComparison
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {T S X : Scheme.{u}}
    (h : T ⟶ S) (a : S ⟶ X) (q : T ⟶ X) (w : h ≫ a = q)
    (F : adicStratificationModules pro X R) :
    (adicStratificationPullback pro R q).obj F ≅
      (adicStratificationPullback pro R h).obj ((adicStratificationPullback pro R a).obj F) :=
  eqToIso (congrArg (fun k ↦ (adicStratificationPullback pro R k).obj F) w.symm) ≪≫
    (adicStratificationPullbackComp pro R h a).app F

/-- The exact normalization of a pulled-back chosen local trivialization, Stacks 093R.
It says that the local isomorphism agrees, on the inverse-image adjunction unit, with
the given trivialization followed by the canonical constant-module comparison. This
characterizes the localization comparison, including its coefficient identifications.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def AdicStratificationTrivializationCompatibility
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {T S : Scheme.{u}}
    (h : T ⟶ S) (G : adicStratificationModules pro S R)
    (P : adicStratificationModules pro T R)
    (b : P ≅ (adicStratificationPullback pro R h).obj G)
    (V : adicStratificationModel pro S) (M : ModuleCat.{u + 1} R)
    (e : G.over V ≅ ((SheafOfModules.strictPerfectConstantSheaf
      (adicStratificationModelTopology pro S) R).obj M).over V) : Prop :=
  ∃! d : P.over ((adicStratificationModelBaseChange pro h).obj V) ≅
      ((SheafOfModules.strictPerfectConstantSheaf
        (adicStratificationModelTopology pro T) R).obj M).over
          ((adicStratificationModelBaseChange pro h).obj V),
    ∀ (W : Over V) (x : G.val.obj (op W.left)),
      (d.hom.val.app (op ((Over.post (adicStratificationModelBaseChange pro h)).obj W)))
        ((b.inv.val.app (op ((adicStratificationModelBaseChange pro h).obj W.left)))
          ((((SheafOfModules.pullbackPushforwardAdjunction
            (adicStratificationRho pro R h)).unit.app G).val.app (op W.left)) x)) =
        (((SheafOfModules.pullbackPushforwardAdjunction (adicStratificationRho pro R h)).homEquiv
          _ _ (adicStratificationConstantMap pro R h M)).val.app (op W.left))
            ((e.hom.val.app (op W)) x)

/-- The hypotheses of the common-strata lemma, bundled without choosing any new sheaves.
Every cover member has its given constructible locally closed scheme stratification.
Source: Stacks 093R and finite-reductions Step 6.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
structure AdicStratificationInput (pro : Bool) (R : Type (u + 1)) [CommRing R]
    (X : Scheme.{u}) (r : ℕ) where
  /-- The finite family of constant-ring module sheaves. -/
  sheaf : Fin r → adicStratificationModules pro X R
  /-- An unrestricted index set for each given open cover. -/
  coverIndex : Fin r → Type v
  /-- The given open subsets. -/
  opens : ∀ j : Fin r, coverIndex j → X.Opens
  /-- Each family is an open covering, including empty covers of the empty scheme. -/
  covers : ∀ j : Fin r, ⨆ a, opens j a = ⊤
  /-- The given finite constructible locally closed scheme stratifications. -/
  strata : ∀ (j : Fin r) (a : coverIndex j), LocallyClosedStratification (opens j a).toScheme
  /-- The input restrictions are locally constant of finite type over the same ring. -/
  locallyConstant : ∀ (j : Fin r) (a : coverIndex j) (k : Fin (strata j a).n),
    SheafOfModules.IsFiniteTypeLocallyConstant
      (adicStratificationModelTopology pro ((strata j a).domain k)) R
      ((adicStratificationPullback pro R ((strata j a).immersion k ≫ (opens j a).ι)).obj
        (sheaf j))

namespace AdicStratificationInput

variable {pro : Bool} {R : Type (u + 1)} [CommRing R] {X : Scheme.{u}} {r : ℕ}
  (D : AdicStratificationInput.{u, v} pro R X r)

/-- The common open members are exactly all finite intersections of input members.
Source: finite-reductions Step 6 and Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def commonOpen (p : ∀ j : Fin r, D.coverIndex j) : X.Opens :=
  ⨅ j : Fin r, D.opens j (p j)

/-- The finite fibre-product factors: the common open and one original input stratum
for each sheaf, all mapped to X. Its limit is equivalently the product over U of the
strata restricted to U. Source: Stacks fibre products, finite-reductions Step 6.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def productFactors (p : ∀ j : Fin r, D.coverIndex j)
    (a : ∀ j : Fin r, Fin (D.strata j (p j)).n) : Option (Fin r) → Scheme.{u}
  | none => (D.commonOpen p).toScheme
  | some j => (D.strata j (p j)).domain (a j)

/-- The factor maps used by the universal property, Stacks fibre products.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def productArrows (p : ∀ j : Fin r, D.coverIndex j)
    (a : ∀ j : Fin r, Fin (D.strata j (p j)).n) :
    ∀ t : Option (Fin r), D.productFactors p a t ⟶ X
  | none => (D.commonOpen p).ι
  | some j => (D.strata j (p j)).immersion (a j) ≫ (D.opens j (p j)).ι

/-- A finite common stratification with actual product projections and every chosen
trivialization transported canonically with its unchanged module model.
Source: Stacks 093R and the eight proof steps of the common-strata lemma.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
structure CommonRefinement (p : ∀ j : Fin r, D.coverIndex j) where
  /-- A finite constructible locally closed scheme partition of the intersection U. -/
  strata : LocallyClosedStratification (D.commonOpen p).toScheme
  /-- One original stratum for each input partition and each refined stratum. -/
  factor : Fin strata.n → ∀ j : Fin r, Fin (D.strata j (p j)).n
  /-- All the actual projections, including the map to U. -/
  cone : ∀ k : Fin strata.n, WidePullbackCone (D.productArrows p (factor k))
  /-- The cone's scheme is the refined stratum itself. -/
  point : ∀ k : Fin strata.n, (cone k).pt = strata.domain k
  /-- The projection to U is precisely the stratum immersion. -/
  toOpen : ∀ k : Fin strata.n,
    (eqToHom (point k).symm ≫ (cone k).π none) = strata.immersion k
  /-- The actual universal property of the finite fibre product, including projections. -/
  isLimit : ∀ k : Fin strata.n, IsLimit (cone k)
  /-- Discard the empty products when the input family is nonempty. -/
  nonempty : r ≠ 0 → ∀ k : Fin strata.n, Nonempty (strata.domain k)
  /-- For the empty input family retain the identity one-stratum partition, even if X is empty. -/
  emptyFamily : r = 0 → strata.n = 1 ∧ ∀ k : Fin strata.n, IsIso (strata.immersion k)
  /-- The actual projections to the original strata. -/
  projection : ∀ (k : Fin strata.n) (j : Fin r),
    strata.domain k ⟶ (D.strata j (p j)).domain (factor k j)
  /-- These projections are those of the limiting fibre-product cone. -/
  projection_eq : ∀ (k : Fin strata.n) (j : Fin r),
    projection k j = eqToHom (point k).symm ≫ (cone k).π (some j)
  /-- Projection followed by the original stratum map is the common stratum map to X. -/
  projection_comp : ∀ (k : Fin strata.n) (j : Fin r),
    projection k j ≫ ((D.strata j (p j)).immersion (factor k j) ≫
      (D.opens j (p j)).ι) = strata.immersion k ≫ (D.commonOpen p).ι
  /-- Every restriction on the common strata is locally constant of finite type. -/
  locallyConstant : ∀ (k : Fin strata.n) (j : Fin r),
    SheafOfModules.IsFiniteTypeLocallyConstant
      (adicStratificationModelTopology pro (strata.domain k)) R
      ((adicStratificationPullback pro R (strata.immersion k ≫ (D.commonOpen p).ι)).obj
        (D.sheaf j))
  /-- Every chosen covering sieve pulls back to the actual base-changed covering. -/
  coverings : ∀ (k : Fin strata.n) (j : Fin r)
    (W : adicStratificationModel pro ((D.strata j (p j)).domain (factor k j)))
    (S : Sieve W), S ∈ adicStratificationModelTopology pro _ W →
      S.functorPushforward (adicStratificationModelBaseChange pro (projection k j)) ∈
        adicStratificationModelTopology pro (strata.domain k)
          ((adicStratificationModelBaseChange pro (projection k j)).obj W)
  /-- Every chosen local trivialization pulls back with exactly the same finite module;
  the equation in the predicate fixes its constant-ring and composition identifications. -/
  trivializations : ∀ (k : Fin strata.n) (j : Fin r)
    (V : adicStratificationModel pro ((D.strata j (p j)).domain (factor k j)))
    (M : ModuleCat.{u + 1} R), Module.Finite R M →
    ∀ e : (((adicStratificationPullback pro R
      ((D.strata j (p j)).immersion (factor k j) ≫ (D.opens j (p j)).ι)).obj
        (D.sheaf j)).over V) ≅
      ((SheafOfModules.strictPerfectConstantSheaf
        (adicStratificationModelTopology pro ((D.strata j (p j)).domain (factor k j))) R).obj
          M).over V,
      AdicStratificationTrivializationCompatibility pro R (projection k j)
        ((adicStratificationPullback pro R
          ((D.strata j (p j)).immersion (factor k j) ≫ (D.opens j (p j)).ι)).obj (D.sheaf j))
        ((adicStratificationPullback pro R (strata.immersion k ≫ (D.commonOpen p).ι)).obj
          (D.sheaf j))
        (adicStratificationProjectionComparison pro R (projection k j)
          ((D.strata j (p j)).immersion (factor k j) ≫ (D.opens j (p j)).ι)
          (strata.immersion k ≫ (D.commonOpen p).ι) (projection_comp k j) (D.sheaf j)) V M e

end AdicStratificationInput

/-- Finite families have common finite constructible stratifications on exactly the
intersection cover, with actual finite fibre products and canonical transport of every
chosen local trivialization over an arbitrary coefficient ring, on either site.
Source: Stacks 093R; finite-reductions Step 6.
(blueprint: lem-sfb-adic-finite-stratification-pullback).

Proof:
1. For r=0 use X and its identity stratum, including X empty. For r>0 the intersections
of members of the finitely many given open covers cover X, by choosing a member through
each point for each input cover.
2. Restrict each input stratification to an intersection U by scheme fibre products
(lemma-constructible-pullback-stratification). Images are constructible by
lem-pur-scheme-constructible-preimage, without any quasi-compactness hypothesis on U.
3. Inductively pull back the next partition to each current stratum. Composition of
immersions is an immersion (lem-weil-pbc-proper-fp-permanence). Its image is the
intersection of the two images, since immersions are injective on underlying points.
The resulting finite partition is disjoint and covers U.
4. Finite intersections remain constructible. Remove empty products when r>0; the
fibre-product universal property gives all actual projection maps and their equations.
5. The coefficient comparison is adjoint to constant sections. It is invertible by
lem-pe-constant-left-module-inverse-image, and agrees with the specified scalar map
because both adjuncts fix constants. Etale inverse image uses its algebraic-structure
lift; pro-etale inverse image uses the recorded geometric inverse image.
6. Pull each chosen covering back along each actual projection. Etale covering base
change and weakly etale/fpqc base change prove it is a covering on the chosen site.
Localize the ringed-site morphism (lem-weil-pbc-localize-ringed-site-morphism) and
apply lem-sfb-geometric-inverse-image-constant-module to the given trivialization.
Its model is the same R-module M with the same finite generating list.
7. The constant comparison is fixed on every generator m. Direct comparison and
two successive comparisons therefore agree under the canonical composition mate.
The normalization equation in AdicStratificationTrivializationCompatibility expresses
exactly this compatibility, with uniqueness by the localized module adjunction.
8. Apply these constructions to all strata and sheaves. The covering-sieve definition
of IsFiniteTypeLocallyConstant gives the asserted common locally constant restrictions.
Neither R nor its underlying set needs to be finite, and no Noetherian assumption enters.
-/
theorem adic_finite_stratification_pullback
    (pro : Bool) (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) (r : ℕ)
    (D : AdicStratificationInput.{u, v} pro R X r) :
    (⨆ p : (∀ j : Fin r, D.coverIndex j), D.commonOpen p) = ⊤ ∧
      ∀ p : (∀ j : Fin r, D.coverIndex j), Nonempty (D.CommonRefinement p) := by
  sorry

end AlgebraicGeometry.Scheme
