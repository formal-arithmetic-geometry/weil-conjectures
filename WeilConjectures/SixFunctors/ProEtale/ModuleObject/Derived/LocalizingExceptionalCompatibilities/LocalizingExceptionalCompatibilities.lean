/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.Monoidal.CommMon_
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullbackDefinitions
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.InverseImageModuleFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.Compactification.BoundaryRefinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Canonical compatibilities of the localizing exceptional inverse image

Source: latest blueprint, sec-six-functors-basics/sk-lem-sf-mate, clauses (1)--(4)
and the final locality assertion (blueprint: sk-lem-sf-mate).

The parameters `c`, `G`, and `adj` are any chosen compactifications and the right
adjoints supplied by sk-prop-sf-existence. The parameter `H` is the recorded coherent
compact-support comparison datum of sk-thm-sf-comp-composition. Thus the maps below
are mates of its specified comparisons, not choices of isomorphisms of functors.
All categories are the ordinary, uncompleted localizing closures of Dctf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing
namespace LocalizingExceptionalCompatibilities

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k]
  (H : CompactSupportComposition.CoherentData Λ k)

/-- The actual compactification lower shriek restricted using H's preservation proof.
Source: sk-prop-sf-existence, definition of Rf! (blueprint: sk-lem-sf-mate). -/
def lower {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left) :=
  localizingLowerShriek Λ c (H.preserves f c).1

/-- Lift the specified compact-support comparison through the full localizing inclusion.
Source: sk-thm-sf-comp-composition, independence (blueprint: sk-lem-sf-mate). -/
def lowerComparison {X Y : SepFinType k} (f : X ⟶ Y)
    (c d : Compactification f.hom.left) : lower Λ k H f c ≅ lower Λ k H f d :=
  NatIso.ofComponents
    (fun K ↦ (localizingClosureProEtale Λ Y.obj.left).isoMk ((H.comparison f c d).app K))
    (fun b ↦ ObjectProperty.hom_ext _ ((H.comparison f c d).hom.naturality b))

/-- Lift the canonical left compositor; no ambient exceptional adjoint is used.
Source: sk-lem-sf-mate proof (1), alpha (blueprint: sk-lem-sf-mate). -/
def lowerComposition {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactification f.hom.left) (d : Compactification g.hom.left)
    (e : Compactification (f.hom.left ≫ g.hom.left)) :
    lower Λ k H f c ⋙ lower Λ k H g d ≅ lower Λ k H (f ≫ g) e :=
  NatIso.ofComponents
    (fun K ↦ (localizingClosureProEtale Λ Z.obj.left).isoMk ((H.comp f g c d e).app K))
    (fun b ↦ ObjectProperty.hom_ext _ ((H.comp f g c d e).hom.naturality b))

/-- Ordinary inverse image restricted to the same localizing categories. For an open
immersion its exact derived presentation is canonically the usual open restriction.
Source: clauses (2)--(4), j* (blueprint: sk-lem-sf-mate). -/
def pullback {X Y : SepFinType k} (f : X ⟶ Y) :
    (localizingClosureProEtale Λ Y.obj.left).FullSubcategory ⥤
      (localizingClosureProEtale Λ X.obj.left).FullSubcategory :=
  (localizingClosureProEtale Λ X.obj.left).lift
    ((localizingClosureProEtale Λ Y.obj.left).ι ⋙ moduleObjectDerivedPullback Λ f.hom.left)
    (fun K ↦ (H.pullback_preserves X Y f.hom.left).1 K.obj K.property)

variable
  (c : ∀ {X Y : SepFinType k} (f : X ⟶ Y), Compactification f.hom.left)
  (G : ∀ {X Y : SepFinType k} (_f : X ⟶ Y),
    (localizingClosureProEtale Λ Y.obj.left).FullSubcategory ⥤
      (localizingClosureProEtale Λ X.obj.left).FullSubcategory)
  (adj : ∀ {X Y : SepFinType k} (f : X ⟶ Y), lower Λ k H f (c f) ⊣ G f)

/-- The right mate of the canonical compact-support compositor. It is selected by the
pasted counit equation, with the composite adjunction of sk-lem-sf-mate proof (1).
Source: clause (1) and proof (1) (blueprint: sk-lem-sf-mate). -/
def composition {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    G (f ≫ g) ≅ G g ⋙ G f :=
  conjugateIsoEquiv (adj (f ≫ g)) ((adj f).comp (adj g))
    (lowerComposition Λ k H f g (c f) (c g) (c (f ≫ g)))

/-- Transport of the exceptional functor under equality of scheme morphisms.
Source: proof (3), substitution fu = vf_V (blueprint: sk-lem-sf-mate). -/
def congr {X Y : SepFinType k} {f g : X ⟶ Y} (h : f = g) : G f ≅ G g :=
  eqToIso (congrArg G h)

/-- The compact-support identity map, transported from the trivial identity model.
Source: proof (1), unital left comparisons (blueprint: sk-lem-sf-mate). -/
def lowerIdentity (X : SepFinType k) : lower Λ k H (𝟙 X) (c (𝟙 X)) ≅ 𝟭 _ :=
  lowerComparison Λ k H (𝟙 X) (c (𝟙 X))
      (Compactification.ofIsProper (𝟙 X.obj.left)) ≪≫
    NatIso.ofComponents
      (fun K ↦ (localizingClosureProEtale Λ X.obj.left).isoMk
        ((CompactSupportComposition.identity Λ X.obj.left).app K.obj))
      (fun b ↦ ObjectProperty.hom_ext _
        ((CompactSupportComposition.identity Λ X.obj.left).hom.naturality b.hom))

/-- The canonical identity identification, the conjugate of the left identity map.
Source: clause (1), identity compatibility (blueprint: sk-lem-sf-mate). -/
def identity (X : SepFinType k) : G (𝟙 X) ≅ 𝟭 _ :=
  conjugateIsoEquiv (adj (𝟙 X)) Adjunction.id (lowerIdentity Λ k H c X).symm

/-- Restrict the actual open-extension adjunction and compare its trivial compactification
with the chosen one. The right functor is the ordinary derived open pullback.
Source: clause (2), open adjunction (blueprint: sk-lem-sf-mate). -/
def openAdjunction {U X : SepFinType k} (j : U ⟶ X) [IsOpenImmersion j.hom.left] :
    lower Λ k H j (c j) ⊣ pullback Λ k H j :=
  (((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.hom.left).ofNatIsoLeft
      (mateOpenTrivialLowerShriek Λ j.hom.left).symm).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory Λ j.hom.left).symm).restrictFullyFaithful
          (localizingClosureProEtale Λ U.obj.left).fullyFaithfulι
          (localizingClosureProEtale Λ X.obj.left).fullyFaithfulι (Iso.refl _) (Iso.refl _)
    |>.ofNatIsoLeft (lowerComparison Λ k H j
      (Compactification.ofIsOpenImmersion j.hom.left) (c j))

/-- The unique adjunction-compatible identification j! = j* on the localizing categories.
Source: clause (2) and proof (2) (blueprint: sk-lem-sf-mate). -/
def openIso {U X : SepFinType k} (j : U ⟶ X) [IsOpenImmersion j.hom.left] :
    G j ≅ pullback Λ k H j :=
  (adj j).rightAdjointUniq (openAdjunction Λ k H c j)

/-- The target-open comparison is the composite through the two factorizations of the
same morphism. This is exactly the chain in proof (3), with its equality substitution.
Source: clause (3), Cartesian open square (blueprint: sk-lem-sf-mate). -/
def targetOpenIso {U V X Y : SepFinType k}
    (a : U ⟶ X) (q : U ⟶ V) (f : X ⟶ Y) (v : V ⟶ Y)
    [IsOpenImmersion a.hom.left] [IsOpenImmersion v.hom.left]
    (sq : IsPullback a q f v) :
    G f ⋙ pullback Λ k H a ≅ pullback Λ k H v ⋙ G q :=
  Functor.isoWhiskerLeft (G f) (openIso Λ k H c G adj a).symm ≪≫
    (composition Λ k H c G adj a f).symm ≪≫ congr Λ k G sq.w ≪≫
      composition Λ k H c G adj q v ≪≫
        Functor.isoWhiskerRight (openIso Λ k H c G adj v) (G q)

/-- Source-open restriction, using the same composition and open comparisons.
Source: final locality assertion and proof (3) (blueprint: sk-lem-sf-mate). -/
def sourceOpenIso {U X Y : SepFinType k} (j : U ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion j.hom.left] : G f ⋙ pullback Λ k H j ≅ G (j ≫ f) :=
  Functor.isoWhiskerLeft (G f) (openIso Λ k H c G adj j).symm ≪≫
    (composition Λ k H c G adj j f).symm

/-- The open factor of an arbitrary compactification, as a morphism in the standing
category; the middle scheme is the recorded overObj, not a newly chosen scheme.
Source: clause (4), compactification data (blueprint: sk-lem-sf-mate). -/
abbrev compactificationOpen {X Y : SepFinType k} {f : X ⟶ Y}
    (d : Compactification.BoundaryCompactification f.hom.left) :
    X ⟶ SepFinType.mk (d.obj.obj.overObj (f := f.hom)) :=
  ObjectProperty.homMk d.obj.obj.overI

/-- The proper factor of that same compactification over k.
Source: clause (4), compactification data (blueprint: sk-lem-sf-mate). -/
abbrev compactificationProper {X Y : SepFinType k} {f : X ⟶ Y}
    (d : Compactification.BoundaryCompactification f.hom.left) :
    SepFinType.mk (d.obj.obj.overObj (f := f.hom)) ⟶ Y :=
  ObjectProperty.homMk d.obj.obj.overG

/-- The properness stored in the given compactification, exposed for its factor in
the full over-field category. Its underlying map is exactly the original proper map.
Source: clause (4), compactification data (blueprint: sk-lem-sf-mate). -/
instance isProper_compactificationProper {X Y : SepFinType k} {f : X ⟶ Y}
    (d : Compactification.BoundaryCompactification f.hom.left) :
    IsProper (compactificationProper k d).hom.left :=
  d.obj.obj.isProper

/-- The identity-open compactification of a proper map computes its actual derived
pushforward, using the normalized identity extension.
Source: proof (4), Rp! = Rp* (blueprint: sk-lem-sf-mate). -/
def properTrivial {T Y : SepFinType k} (p : T ⟶ Y) [IsProper p.hom.left] :
    rightDerivedLowerShriekOfCompactification Λ (Compactification.ofIsProper p.hom.left) ≅
      (lowerStar Λ p.hom.left).rightDerivedFunctor :=
  Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId Λ T.obj.left) _ ≪≫
    Functor.leftUnitor _

/-- The actual Rp* on the localizing closure. Its preservation proof is transported
from the identity-open compactification, without choosing a new functor.
Source: proof (4), the proper factor (blueprint: sk-lem-sf-mate). -/
def properImage {T Y : SepFinType k} (p : T ⟶ Y) [IsProper p.hom.left] :
    (localizingClosureProEtale Λ T.obj.left).FullSubcategory ⥤
      (localizingClosureProEtale Λ Y.obj.left).FullSubcategory :=
  (localizingClosureProEtale Λ Y.obj.left).lift
    ((localizingClosureProEtale Λ T.obj.left).ι ⋙ (lowerStar Λ p.hom.left).rightDerivedFunctor)
    (fun K P hP hS ↦
      letI := hP.2.1
      P.prop_of_iso ((properTrivial Λ k p).app K.obj)
        ((H.preserves p (Compactification.ofIsProper p.hom.left)).1 K.obj K.property P hP hS))

/-- Identify any chosen proper compact-support model with actual Rp*, by the
specified compactification comparison and the normalized identity-open model.
Source: proof (4), independence of the proper model (blueprint: sk-lem-sf-mate). -/
def properImageComparison {T Y : SepFinType k} (p : T ⟶ Y) [IsProper p.hom.left]
    (d : Compactification p.hom.left) : lower Λ k H p d ≅ properImage Λ k H p :=
  lowerComparison Λ k H p d (Compactification.ofIsProper p.hom.left) ≪≫
    NatIso.ofComponents
      (fun K ↦ (localizingClosureProEtale Λ Y.obj.left).isoMk
        ((properTrivial Λ k p).app K.obj))
      (fun b ↦ ObjectProperty.hom_ext _ ((properTrivial Λ k p).hom.naturality b.hom))

/-- The left comparison for the direct compactification adjunction: identify the
chosen open compact support with j!, then Rp* j! with the given compactification,
then compare that model with the chosen one for f. No composition theorem is used.
Source: proof (4), Rf! = Rp* j! (blueprint: sk-lem-sf-mate). -/
def compactificationLeftComparison {X Y : SepFinType k} (f : X ⟶ Y)
    (d : Compactification.BoundaryCompactification f.hom.left) :
    lower Λ k H (compactificationOpen k d) (c (compactificationOpen k d)) ⋙
        properImage Λ k H (compactificationProper k d) ≅ lower Λ k H f (c f) :=
  let e := Functor.isoWhiskerRight
    (H.comparison (compactificationOpen k d) (c (compactificationOpen k d))
        (Compactification.ofIsOpenImmersion d.obj.obj.i) ≪≫
      Functor.isoWhiskerLeft (localizingClosureProEtale Λ X.obj.left).ι
        (mateOpenTrivialLowerShriek Λ d.obj.obj.i))
    (lowerStar Λ d.obj.obj.g).rightDerivedFunctor ≪≫
      Functor.associator _ _ _ ≪≫ H.comparison f d.obj.obj (c f)
  NatIso.ofComponents
    (fun K ↦ (localizingClosureProEtale Λ Y.obj.left).isoMk (e.app K))
    (fun b ↦ ObjectProperty.hom_ext _ (e.hom.naturality b))

/-- The compactification formula from the composite j! adjunction j* and Rp*
adjunction p!, compared directly with the given adjunction of f. All left
comparisons pass through the given Rp* j! model, not through a compositor.
Source: clause (4) and proof (4) (blueprint: sk-lem-sf-mate). -/
def compactificationIso {X Y : SepFinType k} (f : X ⟶ Y)
    (d : Compactification.BoundaryCompactification f.hom.left) :
    G f ≅ G (compactificationProper k d) ⋙ pullback Λ k H (compactificationOpen k d) :=
  conjugateIsoEquiv (adj f)
    ((openAdjunction Λ k H c (compactificationOpen k d)).comp
      ((adj (compactificationProper k d)).ofNatIsoLeft
        (properImageComparison Λ k H (compactificationProper k d)
          (c (compactificationProper k d)))))
    (compactificationLeftComparison Λ k H c f d)

/-- The comparisons above are associative and unital. Together with sourceOpenIso and
targetOpenIso, detection of isomorphisms by arbitrary open covers says precisely that
f! can be computed locally on both source and target.
Source: sk-lem-sf-mate (1)--(4), final sentence, and its proof (1)--(4)
(blueprint: sk-lem-sf-mate).

Proof:
1. For each f, the given adjunction is the one on Loc supplied by sk-prop-sf-existence.
   The compositor is the right mate of H.comp. Composite adjunctions paste their
   counits as epsilon_g after F_g(epsilon_f). Uniqueness of the right adjoint fixes
   precisely composition, including its naturality and counit normalization.
2. Apply mate-pasting to the associativity and identity laws of H. Injectivity of
   conjugation gives the three displayed coherence equations, with the functor
   associator and the equalities of composite scheme morphisms inserted.
3. The exact open-extension/pullback adjunction restricts to Loc. Transport it along
   H.comparison to the chosen compactification. Right-adjoint uniqueness gives openIso.
4. In a target-open Cartesian square, a f = q v. Substitute this equality between
   the two composition comparisons and use openIso for a and v: this is targetOpenIso.
   For a source open this gives sourceOpenIso. For a compactification f = p j,
   compose the restricted j! adjunction j* with Rp! adjunction p!. The normalized
   compactification comparison identifies its left functor Rp* j! with Rf!. Conjugation
   compares this composite adjunction directly to adj f, giving compactificationIso.
   In each case these definitions contain the actual maps.
5. Exact open restrictions detect isomorphisms of derived module objects because
   they detect zero cohomology sheaves. Apply sourceOpenIso to each source open and
   targetOpenIso to each member of an inverse-image target cover. This includes
   empty schemes, identity opens, zero objects, and arbitrary unbounded objects.
-/
theorem coherence_and_locality
    (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime] [CharP k p]
    (_hpℓ : p ≠ ℓ) (_hcd : BaseFieldFiniteCD ℓ k)
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    (∀ {X Y Z W : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W),
      composition Λ k H c G adj (f ≫ g) h ≪≫
          Functor.isoWhiskerLeft (G h) (composition Λ k H c G adj f g) =
        congr Λ k G (Category.assoc f g h) ≪≫
          composition Λ k H c G adj f (g ≫ h) ≪≫
          Functor.isoWhiskerRight (composition Λ k H c G adj g h) (G f) ≪≫
          Functor.associator (G h) (G g) (G f)) ∧
    (∀ {X Y : SepFinType k} (f : X ⟶ Y),
      composition Λ k H c G adj (𝟙 X) f ≪≫
          Functor.isoWhiskerLeft (G f) (identity Λ k H c G adj X) ≪≫
          Functor.rightUnitor (G f) = congr Λ k G (Category.id_comp f)) ∧
    (∀ {X Y : SepFinType k} (f : X ⟶ Y),
      composition Λ k H c G adj f (𝟙 Y) ≪≫
          Functor.isoWhiskerRight (identity Λ k H c G adj Y) (G f) ≪≫
          Functor.leftUnitor (G f) = congr Λ k G (Category.comp_id f)) ∧
    (∀ (X : SepFinType k) (I : Type w) (U : I → X.obj.left.Opens), iSup U = ⊤ →
      ∀ {K L : (localizingClosureProEtale Λ X.obj.left).FullSubcategory} (b : K ⟶ L),
        (∀ i, IsIso ((upperStar Λ (U i).ι).mapDerivedCategory.map b.hom)) → IsIso b) := by
  sorry

end LocalizingExceptionalCompatibilities
end AlgebraicGeometry.ProEtale.CondensedRing
