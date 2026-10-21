/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Sheaf.CategoryTheory.RingedPresentationData
public import Sheaf.CategoryTheory.SheafSubcategoryComparison
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.TraceFormula.SieveSheavesCoveringSite
import Sheaf.CategoryTheory.SiteOfSheafGenerators
import Sheaf.CategoryTheory.SmallSetOfCoveringFamilies
import Sheaf.CategoryTheory.RingedToposEquivalenceRingTransport
import Sheaf.CategoryTheory.RingedPresentationTransport
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# A simultaneous site presentation for a binary subterminal cover

Source: Stacks Project, Sites, Tags 03A1, 03CI, 00Y1, 04GZ and 03EH;
Modules on Sites, Tags 03CR, 03D7, 04IE and 04J4
(blueprint: lem-sp-binary-cover-site-presentation).

The four indices are `0 = 1`, `1 = U`, `2 = V`, `3 = U × V`.
Internal commutative rings are encoded by their section-ring sheaves, as in the recorded
sectionwise reconstruction theorem. The source slice modules are encoded on the existing
category-of-elements site; the target slices use the actual localized topology `J.over`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The exact module equivalence induced by a specified ringed equivalence, together with
its termwise induced ordinary derived equivalence. The underlying-set and rank-one equations
fix the scalar action; the inverse is the specified module direct image.
Source: Stacks 03CR, 03D7 and 05RU
(blueprint: lem-sp-binary-cover-site-presentation). -/
structure BinaryPresentationModules
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (g : RingedToposMorphism (localCoefficientRings S) (localCoefficientRings R)) where
  modules : PresentationModules R ≌ PresentationModules S
  additive : modules.functor.Additive
  inverseAdditive : modules.inverse.Additive
  finiteLimits : PreservesFiniteLimits modules.functor
  finiteColimits : PreservesFiniteColimits modules.functor
  inverseFiniteLimits : PreservesFiniteLimits modules.inverse
  inverseFiniteColimits : PreservesFiniteColimits modules.inverse
  underlying : modules.functor ⋙ presentationForget S ≅ presentationForget R ⋙ g.inverse
  unit : modules.functor.obj (SheafOfModules.unit (localCoefficientRings R)) ≅
    SheafOfModules.unit (localCoefficientRings S)
  structural : (presentationForget S).map unit.hom =
    underlying.hom.app (SheafOfModules.unit (localCoefficientRings R)) ≫ g.ringMap
  pushforward : modules.inverse ≅ g.modules
  derived : PresentationDerived R ≌ PresentationDerived S
  derivedFunctor : derived.functor =
    presentationDerivedMap modules.functor additive finiteLimits finiteColimits
  derivedInverse : derived.inverse = presentationDerivedMap modules.inverse inverseAdditive
    inverseFiniteLimits inverseFiniteColimits

/-- A restriction square preserves both adjunctions by their actual mates. Invertibility of
these mates says precisely that the adjoints are identified compatibly with units and counits,
rather than merely giving isomorphic endpoints.
Source: Stacks Categories, Tag 0B65; Sites, Tag 03EH
(blueprint: lem-sp-binary-cover-site-presentation). -/
structure BinaryPresentationAdjointSquare
    {A B A' B' : Type (u + 1)}
    [Category.{u} A] [Category.{u} B] [Category.{u} A'] [Category.{u} B']
    (E : A ≌ A') (E' : B ≌ B') (F : A ⥤ B) (F' : A' ⥤ B') where
  comparison : F ⋙ E'.functor ≅ E.functor ⋙ F'
  rightMate : ∀ (G : B ⥤ A) (G' : B' ⥤ A') (a : F ⊣ G) (a' : F' ⊣ G'),
    IsIso ((mateEquiv a a' (TwoSquare.mk _ _ _ _ comparison.inv)).natTrans)
  leftMate : ∀ (L : B ⥤ A) (L' : B' ⥤ A') (a : L ⊣ F) (a' : L' ⊣ F'),
    IsIso (((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ comparison.hom)).natTrans)

/-- All witnesses for one small finite-limit-closed presenting subcategory and the four
simultaneous ringed slices. Full faithfulness realizes the small category as a full
subcategory, with chosen representatives of its objects.
Source: Stacks Sites, Tags 03A1, 03CI and 00Y1; Modules on Sites, 03CR
(blueprint: lem-sp-binary-cover-site-presentation). -/
structure BinaryCoverSitePresentation
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U V : Sheaf J (Type u)) where
  E : Type u
  [category : SmallCategory E]
  [finiteLimits : HasFiniteLimits E]
  inclusion : E ⥤ Sheaf J (Type u)
  [full : inclusion.Full]
  [faithful : inclusion.Faithful]
  [preservesLimits : PreservesFiniteLimits inclusion]
  generators : ∀ X : C, ∃ Y : E,
    Nonempty (inclusion.obj Y ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj X))
  objects : Fin 4 → E
  terminal : inclusion.obj (objects 0) ≅ ⊤_ (Sheaf J (Type u))
  first : inclusion.obj (objects 1) ≅ U
  second : inclusion.obj (objects 2) ≅ V
  intersection : inclusion.obj (objects 3) ≅ U ⨯ V
  covers : Precoverage E
  site : covers.IsSiteForCoverings
  [subcanonical : covers.toGrothendieck.Subcanonical]
  epimorphic : ∀ (X : E) (P : PreZeroHypercover.{u} X),
    P.presieve₀ ∈ covers X ↔
      ⟨X, P⟩ ∈ sheafSubcategoryEpimorphicFamilies.{u, u, 0} inclusion
  representatives : Set (Σ X : E, PreZeroHypercover.{u} X)
  smallRepresentatives : Small.{u} representatives
  coveringClass : PreZeroHypercover.IsCoveringClass representatives
  representativeCovers : ∀ (X : E) (P : PreZeroHypercover.{u} X),
    ⟨X, P⟩ ∈ representatives → P.presieve₀ ∈ covers X
  sameSupports : ∀ (X : E) (P : PreZeroHypercover.{u} X), P.presieve₀ ∈ covers X →
    ∃ Q : PreZeroHypercover.{u} X, ⟨X, Q⟩ ∈ representatives ∧ P.presieve₀ = Q.presieve₀
  binaryCover : ∀ X : E,
    Presieve.ofArrows (fun b : Bool ↦ X ⨯ objects (if b then 1 else 2))
      (fun _b ↦ prod.fst : ∀ b : Bool, X ⨯ objects (if b then 1 else 2) ⟶ X) ∈ covers X
  nerve : Sheaf J (Type u) ≌ Sheaf covers.toGrothendieck (Type u)
  nerveFormula : nerve.functor ⋙ sheafToPresheaf covers.toGrothendieck (Type u) ≅
    sheafSubcategoryNerve inclusion
  represented : ∀ X : E, Nonempty (nerve.functor.obj (inclusion.obj X) ≅
    covers.toGrothendieck.yoneda.obj X)
  ring : Sheaf covers.toGrothendieck CommRingCat.{u}
  ringed : RingedToposMorphism (localCoefficientRings ring) (localCoefficientRings R)
  inverseNerve : ringed.inverse = nerve.functor
  directNerve : ringed.direct = nerve.inverse
  ringIsIso : IsIso ringed.ringMap
  wholeModules : BinaryPresentationModules ringed
  sourceSlice : ∀ i : Fin 4,
    RingedSheafSliceAdjunctionData (localCoefficientRings R) (inclusion.obj (objects i))
  slice : ∀ i : Fin 4,
    Over (inclusion.obj (objects i)) ≌ Sheaf (covers.toGrothendieck.over (objects i)) (Type u)
  sliceFormula : ∀ i : Fin 4,
    (slice i).functor ⋙ sheafToPresheaf (covers.toGrothendieck.over (objects i)) (Type u) ≅
      yoneda ⋙ (Functor.whiskeringLeft (Over (objects i))ᵒᵖ
        (Over (inclusion.obj (objects i)))ᵒᵖ (Type u)).obj (Over.post inclusion).op
  sliceRinged : ∀ i : Fin 4,
    RingedToposMorphism (localCoefficientRings (ring.over (objects i)))
      (localCoefficientRings (presentationElementRing R (inclusion.obj (objects i))))
  sliceInverse : ∀ i : Fin 4, Nonempty ((sliceRinged i).inverse ≅
    (sourceSlice i).fibreEquivalence.functor ⋙ (slice i).functor)
  sliceRingIsIso : ∀ i : Fin 4, IsIso (sliceRinged i).ringMap
  sliceModules : ∀ i : Fin 4, BinaryPresentationModules (sliceRinged i)
  sourceContinuous : ∀ (i j : Fin 4) (f : objects i ⟶ objects j),
    Functor.IsContinuous (elementMap (inclusion.map f))
      (elementTopology (inclusion.obj (objects i)))
      (elementTopology (inclusion.obj (objects j)))
  restriction : ∀ i : Fin 4, BinaryPresentationAdjointSquare
    wholeModules.modules (sliceModules i).modules
    (elementModulePullback.{u, u} (localCoefficientRings R) (inclusion.obj (objects i)))
    (SheafOfModules.overFunctor.{u} (localCoefficientRings ring) (objects i))

  further : ∀ (i j : Fin 4) (f : objects i ⟶ objects j),
    BinaryPresentationAdjointSquare (sliceModules j).modules (sliceModules i).modules
      (elementModulePullbackOver.{u, u} (localCoefficientRings R) (inclusion.map f)
        (sourceContinuous i j f))
      (SheafOfModules.overMap.{u} (localCoefficientRings ring) f)

  restrictionComposition : ∀ (i j : Fin 4) (f : objects i ⟶ objects j)
      (M : PresentationModules R),
    HEq ((restriction i).comparison.hom.app M)
      ((further i j f).comparison.hom.app
          ((elementModulePullback.{u, u} (localCoefficientRings R)
            (inclusion.obj (objects j))).obj M) ≫
        (SheafOfModules.overMap.{u} (localCoefficientRings ring) f).map
          ((restriction j).comparison.hom.app M) ≫
        (SheafOfModules.overFunctorMap.{u} (localCoefficientRings ring) f).hom.app
          (wholeModules.modules.functor.obj M))
  furtherIdentity : ∀ (i : Fin 4)
      (M : PresentationModules (presentationElementRing R (inclusion.obj (objects i)))),
    HEq ((further i i (𝟙 (objects i))).comparison.hom.app M)
      (𝟙 ((sliceModules i).modules.functor.obj M))
  furtherComposition : ∀ (i j k : Fin 4) (f : objects i ⟶ objects j)
      (g : objects j ⟶ objects k)
      (M : PresentationModules (presentationElementRing R (inclusion.obj (objects k)))),
    HEq ((further i k (f ≫ g)).comparison.hom.app M)
      ((further i j f).comparison.hom.app
          ((elementModulePullbackOver.{u, u} (localCoefficientRings R) (inclusion.map g)
            (sourceContinuous j k g)).obj M) ≫
        (SheafOfModules.overMap.{u} (localCoefficientRings ring) f).map
          ((further j k g).comparison.hom.app M))

/-- A binary subterminal cover has one simultaneous small subcanonical site presentation,
with the nerve, its four slice nerves, exact module equivalences and ordinary derived
comparisons, preserving the adjunctions by their canonical mates.

Source: Stacks Sites, Tags 03A1 and 03CI, with the simultaneous ringed extension described
in the node; Tags 00Y1, 04GZ and 03EH for slices
(blueprint: lem-sp-binary-cover-site-presentation).

Proof:
1. Replace the sieve site by a covering-family site using
   `lem-trf-sieve-sheaves-covering-site`. Sheafify the original representables using
   `lem-trf-sieve-set-sheafification-exists`.
2. Start with the original generators, the replacement-site generators and 1,U,V,U×V.
   Adjoin terminal objects and pullbacks at each natural-number stage. Each stage is small;
   each finite diagram lies in some stage. Sectionwise limits, transported through the
   replacement equivalence, give finite limits and their preservation by the inclusion.
3. Apply `lem-weil-pbc-site-of-sheaf-generators`. Full faithfulness identifies its nerve with
   Hom in the original topos. This makes every representable a sheaf. Joint epimorphy is
   preserved and reflected by an equivalence, so the covers have the stated description.
4. The local union hypothesis says the terminal section locally lifts to U or V. Any two
   maps agreeing on both product projections therefore agree locally on every section,
   and separatedness makes them equal. These binary families are epimorphic and cover.
5. Choose a small covering class retaining these families using
   `lem-weil-pbc-small-set-of-covering-families`; the supports and topology do not change.
6. Apply `lem-weil-pbc-localized-sheaves-over-representable` to the four represented
   objects. The slice nerve is the fibre of Hom(C,B) → Hom(C,Z) over the structure map.
7. Restriction sends a lift (b,c') in a pullback to b, with inverse b ↦ (b,c'). Two successive
   restrictions and the direct restriction select the same b. Identities do also. Ring
   operations are computed on this component, identifying the restricted rings.
8. Use `lem-weil-pbc-sheaf-ring-object-sectionwise-reconstruction` and
   `lem-weil-pbc-ringed-topos-equivalence-ring-transport` for the whole and slice rings.
9. Apply `lem-weil-pbc-ringed-presentation-transport` and
   `lem-weil-pbc-ringed-sheaf-slice-adjunction` to obtain the exact module equivalences,
   their underlying comparisons, and their termwise ordinary derived equivalences.
10. The restriction comparisons send (m,c') to m, preserving addition and scalar action.
    They obey the preceding composition equations on complexes and after localization.
    Additive exact functors preserve the cone matrix and shift, hence distinguished triangles.
11. Identify right and left adjoints by `det-sp-unique-right-adjoint` and
    `lem-weil-pbc-conjugate-iso-unit-equation`. Their mates preserve the units and counits.
    In `def-weil-pbc-adjunction-mate`, each of the unit, comparison and counit factors
    transports to its corresponding factor, so nested-localization mates are preserved.
-/
theorem exists_binaryCoverSitePresentation
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U V : Sheaf J (Type u))
    (hU : IsSubterminal U) (hV : IsSubterminal V)
    (hcover : ∀ X : C,
      Sieve.generate (fun (Y : C) (_ : Y ⟶ X) ↦
        Nonempty (U.obj.obj (op Y)) ∨ Nonempty (V.obj.obj (op Y))) ∈ J X) :
    Nonempty (BinaryCoverSitePresentation J R U V) := by
  sorry

end CategoryTheory
