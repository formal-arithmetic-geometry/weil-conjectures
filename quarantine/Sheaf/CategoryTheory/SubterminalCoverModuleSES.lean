module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-! # The module short exact sequence of a binary subterminal cover

Source: Stacks Project, Cohomology, Tag 08BU, lemma-exact-sequence-lower-shriek;
the subterminal-site formulation is the local split calculation in the blueprint
(blueprint: lem-sp-subterminal-cover-module-ses).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe c v r
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.SubterminalCover

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- Forget only commutativity of the given coefficient sheaf. Source: Stacks 08BU
(blueprint: lem-sp-subterminal-cover-module-ses). -/
abbrev ring : Sheaf J RingCat.{max c v r} :=
  (sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R

/-- The recorded category of modules over the given ring sheaf. Source: Stacks 08BU
(blueprint: lem-sp-subterminal-cover-module-ses). -/
abbrev modules := ringedSiteModules.{max c v r} (ring.{c, v, r} R)

/-- The composite `j_Z! j_Z*`, using the actual sheafified direct-sum extension.
Source: Stacks 08BU (blueprint: lem-sp-subterminal-cover-module-ses). -/
abbrev supported (Z : C) : modules.{c, v, r} R ⥤ modules.{c, v, r} R :=
  localizedSystemRestriction.{c, v, r} R Z ⋙ localizedSystemExtension.{c, v, r} R Z

/-- The canonical adjunction counit. Source: Stacks 08BU
(blueprint: lem-sp-subterminal-cover-module-ses). -/
def counit (Z : C) (F : modules.{c, v, r} R) : (supported.{c, v, r} R Z).obj F ⟶ F :=
  (localizedSystemAdjunction.{c, v, r} R Z).counit.app F

/-- The nested-open map is the transpose of the restricted unit, using the sectionwise
iterated-restriction comparison. Source: Stacks 08BU
(blueprint: lem-sp-subterminal-cover-module-ses). -/
def nested [HasPullbacks C] {W Z : C} (f : W ⟶ Z) (F : modules.{c, v, r} R) :
    (supported.{c, v, r} R W).obj F ⟶ (supported.{c, v, r} R Z).obj F :=
  ((localizedSystemAdjunction.{c, v, r} R W).homEquiv _ _).symm
    ((overFunctorMap (ring.{c, v, r} R) f).inv.app F ≫
      (overMap (ring.{c, v, r} R) f).map
        ((localizedSystemAdjunction.{c, v, r} R Z).unit.app
          ((localizedSystemRestriction.{c, v, r} R Z).obj F)) ≫
      (overFunctorMap (ring.{c, v, r} R) f).hom.app ((supported.{c, v, r} R Z).obj F))

/-- The canonical local component formulas, expressed without choosing a biproduct
comparison. Here `k` is extension from W inside Z: its adjunction characterizes it up
to unique counit-compatible isomorphism. The isomorphisms identify restriction of the
self-extension with identity, and restriction of both other extensions with `k(F|W)`.
The last four equations specify every component of the two local matrices.
Source: Stacks 08BU (blueprint: lem-sp-subterminal-cover-module-ses). -/
def localDescription [HasPullbacks C] (W Z T : C) (p : W ⟶ Z) (q : W ⟶ T) : Prop :=
  ∃ (k : ringedSiteModules.{max c v r} ((ring.{c, v, r} R).over W) ⥤
      ringedSiteModules.{max c v r} ((ring.{c, v, r} R).over Z))
    (adj : k ⊣ overMap (ring.{c, v, r} R) p)
    (eSelf : supported.{c, v, r} R Z ⋙ localizedSystemRestriction.{c, v, r} R Z ≅
      localizedSystemRestriction.{c, v, r} R Z)
    (eOther : supported.{c, v, r} R T ⋙ localizedSystemRestriction.{c, v, r} R Z ≅
      localizedSystemRestriction.{c, v, r} R W ⋙ k)
    (eOverlap : supported.{c, v, r} R W ⋙ localizedSystemRestriction.{c, v, r} R Z ≅
      localizedSystemRestriction.{c, v, r} R W ⋙ k),
    ∀ F : modules.{c, v, r} R,
      (localizedSystemRestriction.{c, v, r} R Z).map (counit.{c, v, r} R Z F) = eSelf.hom.app F ∧
      (localizedSystemRestriction.{c, v, r} R Z).map (counit.{c, v, r} R T F) =
        eOther.hom.app F ≫ k.map ((overFunctorMap (ring.{c, v, r} R) p).inv.app F) ≫
          adj.counit.app ((localizedSystemRestriction.{c, v, r} R Z).obj F) ∧
      (localizedSystemRestriction.{c, v, r} R Z).map (nested.{c, v, r} R p F) ≫ eSelf.hom.app F =
        eOverlap.hom.app F ≫ k.map ((overFunctorMap (ring.{c, v, r} R) p).inv.app F) ≫
          adj.counit.app ((localizedSystemRestriction.{c, v, r} R Z).obj F) ∧
      (localizedSystemRestriction.{c, v, r} R Z).map (nested.{c, v, r} R q F) ≫ eOther.hom.app F =
        eOverlap.hom.app F

variable [HasFiniteLimits C] (U V : C)

/-- Intersection of the two subterminals. Source: Stacks 08BU
(blueprint: lem-sp-subterminal-cover-module-ses). -/
abbrev overlap := U ⨯ V

/-- The first arrow has the sign convention `(i_U,-i_V)`. Source: Stacks 08BU
(blueprint: lem-sp-subterminal-cover-module-ses). -/
def first (F : modules.{c, v, r} R) : (supported.{c, v, r} R (overlap U V)).obj F ⟶
    (supported.{c, v, r} R U).obj F ⊞ (supported.{c, v, r} R V).obj F :=
  biprod.lift (nested.{c, v, r} R (prod.fst : U ⨯ V ⟶ U) F)
    (-nested.{c, v, r} R (prod.snd : U ⨯ V ⟶ V) F)

/-- The second arrow is the pair of canonical counits. Source: Stacks 08BU
(blueprint: lem-sp-subterminal-cover-module-ses). -/
def second (F : modules.{c, v, r} R) :
    (supported.{c, v, r} R U).obj F ⊞ (supported.{c, v, r} R V).obj F ⟶ F :=
  biprod.desc (counit.{c, v, r} R U F) (counit.{c, v, r} R V F)

/-- The canonical binary-cover sequence, its naturality, and its termwise complex version.

Source: Stacks Project, Cohomology, Tag 08BU, proof of
lemma-exact-sequence-lower-shriek; blueprint subterminal-slice generalization
(blueprint: lem-sp-subterminal-cover-module-ses).

Proof:
1. Node `lem-sp-subterminal-module-local-calculus` identifies restricted extensions
with extension from the intersection: before sheafification, both are the same summands
with the same scalar and restriction maps. Restriction commutes with their sheafification.
2. Transpose a nested map followed by its counit. The triangle identity makes the
transpose the identity on `F|W`, proving both counit composites equal the W-counit.
Their difference is zero.
3. On U the component maps are `(i,-1)` and `(1,i)`; on V they are `(1,-i')` and
`(i',1)`. Compatibility of the local-calculus identifications with units and counits
identifies each component, including the identities, by its adjunction transpose.
4. On U the splitting is `s(y)=(y,0)`, `r(y,z)=-z`; on V it is
`s(z)=(0,z)`, `r(y,z)=y`. In both cases `ra=bs=1` and `ar+sb=1`, hence the
local sequences are short exact, without requiring i or i' invertible.
5. Joint detection of exactness by restriction to the covering U,V gives global
short exactness, including the endpoint mono and epi. No points of the topos are used.
6. Naturality of the unit, after taking W-transposes, gives naturality of nested maps;
naturality of the counit gives naturality of the second arrow. Apply these equations
to every differential and every component of a cochain map. Apply module short
exactness in each degree to obtain the claimed degreewise short exact sequence. -/
theorem shortExact [J.Subcanonical]
    [Mono (terminal.from U)] [Mono (terminal.from V)]
    (hcover : Sieve.ofArrows (fun b : Bool ↦ if b then U else V)
      (fun b ↦ terminal.from (if b then U else V)) ∈ J (⊤_ C)) :
    (∀ F : modules.{c, v, r} R,
      nested.{c, v, r} R (prod.fst : U ⨯ V ⟶ U) F ≫ counit.{c, v, r} R U F =
        counit.{c, v, r} R (overlap U V) F ∧
      nested.{c, v, r} R (prod.snd : U ⨯ V ⟶ V) F ≫ counit.{c, v, r} R V F =
        counit.{c, v, r} R (overlap U V) F ∧
      ∃ h : first.{c, v, r} R U V F ≫ second.{c, v, r} R U V F = 0,
        (ShortComplex.mk (first.{c, v, r} R U V F) (second.{c, v, r} R U V F) h).ShortExact) ∧
    (∀ (F G : modules.{c, v, r} R) (a : F ⟶ G),
      (supported.{c, v, r} R (overlap U V)).map a ≫ first.{c, v, r} R U V G =
        first.{c, v, r} R U V F ≫
          biprod.map ((supported.{c, v, r} R U).map a) ((supported.{c, v, r} R V).map a) ∧
      biprod.map ((supported.{c, v, r} R U).map a) ((supported.{c, v, r} R V).map a) ≫
          second.{c, v, r} R U V G =
        second.{c, v, r} R U V F ≫ a) ∧
    localDescription.{c, v, r} R (overlap U V) U V prod.fst prod.snd ∧
    localDescription.{c, v, r} R (overlap U V) V U prod.snd prod.fst ∧
    (∀ (K : CochainComplex (modules.{c, v, r} R) ℤ) (i j : ℤ),
      (supported.{c, v, r} R (overlap U V)).map (K.d i j) ≫ first.{c, v, r} R U V (K.X j) =
        first.{c, v, r} R U V (K.X i) ≫
          biprod.map ((supported.{c, v, r} R U).map (K.d i j))
            ((supported.{c, v, r} R V).map (K.d i j)) ∧
      biprod.map ((supported.{c, v, r} R U).map (K.d i j))
          ((supported.{c, v, r} R V).map (K.d i j)) ≫
          second.{c, v, r} R U V (K.X j) = second.{c, v, r} R U V (K.X i) ≫ K.d i j) ∧
    (∀ (K : CochainComplex (modules.{c, v, r} R) ℤ) (n : ℤ),
      ∃ h : first.{c, v, r} R U V (K.X n) ≫ second.{c, v, r} R U V (K.X n) = 0,
        (ShortComplex.mk (first.{c, v, r} R U V (K.X n))
          (second.{c, v, r} R U V (K.X n)) h).ShortExact) ∧
    (∀ (K L : CochainComplex (modules.{c, v, r} R) ℤ) (a : K ⟶ L) (n : ℤ),
      (supported.{c, v, r} R (overlap U V)).map (a.f n) ≫ first.{c, v, r} R U V (L.X n) =
        first.{c, v, r} R U V (K.X n) ≫
          biprod.map ((supported.{c, v, r} R U).map (a.f n))
            ((supported.{c, v, r} R V).map (a.f n)) ∧
      biprod.map ((supported.{c, v, r} R U).map (a.f n)) ((supported.{c, v, r} R V).map (a.f n)) ≫
          second.{c, v, r} R U V (L.X n) = second.{c, v, r} R U V (K.X n) ≫ a.f n) := by
  sorry

end SheafOfModules.SubterminalCover
