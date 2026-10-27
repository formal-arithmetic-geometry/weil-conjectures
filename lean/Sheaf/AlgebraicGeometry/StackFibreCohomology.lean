module

public import Sheaf.AlgebraicGeometry.StackBigEtaleModuleFunctors
public import Sheaf.AlgebraicGeometry.StackFppfModuleFunctors
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Linear.Yoneda
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses

/-! # Big stack sites and the fibre cohomology presheaf

Source: Stacks Project, stacks-sheaves.tex, Tags 06TP, 06TV, 06W6 and 075G
(blueprint: def-sfb-stack-fibre-cohomology-presheaf).

All coefficients are in the common ambient universe. The comma model of the test
fibre retains arrows and automorphisms; it is equivalent to the scheme 2-base change.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The two big topologies in Tag 075G.
Source: Stacks 075G (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
inductive ModuliCohomologyTopology
  | etale
  | fppf

/-- Select the already recorded big topology.
Source: Stacks 06TP (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
abbrev moduliCohomologyTopology {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (τ : ModuliCohomologyTopology) :
    GrothendieckTopology F.obj :=
  match τ with
  | .etale => moduliBigEtaleTopology F
  | .fppf => moduliFppfTopology F

/-- Select the recorded structure ring, without constructing another ring sheaf.
Source: Stacks 06TV (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
abbrev moduliCohomologyRings {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    (τ : ModuliCohomologyTopology) :
    Sheaf (moduliCohomologyTopology F τ) RingCat.{max (u + 1) v w} :=
  ⟨(moduliBigEtaleRings F hF).obj, match τ with
    | .etale => (moduliBigEtaleRings F hF).property
    | .fppf => (moduliModuleRings F hF).property⟩

/-- Select the recorded category of all modules.
Source: Stacks 075G (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
abbrev ModuliCohomologyModules {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    (τ : ModuliCohomologyTopology) :=
  ringedSiteModules.{max (u + 1) v w} (moduliCohomologyRings F hF τ)

/-- Use the selected site's recorded sheafification instance.
Source: Stacks 06WE (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
instance moduliCohomologyHasSheafify {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (τ : ModuliCohomologyTopology) :
    HasSheafify (moduliCohomologyTopology F τ) AddCommGrpCat.{max (u + 1) v w} :=
  match τ with
  | .etale => moduliBigEtale_hasSheafify F
  | .fppf => moduliFppf_hasSheafify F

/-- Use the selected site's recorded local-bijection instance.
Source: Stacks 06WE (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
instance moduliCohomologyWEquals {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (τ : ModuliCohomologyTopology) :
    (moduliCohomologyTopology F τ).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v w} :=
  match τ with
  | .etale => moduliBigEtale_wEqualsLocallyBijective F
  | .fppf => moduliFppf_wEqualsLocallyBijective F

/-- Use Mathlib's abelian structure with the selected topology.
Source: Stacks 06WE (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
instance moduliCohomologyAbelian {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    (τ : ModuliCohomologyTopology) : Abelian (ModuliCohomologyModules F hF τ) :=
  letI : HasSheafify (moduliCohomologyTopology F τ)
      AddCommGrpCat.{max (u + 1) v w} := moduliCohomologyHasSheafify F τ
  letI : (moduliCohomologyTopology F τ).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v w} := moduliCohomologyWEquals F τ
  inferInstanceAs (Abelian (SheafOfModules.{max (u + 1) v w}
    (moduliCohomologyRings F hF τ)))

/-- Select the recorded injective-resolution instance.
Source: Stacks 06WE (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
instance moduliCohomologyHasInjectiveResolutions {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    (τ : ModuliCohomologyTopology) : HasInjectiveResolutions (ModuliCohomologyModules F hF τ) :=
  match τ with
  | .etale => moduliBigEtale_hasInjectiveResolutions F hF
  | .fppf => moduliFppf_hasInjectiveResolutions F hF

/-- The underlying presheaf isomorphism of the recorded structural ring comparison.
Source: Stacks 06TV (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
def moduliCohomologyRingIso {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (τ : ModuliCohomologyTopology) :
    (moduliCohomologyRings F hF τ).obj ≅
      a.toFunctor.op ⋙ (moduliCohomologyRings G hG τ).obj :=
  match τ with
  | .etale => (sheafToPresheaf (moduliBigEtaleTopology F) RingCat).mapIso
      (moduliBigEtaleRingIso hF hG a)
  | .fppf => (sheafToPresheaf (moduliFppfTopology F) RingCat).mapIso
      (moduliFppfRingIso hF hG a)

/-- Select literal precomposition from the topology's recorded interface.
Source: Stacks 06W6 (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
abbrev moduliCohomologyRestriction {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (τ : ModuliCohomologyTopology) :
    ModuliCohomologyModules G hG τ ⥤ ModuliCohomologyModules F hF τ :=
  letI : a.toFunctor.IsContinuous (moduliCohomologyTopology F τ)
      (moduliCohomologyTopology G τ) := match τ with
    | .etale => moduliBigEtale_continuous hF hG a
    | .fppf => moduliFppf_continuous hF hG a
  SheafOfModules.pushforward (F := a.toFunctor)
    ⟨(moduliCohomologyRingIso hF hG a τ).hom⟩

/-- The selected precomposition has its recorded right adjoint.
Source: Stacks 06W6 (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
instance moduliCohomologyRestriction_isLeftAdjoint
    {S : AlgebraicGeometry.Scheme.{u}} {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (τ : ModuliCohomologyTopology) :
    (moduliCohomologyRestriction hF hG a τ).IsLeftAdjoint :=
  match τ with
  | .etale => moduliBigEtalePrecomposition_isLeftAdjoint hF hG a
  | .fppf => moduliFppfPrecomposition_isLeftAdjoint hF hG a

/-- Select the recorded direct image, rather than selecting a new right adjoint.
Source: Stacks 06W6 (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
abbrev moduliCohomologyPushforward {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (τ : ModuliCohomologyTopology) :
    ModuliCohomologyModules F hF τ ⥤ ModuliCohomologyModules G hG τ :=
  match τ with
  | .etale => moduliBigEtaleDirectImage hF hG a
  | .fppf => moduliFppfDirectImage hF hG a

/-- The adjunction of the selected direct image and its original precomposition.
Source: Stacks 06W6 (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
def moduliCohomologyAdjunction {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (τ : ModuliCohomologyTopology) :
    moduliCohomologyRestriction hF hG a τ ⊣ moduliCohomologyPushforward hF hG a τ :=
  match τ with
  | .etale => Adjunction.ofIsLeftAdjoint (moduliBigEtalePrecomposition hF hG a)
  | .fppf => Adjunction.ofIsLeftAdjoint (moduliFppfPrecomposition hF hG a)

/-- Select the recorded additivity instance.
Source: Stacks 06W6 (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
instance moduliCohomologyPushforward_additive
    {S : AlgebraicGeometry.Scheme.{u}} {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (τ : ModuliCohomologyTopology) :
    (moduliCohomologyPushforward hF hG a τ).Additive :=
  match τ with
  | .etale => moduliBigEtaleDirectImage_additive hF hG a
  | .fppf => moduliFppfDirectImage_additive hF hG a

/-- Select the recorded higher direct image, with its existing derived-functor choices.
Source: Stacks 075G (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
abbrev moduliCohomologyHigherImage {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (τ : ModuliCohomologyTopology) (q : ℕ) :
    ModuliCohomologyModules F hF τ ⥤ ModuliCohomologyModules G hG τ :=
  (moduliCohomologyPushforward hF hG a τ).rightDerived q

/-- The underived direct image, viewed as a module presheaf.
Source: Stacks 075G (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
abbrev moduliCohomologyPresheafPushforward {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (τ : ModuliCohomologyTopology) :
    ModuliCohomologyModules F hF τ ⥤
      PresheafOfModules.{max (u + 1) v w} (moduliCohomologyRings G hG τ).obj :=
  moduliCohomologyPushforward hF hG a τ ⋙
    SheafOfModules.forget.{max (u + 1) v w} (moduliCohomologyRings G hG τ)

/-- The fibre cohomology presheaf computed on an injective resolution on the source.
Its identification with independent injective cohomology on each test fibre is
part of Tag 075G, not an extra assumption in this definition.
Source: Stacks 075G (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
def moduliFibreCohomologyPresheaf {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (τ : ModuliCohomologyTopology) (q : ℕ) :
    ModuliCohomologyModules F hF τ ⥤
      PresheafOfModules.{max (u + 1) v w} (moduliCohomologyRings G hG τ).obj :=
  letI : HasSheafify (moduliCohomologyTopology F τ)
      AddCommGrpCat.{max (u + 1) v w} := moduliCohomologyHasSheafify F τ
  letI : (moduliCohomologyTopology F τ).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v w} := moduliCohomologyWEquals F τ
  letI : Abelian (ModuliCohomologyModules F hF τ) := moduliCohomologyAbelian F hF τ
  letI : HasInjectiveResolutions (ModuliCohomologyModules F hF τ) :=
    moduliCohomologyHasInjectiveResolutions F hF τ
  (moduliCohomologyPresheafPushforward hF hG a τ).rightDerived q


/-- Comma model of the scheme test fibre: objects are x and an arrow a(x) → y.
Source: Stacks 06W6 (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
def moduliCohomologyFibre {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)} (a : BasedFunctor F G) (y : G.obj) :
    BasedCategory (Over S) :=
  BasedCategory.ofFunctor (CostructuredArrow.proj a.toFunctor y ⋙ F.p)

/-- The comma test fibre is fibred in groupoids over schemes.
Source: Stacks 06W6 (blueprint: def-sfb-stack-fibre-cohomology-presheaf).
Proof: lift a scheme arrow cartesianly in F and compose its image with the
specified arrow to y. Strong cartesianness in F and G gives unique lifts of
triangles, hence the required fibred-groupoid axioms. -/
theorem moduliCohomologyFibre_isFibred {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (y : G.obj) : IsFibredInGroupoids (moduliCohomologyFibre a y) := by
  sorry

/-- Restricting a module to the comma test fibre preserves its sheaf condition.
Source: Stacks 06W6 (blueprint: def-sfb-stack-fibre-cohomology-presheaf).
Proof: every inherited covering projects to the same scheme covering. Its
cartesian overlaps and all compatibility equations are the original ones for M;
apply M's sheaf condition. The scalar rings agree definitionally. -/
theorem moduliCohomologyFibreRestriction_isSheaf {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (y : G.obj) (τ : ModuliCohomologyTopology)
    (M : ModuliCohomologyModules F hF τ) :
    Presheaf.IsSheaf (moduliCohomologyTopology (moduliCohomologyFibre a y) τ)
      ((PresheafOfModules.pushforward₀ (CostructuredArrow.proj a.toFunctor y)
        (moduliCohomologyRings F hF τ).obj).obj M.val).presheaf := by
  sorry

/-- Precomposition to the test fibre, with original values, maps and scalar actions.
Source: Stacks 06W6 (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
def moduliCohomologyFibreRestriction {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (y : G.obj) (τ : ModuliCohomologyTopology) :
    ModuliCohomologyModules F hF τ ⥤ ModuliCohomologyModules (moduliCohomologyFibre a y)
      (moduliCohomologyFibre_isFibred hF hG a y) τ where
  obj M := ⟨(PresheafOfModules.pushforward₀ (CostructuredArrow.proj a.toFunctor y)
    (moduliCohomologyRings F hF τ).obj).obj M.val,
      moduliCohomologyFibreRestriction_isSheaf hF hG a y τ M⟩
  map f := ⟨(PresheafOfModules.pushforward₀ (CostructuredArrow.proj a.toFunctor y)
    (moduliCohomologyRings F hF τ).obj).map f.val⟩

/-- Fibre precomposition is additive since all maps are unchanged.
Source: Stacks 06W6 (blueprint: def-sfb-stack-fibre-cohomology-presheaf).
Proof: evaluate at every comma object; precomposition preserves the pointwise
sum of any two module morphisms, hence preserves their sum as sheaf morphisms. -/
@[instance] theorem moduliCohomologyFibreRestriction_additive
    {S : AlgebraicGeometry.Scheme.{u}} {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (y : G.obj) (τ : ModuliCohomologyTopology) :
    (moduliCohomologyFibreRestriction hF hG a y τ).Additive := by
  sorry

/-- Global sections, equivalently compatible families via unitHomEquiv.
Source: Stacks 06W6 (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
def moduliCohomologyGlobalSections {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    (τ : ModuliCohomologyTopology) :
    ModuliCohomologyModules F hF τ ⥤ AddCommGrpCat.{max (u + 1) v w} :=
  preadditiveCoyoneda.obj (op (SheafOfModules.unit (moduliCohomologyRings F hF τ)))

/-- Global sections are additive by postcomposition of module morphisms.
Source: Stacks 06W6 (blueprint: def-sfb-stack-fibre-cohomology-presheaf).
Proof: addition of morphisms is componentwise, and postcomposition is additive
in the preadditive category of module sheaves. -/
@[instance] theorem moduliCohomologyGlobalSections_additive
    {S : AlgebraicGeometry.Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hF : IsFibredInGroupoids F) (τ : ModuliCohomologyTopology) :
    (moduliCohomologyGlobalSections F hF τ).Additive := by
  sorry

/-- Independently derived global sections on the test fibre, using its own injectives.
Source: Stacks 075G (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
def moduliCohomologyFibreGroups {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (y : G.obj) (τ : ModuliCohomologyTopology) (q : ℕ) :
    ModuliCohomologyModules F hF τ ⥤ AddCommGrpCat.{max (u + 1) v w} :=
  letI : HasSheafify (moduliCohomologyTopology (moduliCohomologyFibre a y) τ)
      AddCommGrpCat.{max (u + 1) v w} :=
    moduliCohomologyHasSheafify (moduliCohomologyFibre a y) τ
  letI : (moduliCohomologyTopology (moduliCohomologyFibre a y) τ).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v w} :=
    moduliCohomologyWEquals (moduliCohomologyFibre a y) τ
  letI : Abelian (ModuliCohomologyModules (moduliCohomologyFibre a y)
      (moduliCohomologyFibre_isFibred hF hG a y) τ) :=
    moduliCohomologyAbelian (moduliCohomologyFibre a y)
      (moduliCohomologyFibre_isFibred hF hG a y) τ
  letI : HasInjectiveResolutions (ModuliCohomologyModules (moduliCohomologyFibre a y)
      (moduliCohomologyFibre_isFibred hF hG a y) τ) :=
    moduliCohomologyHasInjectiveResolutions (moduliCohomologyFibre a y)
      (moduliCohomologyFibre_isFibred hF hG a y) τ
  moduliCohomologyFibreRestriction hF hG a y τ ⋙
    (moduliCohomologyGlobalSections (moduliCohomologyFibre a y)
      (moduliCohomologyFibre_isFibred hF hG a y) τ).rightDerived q


/-- Evaluation of a module presheaf, retaining its abelian group.
Source: Stacks 075G (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
abbrev moduliCohomologyEvaluation {S : AlgebraicGeometry.Scheme.{u}}
    (G : BasedCategory.{v, w} (Over S)) (hG : IsFibredInGroupoids G)
    (τ : ModuliCohomologyTopology) (y : G.obj) :=
  PresheafOfModules.evaluation.{max (u + 1) v w} (moduliCohomologyRings G hG τ).obj
    (op y) ⋙ forget₂ (ModuleCat.{max (u + 1) v w}
      ((moduliCohomologyRings G hG τ).obj.obj (op y))) AddCommGrpCat

/-- The section formula, uniquely normalized by the inverse-image counit.
Source: Stacks 06W6 (blueprint: def-sfb-stack-fibre-cohomology-presheaf).
Proof: a section s over y gives at (x,b:a(x)→y) its restriction along b, followed
by the counit at x. Naturality gives a compatible family. Conversely such families
give the right Kan extension, so the adjunction Hom bijection makes this map
bijective. The two constructions commute with M-morphisms and are additive.
Equality on each component of every compatible family proves uniqueness. -/
theorem moduliCohomologySectionsIso_existsUnique {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (y : G.obj) (τ : ModuliCohomologyTopology) :
    ∃! e : moduliCohomologyPresheafPushforward hF hG a τ ⋙
        moduliCohomologyEvaluation G hG τ y ≅
      moduliCohomologyFibreRestriction hF hG a y τ ⋙
        moduliCohomologyGlobalSections (moduliCohomologyFibre a y)
          (moduliCohomologyFibre_isFibred hF hG a y) τ,
      ∀ (M : ModuliCohomologyModules F hF τ)
        (s : ((moduliCohomologyPushforward hF hG a τ).obj M).val.obj (op y))
        (i : CostructuredArrow a.toFunctor y),
        (((moduliCohomologyFibreRestriction hF hG a y τ).obj M).unitHomEquiv
          ((e.hom.app M) s)).val (op i) =
        (((moduliCohomologyAdjunction hF hG a τ).counit.app
          M).val.app (op i.left))
            ((((moduliCohomologyPushforward hF hG a τ).obj M).val.map i.hom.op) s) := by
  sorry

/-- The canonical section isomorphism, determined uniquely by the displayed counit formula.
Source: Stacks 06W6 (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
def moduliCohomologySectionsIso {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (y : G.obj) (τ : ModuliCohomologyTopology) :
    moduliCohomologyPresheafPushforward hF hG a τ ⋙
        moduliCohomologyEvaluation G hG τ y ≅
      moduliCohomologyFibreRestriction hF hG a y τ ⋙
        moduliCohomologyGlobalSections (moduliCohomologyFibre a y)
          (moduliCohomologyFibre_isFibred hF hG a y) τ :=
  (moduliCohomologySectionsIso_existsUnique hF hG a y τ).exists.choose

/-- The pullbacks of a test function to every object of its comma fibre.
Source: Stacks 06TV and 075G (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
def moduliCohomologyFibreFunctionValues {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (y : G.obj) (τ : ModuliCohomologyTopology)
    (b : (moduliCohomologyRings G hG τ).obj.obj (op y))
    (i : (moduliCohomologyFibre a y).objᵒᵖ) :
    ((moduliStructurePresheaf (moduliCohomologyFibre a y)) ⋙
      forget₂ CommRingCat RingCat).obj i :=
  ((moduliCohomologyRingIso hF hG a τ).inv.app (op i.unop.left))
    ((moduliCohomologyRings G hG τ).obj.map i.unop.hom.op b)

/-- Pullbacks of a function form a compatible family.
Source: Stacks 06TV (blueprint: def-sfb-stack-fibre-cohomology-presheaf).
Proof: the comma triangle says that the two arrows to y agree. Apply the
regular-functions functor and naturality of the structure-ring identification. -/
theorem moduliCohomologyFibreFunction_compatible {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (y : G.obj) (τ : ModuliCohomologyTopology)
    (b : (moduliCohomologyRings G hG τ).obj.obj (op y)) :
    ∀ {i j : (moduliCohomologyFibre a y).objᵒᵖ} (f : i ⟶ j),
      ((moduliStructurePresheaf (moduliCohomologyFibre a y)) ⋙
        forget₂ CommRingCat RingCat).map f (moduliCohomologyFibreFunctionValues hF hG a y τ b i) =
          moduliCohomologyFibreFunctionValues hF hG a y τ b j := by
  sorry

/-- A test function as a global section of the fibre's structure ring.
Source: Stacks 06TV (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
def moduliCohomologyFibreFunction {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (y : G.obj) (τ : ModuliCohomologyTopology)
    (b : (moduliCohomologyRings G hG τ).obj.obj (op y)) :
    RingCat.sectionsSubring ((moduliStructurePresheaf (moduliCohomologyFibre a y)) ⋙
      forget₂ CommRingCat RingCat) :=
  ⟨moduliCohomologyFibreFunctionValues hF hG a y τ b,
    moduliCohomologyFibreFunction_compatible hF hG a y τ b⟩

/-- Multiplication on a restricted module by the pulled-back test function.
Source: Stacks 075G (blueprint: def-sfb-stack-fibre-cohomology-presheaf). -/
def moduliCohomologyFibreScalar {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (y : G.obj) (τ : ModuliCohomologyTopology)
    (M : ModuliCohomologyModules F hF τ)
    (b : (moduliCohomologyRings G hG τ).obj.obj (op y)) :
    (moduliCohomologyFibreRestriction hF hG a y τ).obj M ⟶
      (moduliCohomologyFibreRestriction hF hG a y τ).obj M :=
  ⟨PresheafOfModules.sectionsSMul
    ((moduliCohomologyFibreRestriction hF hG a y τ).obj M).val
      (moduliCohomologyFibreFunction hF hG a y τ b)⟩

end CategoryTheory
