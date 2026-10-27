module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Algebra sheaves on the big fppf site of a fibred groupoid

Source: Stacks Project, stacks-sheaves.tex, Tags 06TP, 06TV, 06WG and 06W5--06W6
(blueprint: def-sfb-stack-quasi-coherent-algebra).

The total category, rather than its isomorphism classes, is the site. Regular functions
are transported by `ULift` to the common ambient universe containing the site; this changes
neither the rings nor their restriction maps, via `ULift.ringEquiv`. No algebraicity is used.
-/

@[expose] public section

set_option autoImplicit false

universe u v w v' w'

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The underlying scheme of an object of the fibred category.
Source: Stacks Tag 06TP (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliSchemeForget {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) : F.obj ⥤ AlgebraicGeometry.Scheme.{u} :=
  F.p ⋙ Over.forget S

/-- Fppf coverings are precisely families whose scheme maps form fppf coverings.
Source: Stacks Tag 06TP (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliFppfPrecoverage {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) : Precoverage F.obj :=
  AlgebraicGeometry.Scheme.fppfPrecoverage.comap (moduliSchemeForget F)

/-- The big fppf topology on the total category.
Source: Stacks Tag 06TP (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
abbrev moduliFppfTopology {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) : GrothendieckTopology F.obj :=
  (moduliFppfPrecoverage F).toGrothendieck

/-- Regular functions with canonical universe transport; maps are pullback on whole schemes.
Source: Stacks Tag 06TV (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliStructurePresheaf {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) :
    F.objᵒᵖ ⥤ CommRingCat.{max (u + 1) v w} where
  obj x := CommRingCat.of (ULift.{max (u + 1) v w}
    (AlgebraicGeometry.Scheme.Γ.obj (op ((moduliSchemeForget F).obj x.unop))))
  map f := CommRingCat.ofHom
    (AlgebraicGeometry.Scheme.Γ.map ((moduliSchemeForget F).map f.unop).op).hom.ulift

/-- Regular functions satisfy fppf descent on a category fibred in groupoids.
Source: Stacks Tag 06TV (blueprint: def-sfb-stack-quasi-coherent-algebra).

Proof: a covering projects to an fppf covering of schemes. Strongly cartesian lifts
identify its overlaps with the corresponding scheme fibre products. Regular functions
satisfy fppf descent on schemes, giving the unique glued section and its compatibility
with every arrow. The canonical ULift equivalences preserve this equalizer diagram. -/
theorem moduliStructurePresheaf_isSheaf {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    Presheaf.IsSheaf (moduliFppfTopology F) (moduliStructurePresheaf F) := by
  sorry

/-- The structure sheaf evaluates to the regular functions of the underlying scheme.
Source: Stacks Tag 06TV (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliStructureSheaf {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    Sheaf (moduliFppfTopology F) CommRingCat.{max (u + 1) v w} :=
  ⟨moduliStructurePresheaf F, moduliStructurePresheaf_isSheaf F hF⟩

/-- Commutative algebra sheaves and their morphisms commuting with the structure maps.
Source: Stacks Tags 06TV, 06WG (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
abbrev ModuliAlgebraSheaf {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :=
  Under (moduliStructureSheaf F hF)

/-- Forget commutativity in the structure sheaf, as required by module sheaves.
Source: Stacks Tag 06WG (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
abbrev moduliModuleRings {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :=
  (sheafCompose (moduliFppfTopology F)
    (forget₂ CommRingCat.{max (u + 1) v w} RingCat.{max (u + 1) v w})).obj
    (moduliStructureSheaf F hF)

/-- The underlying module has scalar action `r • a = η(r) * a`.
Source: Stacks Tag 06WG (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
noncomputable def moduliAlgebraModule {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {hF : IsFibredInGroupoids F}
    (A : ModuliAlgebraSheaf F hF) :
    ringedSiteModules.{max (u + 1) v w} (moduliModuleRings F hF) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (moduliFppfTopology F)
      (forget₂ CommRingCat.{max (u + 1) v w} RingCat.{max (u + 1) v w})).map A.hom)).obj
    (SheafOfModules.unit
      ((sheafCompose (moduliFppfTopology F)
        (forget₂ CommRingCat.{max (u + 1) v w} RingCat.{max (u + 1) v w})).obj A.right))

/-- Slice sheafification exists in the ambient universe of the total site.
Source: Stacks Tags 06TP, 06WG (blueprint: def-sfb-stack-quasi-coherent-algebra).
Proof: each slice has objects and arrows in the ambient universe. The usual two
plus constructions for additive presheaves give sheafification there, by taking
matching families and quotienting by equality after a covering refinement. -/
@[instance] theorem moduliSliceHasWeakSheafify {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (x : F.obj) :
    HasWeakSheafify ((moduliFppfTopology F).over x)
      AddCommGrpCat.{max (u + 1) v w} := by
  sorry

/-- Sheafification on slices inverts exactly locally bijective maps.
Source: Stacks Tags 06TP, 06WG (blueprint: def-sfb-stack-quasi-coherent-algebra).
Proof: two plus constructions have locally bijective unit. A locally bijective
map becomes an isomorphism: locally lift sections and use local injectivity to
glue uniquely. Conversely an isomorphism after sheafification, together with its
locally bijective units, forces both local lifting and local equality. -/
@[instance] theorem moduliSliceWEqualsLocallyBijective {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (x : F.obj) :
    ((moduliFppfTopology F).over x).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v w} := by
  sorry

/-- Quasi-coherence is the existing general-site predicate of local free presentations.
Source: Stacks Tag 06WG (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def IsQuasicoherentModuliAlgebra {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {hF : IsFibredInGroupoids F}
    (A : ModuliAlgebraSheaf F hF) : Prop :=
  SheafOfModules.IsQuasicoherent (moduliAlgebraModule A)

/-- Surjections mean local lifting of sections in the fppf topology, not objectwise lifting.
Source: Stacks Tags 06TP, 06WG (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
abbrev IsSurjectiveModuliAlgebra {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {hF : IsFibredInGroupoids F}
    {A B : ModuliAlgebraSheaf F hF} (f : A ⟶ B) : Prop :=
  Presheaf.IsLocallySurjective (moduliFppfTopology F) f.right.hom

/-- Global sections of any set-valued sheaf are compatible families on all objects.
Source: Stacks Tag 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
abbrev moduliGlobalSections {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)}
    (A : Sheaf (moduliFppfTopology F) (Type (max (u + 1) v w))) :=
  A.obj.sections

/-- Global sections of a ring sheaf, with pointwise ring operations.
Source: Stacks Tag 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliGlobalSectionsRing {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)}
    (A : Sheaf (moduliFppfTopology F) CommRingCat.{max (u + 1) v w}) :
    CommRingCat.{max (u + 1) v w} :=
  CommRingCat.of (RingCat.sectionsSubring (A.obj ⋙ forget₂ CommRingCat RingCat))

/-- Pullback to an actual 2-base change uses the recorded fibred-category construction.
Source: Stacks Tag 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
abbrev moduliSpaceBaseChange {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (T : Y.EtaleSite) :=
  moduliTwoFiberProduct φ (discreteModuliMap T.obj.hom)

/-- The projection from a 2-base change to the original category.
Source: Stacks Tag 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
abbrev moduliSpaceBaseChangeProjection {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (T : Y.EtaleSite) :=
  moduliTwoFiberFst φ (discreteModuliMap T.obj.hom)

/-- Restriction on a 2-base change is literal precomposition with its projection.
Source: Stacks Tag 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliBaseChangeRestrictionPresheaf {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (T : Y.EtaleSite)
    (A : Sheaf (moduliFppfTopology F) CommRingCat.{max (u + 1) v w}) :=
  (moduliSpaceBaseChangeProjection Y φ T).toFunctor.op ⋙ A.obj

/-- Literal restriction to the 2-base change remains a sheaf.
Source: Stacks Tags 06TV, 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra).
Proof: the projection sends an fppf covering to the same scheme covering and
identifies its overlaps. The sheaf equalizer is therefore the original one for A. -/
theorem moduliBaseChangeRestriction_isSheaf {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (T : Y.EtaleSite)
    (A : Sheaf (moduliFppfTopology F) CommRingCat.{max (u + 1) v w}) :
    Presheaf.IsSheaf (moduliFppfTopology (moduliSpaceBaseChange Y φ T))
      (moduliBaseChangeRestrictionPresheaf Y φ T A) := by
  sorry

/-- The restricted sheaf uses the original values and all the original operations.
Source: Stacks Tag 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliBaseChangeRestriction {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (T : Y.EtaleSite)
    (A : Sheaf (moduliFppfTopology F) CommRingCat.{max (u + 1) v w}) :
    Sheaf (moduliFppfTopology (moduliSpaceBaseChange Y φ T))
      CommRingCat.{max (u + 1) v w} :=
  ⟨moduliBaseChangeRestrictionPresheaf Y φ T A,
    moduliBaseChangeRestriction_isSheaf hF Y φ T A⟩

/-- Scheme 2-base change preserves categories fibred in groupoids.
Source: Stacks Tags 06TP, 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra).
Proof: lift a base arrow in F and in the discrete fibred category of the chart.
The comparison isomorphism pulls back uniquely. The cartesian universal property
in both factors gives the unique cartesian factorization in their 2-fibre product. -/
theorem moduliSpaceBaseChange_isFibred {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (T : Y.EtaleSite) :
    IsFibredInGroupoids (moduliSpaceBaseChange Y φ T) := by
  sorry

/-- The restricted structure presheaf is the structure presheaf of the 2-base change.
Source: Stacks Tags 06TV, 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra).
Proof: the projection is over Sch/S, so underlying schemes and their maps agree.
Apply Γ and its canonical ULift transport to this equality of projections. -/
theorem moduliBaseChangeStructurePresheaf_eq {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (T : Y.EtaleSite) :
    moduliStructurePresheaf (moduliSpaceBaseChange Y φ T) =
      (moduliSpaceBaseChangeProjection Y φ T).toFunctor.op ⋙ moduliStructurePresheaf F := by
  sorry

/-- Restrict algebra operations and the structure morphism by precomposition.
Source: Stacks Tags 06TV, 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliBaseChangeAlgebra {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (T : Y.EtaleSite)
    (A : ModuliAlgebraSheaf F hF) :
    ModuliAlgebraSheaf (moduliSpaceBaseChange Y φ T)
      (moduliSpaceBaseChange_isFibred hF Y φ T) :=
  Under.mk
    ({ hom := eqToHom (moduliBaseChangeStructurePresheaf_eq Y φ T) ≫
        Functor.whiskerLeft (moduliSpaceBaseChangeProjection Y φ T).toFunctor.op A.hom.hom } :
      moduliStructureSheaf (moduliSpaceBaseChange Y φ T)
        (moduliSpaceBaseChange_isFibred hF Y φ T) ⟶
          moduliBaseChangeRestriction hF Y φ T A.right)

/-- The comma model of the same base change: objects are x and an arrow φ(x) → T.
Source: Stacks Tag 06W6, paragraph after the equation
(blueprint: def-sfb-stack-quasi-coherent-algebra). -/
abbrev ModuliPushforwardIndex {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (T : Y.EtaleSite) :=
  CostructuredArrow φ.toFunctor T.obj

/-- Sections on the comma model are compatible families with original restriction maps.
Source: Stacks Tag 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliPushforwardDiagram {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (T : Y.EtaleSite)
    (A : Sheaf (moduliFppfTopology F) CommRingCat.{max (u + 1) v w}) :=
  (CostructuredArrow.proj φ.toFunctor T.obj).op ⋙ A.obj

/-- The direct-image presheaf: section rings on the base-change categories, with
restriction by base change. Source: Stacks Tags 06W5--06W6
(blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliDirectImagePresheaf {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    (A : Sheaf (moduliFppfTopology F) CommRingCat.{max (u + 1) v w}) :
    Y.EtaleSiteᵒᵖ ⥤ CommRingCat.{max (u + 1) v w} where
  obj T := CommRingCat.of
    (RingCat.sectionsSubring (moduliPushforwardDiagram Y φ T.unop A ⋙
      forget₂ CommRingCat RingCat))
  map f := CommRingCat.ofHom
    { toFun := fun s ↦ ⟨fun i ↦ s.1 (op ((CostructuredArrow.map f.unop.hom).obj i.unop)),
        fun g ↦ s.2 ((CostructuredArrow.map f.unop.hom).map g.unop).op⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := by ext s i; rfl
  map_comp _ _ := by ext s i; rfl

/-- The section formula defines a sheaf on the small étale site of the target.
Source: Stacks Tags 06W5--06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra).
Proof: an étale cover of T pulls back to an fppf cover of every object over T.
A compatible family of sections therefore glues uniquely using A's sheaf condition;
uniqueness shows compatibility along all arrows of the comma category. This gives
exactly the sheaf equalizer for each étale covering of T. -/
theorem moduliDirectImagePresheaf_isSheaf {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    (A : Sheaf (moduliFppfTopology F) CommRingCat.{max (u + 1) v w}) :
    Presheaf.IsSheaf Y.etaleTopology (moduliDirectImagePresheaf Y φ A) := by
  sorry

/-- The direct-image ring sheaf with the explicit base-change section formula.
Source: Stacks Tags 06W5--06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliDirectImage {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    (A : Sheaf (moduliFppfTopology F) CommRingCat.{max (u + 1) v w}) :
    Sheaf Y.etaleTopology CommRingCat.{max (u + 1) v w} :=
  ⟨moduliDirectImagePresheaf Y φ A, moduliDirectImagePresheaf_isSheaf hF Y φ A⟩

/-- The direct-image value is the ring of sections on the actual 2-fibre product.
Source: Stacks Tag 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra).
Proof: an object (x, w, α) of the 2-fibre product gives the comma object whose
arrow is α followed by the arrow from w to the chart. In the opposite direction,
use the underlying scheme map of a comma arrow as w and factor the arrow into
its vertical isomorphism followed by that chart arrow. The two constructions are
inverse up to their canonical isomorphisms, over F. Precomposition therefore
identifies compatible families, and preserves pointwise ring operations. -/
theorem moduliDirectImage_sections {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (T : Y.EtaleSite)
    (A : Sheaf (moduliFppfTopology F) CommRingCat.{max (u + 1) v w}) :
    Nonempty (((moduliDirectImage hF Y φ A).obj.obj (op T)) ≃+*
      RingCat.sectionsSubring
        ((moduliBaseChangeRestriction hF Y φ T A).obj ⋙ forget₂ CommRingCat RingCat)) := by
  sorry

/-- The canonical scheme map from a comma object to the target chart.
Source: Stacks Tag 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliChartSchemeMap {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (T : Y.EtaleSite)
    (i : ModuliPushforwardIndex Y φ T) :
    (moduliSchemeForget F).obj i.left ⟶ (AlgebraicGeometry.AlgebraicSpace.etaleForget Y).obj T :=
  eqToHom (congrArg (fun Z : Over S ↦ Z.left) (φ.w_obj i.left)).symm ≫ i.hom.left.left

/-- Pullbacks of a function on a chart form a compatible section family.
Source: Stacks Tag 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra).
Proof: the comma square says that its two scheme maps to the chart agree. Apply
contravariant functoriality of scheme global sections and transport by ULift. -/
theorem moduliChartPullbacks_compatible {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (T : Y.EtaleSite)
    (r : AlgebraicGeometry.Scheme.Γ.obj
      (op ((AlgebraicGeometry.AlgebraicSpace.etaleForget Y).obj T))) :
    (fun i : (ModuliPushforwardIndex Y φ T)ᵒᵖ ↦
      ULift.up ((AlgebraicGeometry.Scheme.Γ.map
      (moduliChartSchemeMap Y φ T i.unop).op) r)) ∈
      (moduliPushforwardDiagram Y φ T (moduliStructureSheaf F hF) ⋙
        forget CommRingCat).sections := by
  sorry

/-- The canonical structure map on a chart sends r to all its scheme pullbacks.
Source: Stacks Tag 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliStructureMapApp {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) (T : Y.EtaleSite) :
    AlgebraicGeometry.Scheme.Γ.obj
      (op ((AlgebraicGeometry.AlgebraicSpace.etaleForget Y).obj T)) →+*
    (moduliDirectImage hF Y φ (moduliStructureSheaf F hF)).obj.obj (op T) where
  toFun r := ⟨fun i ↦ ULift.up ((AlgebraicGeometry.Scheme.Γ.map
    (moduliChartSchemeMap Y φ T i.unop).op) r), moduliChartPullbacks_compatible hF Y φ T r⟩
  map_one' := Subtype.ext (funext (fun _i ↦ congrArg ULift.up (map_one _)))
  map_mul' r s := Subtype.ext (funext (fun _i ↦ congrArg ULift.up (map_mul _ r s)))
  map_zero' := Subtype.ext (funext (fun _i ↦ congrArg ULift.up (map_zero _)))
  map_add' r s := Subtype.ext (funext (fun _i ↦ congrArg ULift.up (map_add _ r s)))

/-- The chart structure maps commute with restriction on the target étale site.
Source: Stacks Tag 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra).
Proof: on each comma object the two composites are pullback along the same
composite scheme morphism. Functoriality of Γ proves equality componentwise. -/
theorem moduliStructureMapApp_naturality {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    {T U : Y.EtaleSite} (f : T ⟶ U) :
    (moduliStructureMapApp hF Y φ T).comp
      (AlgebraicGeometry.Scheme.Γ.map
        ((AlgebraicGeometry.AlgebraicSpace.etaleForget Y).map f).op).hom =
    ((moduliDirectImage hF Y φ (moduliStructureSheaf F hF)).obj.map f.op).hom.comp
      (moduliStructureMapApp hF Y φ U) := by
  sorry

set_option linter.checkUnivs false in
/-- Target regular functions in the same ambient universe as the direct image.
Source: Stacks Tag 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliTargetStructurePresheaf {S : AlgebraicGeometry.Scheme.{u}}
    (Y : AlgebraicGeometry.AlgebraicSpace S) :
    Y.EtaleSiteᵒᵖ ⥤ CommRingCat.{max (u + 1) v w} where
  obj T := CommRingCat.of (ULift.{max (u + 1) v w}
    (AlgebraicGeometry.Scheme.Γ.obj
      (op ((AlgebraicGeometry.AlgebraicSpace.etaleForget Y).obj T.unop))))
  map f := CommRingCat.ofHom (AlgebraicGeometry.Scheme.Γ.map
    ((AlgebraicGeometry.AlgebraicSpace.etaleForget Y).map f.unop).op).hom.ulift

set_option linter.checkUnivs false in
/-- Universe transport preserves the target's regular-functions sheaf condition.
Source: Stacks Tags 06TV, 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra).
Proof: the target structure sheaf satisfies étale descent. Apply the canonical
ULift ring equivalences at every chart to its matching-family equalizer. -/
theorem moduliTargetStructurePresheaf_isSheaf {S : AlgebraicGeometry.Scheme.{u}}
    (Y : AlgebraicGeometry.AlgebraicSpace S) :
    Presheaf.IsSheaf Y.etaleTopology (moduliTargetStructurePresheaf.{u, v, w} Y) := by
  sorry

set_option linter.checkUnivs false in
/-- The target structure sheaf, canonically transported by ULift.ringEquiv.
Source: Stacks Tags 06TV, 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliTargetStructureSheaf {S : AlgebraicGeometry.Scheme.{u}}
    (Y : AlgebraicGeometry.AlgebraicSpace S) :
    Sheaf Y.etaleTopology CommRingCat.{max (u + 1) v w} :=
  ⟨moduliTargetStructurePresheaf.{u, v, w} Y, moduliTargetStructurePresheaf_isSheaf.{u, v, w} Y⟩

/-- Pullback of regular functions commutes with every target restriction.
Source: Stacks Tag 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra).
Proof: remove the canonical ULift transports. The equality is the naturality
identity moduliStructureMapApp_naturality, evaluated on the chart function. -/
theorem moduliStructureMap_naturality {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    {T U : Y.EtaleSiteᵒᵖ} (f : T ⟶ U) :
    (moduliTargetStructurePresheaf.{u, v, w} Y).map f ≫
      CommRingCat.ofHom ((moduliStructureMapApp hF Y φ U.unop).comp
        ULift.ringEquiv.toRingHom) =
    CommRingCat.ofHom ((moduliStructureMapApp hF Y φ T.unop).comp
      ULift.ringEquiv.toRingHom) ≫
        (moduliDirectImage hF Y φ (moduliStructureSheaf F hF)).obj.map f := by
  sorry

/-- The canonical map O_Y → φ_* O_F sends a regular function to all its pullbacks.
Source: Stacks Tag 06W6 (blueprint: def-sfb-stack-quasi-coherent-algebra). -/
def moduliStructureMap {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (Y : AlgebraicGeometry.AlgebraicSpace S)
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) :
    moduliTargetStructureSheaf.{u, v, w} Y ⟶
      moduliDirectImage hF Y φ (moduliStructureSheaf F hF) where
  hom :=
    { app := fun T ↦ CommRingCat.ofHom ((moduliStructureMapApp hF Y φ T.unop).comp
        ULift.ringEquiv.toRingHom)
      naturality := fun _ _ f ↦ moduliStructureMap_naturality hF Y φ f }

end CategoryTheory
