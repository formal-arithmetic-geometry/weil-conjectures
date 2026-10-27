module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbelianDirectImage
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # The canonical small-etale cohomology edge for representable space maps

Source: Stacks Project, Properties of Spaces, Tags 03G2(4), 03LR and 03G8;
Cohomology on Sites, Tags 0732 and 0733
(blueprint: def-sfb-space-representable-cohomology-edge).

The coefficient lift retains every original section and its addition. It places
cohomology in the standard universe of the recorded abelian direct-image interface.
The comparison of module and additive direct images is fixed on every section by the
projection to the actual representing fibre-product chart. The constant-sheaf map
is constructed from sheafification of the constant-presheaf unit, then transposed
through the actual inverse-image/direct-image adjunction. No isomorphism or cohomology
map is chosen without its normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The original small-etale site has small Ext groups in the stated universe.
Proof: restrict to a small affine etale basis, as in Tags 03ED and 039Z. Abelian
sheaves on that basis form a Grothendieck abelian category with enough injectives.
The restriction equivalence transfers injective resolutions to the original site.
Its Hom groups are in universe u+1, so Ext computed by these resolutions is u+1-small.
Source: Stacks Project, Properties of Spaces, Tag 03ED; Sites, Tag 039Z;
Cohomology on Sites, enough injectives
(blueprint: def-sfb-space-representable-cohomology-edge). -/
@[instance] theorem etaleAdditiveHasExt (X : AlgebraicSpace S) :
    HasExt.{u + 1} (Sheaf X.etaleTopology AddCommGrpCat.{u + 1}) := by
  sorry

/-- An affine space morphism is representable by schemes.
Proof: on every affine test scheme use the representing affine scheme in MapIsAffine.
For a general test scheme cover by affine opens. The resulting affine schemes glue:
on overlaps their pullback universal properties give unique compatible isomorphisms.
Scheme open gluing produces the representing scheme, with both projections. This is
exactly relative representability for Yoneda; no atlas is chosen as extra input.
Source: Stacks Project, Morphisms of Spaces, Tag 03WF; Spaces, scheme gluing
(blueprint: def-sfb-space-representable-cohomology-edge). -/
theorem affine_relativelyRepresentable (f : Y ⟶ X) (hf : MapIsAffine f) :
    yoneda.relativelyRepresentable f.hom.hom := by
  sorry

/-- The underlying additive sheaf with its canonical coefficient universe lift.
This is the existing forgetful functor followed by Mathlib's ULift functor. Section
values are ULift of the original groups, and every restriction is the lifted original
restriction. This exact fully faithful coefficient transport preserves the sheaf and
cohomology constructions, as can be checked on a small affine etale basis.
Source: Stacks Project, Properties of Spaces, Tags 03G2(4), 03LR and 03G8;
Cohomology on Sites, Tags 0732 and 0733
(blueprint: def-sfb-space-representable-cohomology-edge). -/
abbrev liftedAdditive (X : AlgebraicSpace S) :
    X.Modules ⥤ Sheaf X.etaleTopology AddCommGrpCat.{u + 1} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafCompose X.etaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}

variable (f : Y ⟶ X) (hf : yoneda.relativelyRepresentable f.hom.hom)
/-- Continuity of the already chosen representing base-change functor.
The proof is the recorded continuity field of RepresentableEtaleBaseChange; there is
no second site functor or choice of pullback squares.
Source: Stacks Project, Properties of Spaces, Tags 03G2(4), 03LR and 03G8;
Cohomology on Sites, Tags 0732 and 0733
(blueprint: def-sfb-space-representable-cohomology-edge). -/
instance baseChangeContinuous :
    (representableEtaleBaseChange f hf).functor.IsContinuous X.etaleTopology Y.etaleTopology :=
  (representableEtaleBaseChange f hf).continuous

/-- The actual left adjoint to the recorded representable abelian direct image.
Mathlib constructs it by left Kan extension and sheafification. The base-change
functor and its representing squares are the existing recorded construction.
Source: Stacks Project, Properties of Spaces, Tags 03G2(4), 03LR and 03G8;
Cohomology on Sites, Tags 0732 and 0733
(blueprint: def-sfb-space-representable-cohomology-edge). -/
abbrev representableAbelianInverseImage :=
  (representableEtaleBaseChange f hf).functor.sheafPullback
    AddCommGrpCat.{u + 1} X.etaleTopology Y.etaleTopology

/-- The actual inverse-image/direct-image adjunction, including its counit.
Source: Stacks Project, Properties of Spaces, Tags 03G2(4), 03LR and 03G8;
Cohomology on Sites, Tags 0732 and 0733
(blueprint: def-sfb-space-representable-cohomology-edge). -/
abbrev representableAbelianAdjunction :=
  (representableEtaleBaseChange f hf).functor.sheafAdjunctionContinuous
    AddCommGrpCat.{u + 1} X.etaleTopology Y.etaleTopology

/-- The abelian inverse image is additive.
Proof: direct image is sectionwise precomposition and preserves addition of maps.
Transport the addition identity through the adjunction Hom equivalence. This is
also the abelian-group lift of the geometric inverse image of Tag 03G2(4).
Source: Stacks Project, Properties of Spaces, Tags 03G2(4), 03LR and 03G8;
Cohomology on Sites, Tags 0732 and 0733
(blueprint: def-sfb-space-representable-cohomology-edge). -/
@[instance] theorem representableAbelianInverseImage_additive :
    (representableAbelianInverseImage f hf).Additive := by
  sorry

/-- The abelian inverse image is left exact.
Proof: Tag 03G2(4) identifies this base-change functor with the small-etale geometric
morphism. Its inverse image preserves finite limits of set sheaves. Addition and
zero transport across those limits, so the induced abelian inverse image preserves
kernels and finite products. Uniqueness of left adjoints identifies it with the
specific Mathlib left adjoint used here.
Source: Stacks Project, Properties of Spaces, Tags 03G2(4), 03LR and 03G8;
Cohomology on Sites, Tags 0732 and 0733
(blueprint: def-sfb-space-representable-cohomology-edge). -/
@[instance] theorem representableAbelianInverseImage_leftExact :
    PreservesFiniteLimits (representableAbelianInverseImage f hf) := by
  sorry

/-- The abelian inverse image is right exact.
Proof: it is the left adjoint in representableAbelianAdjunction. Every left adjoint
preserves colimits, in particular finite colimits and cokernels.
Source: Stacks Project, Properties of Spaces, Tags 03G2(4), 03LR and 03G8;
Cohomology on Sites, Tags 0732 and 0733
(blueprint: def-sfb-space-representable-cohomology-edge). -/
@[instance] theorem representableAbelianInverseImage_rightExact :
    PreservesFiniteColimits (representableAbelianInverseImage f hf) := by
  sorry

/-- The constant-sheaf unit sends every local integer to that same integer.
It is sheafification of the constant-presheaf unit, evaluated after the existing
scheme base-change functor. The displayed formula fixes its normalization globally,
including when neither space is a terminal object of its scheme-valued small site.
Source: Stacks Project, Properties of Spaces, Tags 03G2(4), 03LR and 03G8;
Cohomology on Sites, Tags 0732 and 0733
(blueprint: def-sfb-space-representable-cohomology-edge). -/
def representableConstantUnit :
    (constantSheaf X.etaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (representableAbelianDirectImage f hf).obj
        ((constantSheaf Y.etaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  ((sheafificationAdjunction X.etaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    { app := fun T ↦
        (toSheafify Y.etaleTopology
          ((Functor.const Y.EtaleSiteᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
            ((representableEtaleBaseChange f hf).functor.op.obj T)
      naturality := fun _ _ a ↦
        (toSheafify Y.etaleTopology
          ((Functor.const Y.EtaleSiteᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality
            ((representableEtaleBaseChange f hf).functor.op.map a) }

/-- The canonical inverse-image comparison for the constant integer sheaves.
It is the transpose of representableConstantUnit under the actual sheaf adjunction.
Source: Stacks Project, Properties of Spaces, Tags 03G2(4), 03LR and 03G8;
Cohomology on Sites, Tags 0732 and 0733
(blueprint: def-sfb-space-representable-cohomology-edge). -/
def representableConstantComparison :
    (representableAbelianInverseImage f hf).obj
        ((constantSheaf X.etaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶
      (constantSheaf Y.etaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  ((representableAbelianAdjunction f hf).homEquiv _ _).symm
    (representableConstantUnit f hf)

/-- The normalized constant-integer comparison is invertible.
Proof: inverse image of the geometric morphism of Tag 03G2(4) preserves constant
objects, as it preserves finite limits and all colimits. Present the constant
abelian group by free abelian generators and relations; the sheafification unit
comparison sends each generator to the same local constant section. Thus its
comparison is precisely representableConstantComparison and is invertible.
Source: Stacks Project, Properties of Spaces, Tags 03G2(4), 03LR and 03G8;
Cohomology on Sites, Tags 0732 and 0733
(blueprint: def-sfb-space-representable-cohomology-edge). -/
@[instance] theorem representableConstantComparison_isIso :
    IsIso (representableConstantComparison f hf) := by
  sorry

/-- The terminal chart of the fibre product used to compute the direct image.
Its triangle comes from the representing pullback square, not an arbitrary map.
Source: Stacks Project, Properties of Spaces, Tags 03G2(4), 03LR and 03G8;
Cohomology on Sites, Tags 0732 and 0733
(blueprint: def-sfb-space-representable-cohomology-edge). -/
def representableModuleChart (V : X.EtaleSite) : ModuleChart f V :=
  CostructuredArrow.mk (Y := (representableEtaleBaseChange f hf).functor.obj V)
    (CostructuredArrow.homMk ((representableEtaleBaseChange f hf).projection.app V)
      ((representableEtaleBaseChange f hf).square V).w.symm)

/-- Module and additive direct images have their unique section-normalized comparison.
Proof: for an etale test V, the representing scheme Y times_X V is a terminal object
of ModuleChart f V by its pullback universal property. Its opposite is initial, so
the limit specifying moduleDirectImage is its value there. The cone projection is
therefore invertible. Forget scalars and lift coefficients: this is the additive
precomposition value of representableAbelianDirectImage. Naturality of the recorded
cone projections gives naturality in V and in F. Those same projections force every
component of any normalized comparison, proving uniqueness.
Source: Stacks Project, Properties of Spaces, Tags 03G2(4), 03LR and 03G8;
Cohomology on Sites, Tags 0732 and 0733
(blueprint: def-sfb-space-representable-cohomology-edge). -/
theorem representableModuleDirectImageComparison_existsUnique :
    ∃! e : moduleDirectImage f ⋙ liftedAdditive X ≅
        liftedAdditive Y ⋙ representableAbelianDirectImage f hf,
      ∀ (F : Y.Modules) (V : X.EtaleSite) (s : ((moduleDirectImage f).obj F).val.obj (op V)),
        (e.hom.app F).hom.app (op V) (ULift.up s) =
          ULift.up (((moduleDirectImageModel f).projection F V).app
            (op (representableModuleChart f hf V)) s) := by
  sorry

/-- The module/additive direct-image comparison selected by its complete normalization.
The existence-uniqueness theorem fixes every chart section, so this universal-property
choice determines the comparison up to equality, not merely abstract isomorphism.
Source: Stacks Project, Properties of Spaces, Tags 03G2(4), 03LR and 03G8;
Cohomology on Sites, Tags 0732 and 0733
(blueprint: def-sfb-space-representable-cohomology-edge). -/
def representableModuleDirectImageComparison :
    moduleDirectImage f ⋙ liftedAdditive X ≅
      liftedAdditive Y ⋙ representableAbelianDirectImage f hf :=
  (representableModuleDirectImageComparison_existsUnique f hf).choose

/-- The canonical edge H^q(X,f_*F) to H^q(Y,F), before any affineness hypothesis.
First identify the module direct image with the additive direct image, then apply
exact abelian inverse image to the Ext class using the normalized constant-sheaf
comparison, and finally apply the actual adjunction counit. This is the standard
Leray bottom edge (Tag 0732), with the defining global-sections map in degree zero.
Source: Stacks Project, Properties of Spaces, Tags 03G2(4), 03LR and 03G8;
Cohomology on Sites, Tags 0732 and 0733
(blueprint: def-sfb-space-representable-cohomology-edge). -/
def representableCohomologyEdge (F : Y.Modules) (q : ℕ) :
    Sheaf.H ((liftedAdditive X).obj ((moduleDirectImage f).obj F)) q →+
      Sheaf.H ((liftedAdditive Y).obj F) q :=
  (Sheaf.H.map ((representableAbelianAdjunction f hf).counit.app
      ((liftedAdditive Y).obj F)) q).comp
    ((Sheaf.H.mapFunctor (representableAbelianInverseImage f hf)
      (asIso (representableConstantComparison f hf)).symm
      ((representableAbelianDirectImage f hf).obj ((liftedAdditive Y).obj F)) q).comp
        (Sheaf.H.map ((representableModuleDirectImageComparison f hf).hom.app F) q))

end AlgebraicGeometry.AlgebraicSpace
