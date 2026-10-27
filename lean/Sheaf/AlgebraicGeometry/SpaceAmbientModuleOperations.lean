/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.CategoryTheory.CochainCoefficientUniverseTransport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-!
# Ambient-universe module operations on small étale sites of algebraic spaces

Source: Stacks Project, Properties of Spaces, Tags 03G8, 03H7 and 03LV;
Morphisms of Algebraic Spaces, Tag 03M8; Modules on Sites, Tag 03D7
(blueprint: def-sfb-space-ambient-module-operations).

A direct image is specified by a limit of sections on ALL étale scheme charts, together
with the restriction and module-map identities for the limit projections. This universal
property determines the functor up to its unique normalized natural isomorphism. Tensor
pullback is the left adjoint to this direct image, with its adjunction unit retained.
No arbitrary functor or unnormalized comparison is supplied as a hypothesis.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u m

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

namespace AmbientCoefficients

/-- The regular-function sheaf with section carriers lifted to the ambient universe.
Source: Stacks 03G8, 03D7 (blueprint: def-sfb-space-ambient-module-operations). -/
abbrev commStructureSheaf (X : AlgebraicSpace S) :=
  SheafOfModules.CochainUniverseTransport.ring.{u + 1, u, u, u + 1, m}
    X.commStructureSheaf

/-- Forget commutativity of the canonically lifted regular-function sheaf.
Source: Stacks 03G8, 03D7 (blueprint: def-sfb-space-ambient-module-operations). -/
abbrev structureSheaf (X : AlgebraicSpace S) :=
  (sheafCompose X.etaleTopology (forget₂ CommRingCat RingCat)).obj
    (commStructureSheaf.{u, m} X)

/-- The same module-sheaf category after canonical sectionwise coefficient transport.
Source: Stacks 03G8, 03D7 (blueprint: def-sfb-space-ambient-module-operations). -/
abbrev Modules (X : AlgebraicSpace S) :=
  SheafOfModules.{max (u + 1) m} (structureSheaf.{u, m} X)

/-- Pullback of functions in the same lifted coordinates.
Source: Stacks 03G8, 03D7 (blueprint: def-sfb-space-ambient-module-operations). -/
def moduleChartScalar (f : X ⟶ Y) (V : Y.EtaleSite) (q : ModuleChart f V) :
    (structureSheaf.{u, m} Y).obj.obj (op V) ⟶
      (structureSheaf.{u, m} X).obj.obj (op q.left) :=
  RingCat.ofHom (Scheme.Γ.map q.hom.left.left.op).hom.ulift

/-- A chart restriction is linear over the functions on `V`.
Source: Stacks, Tag 03M8 (blueprint: def-sfb-space-ambient-module-operations).
Proof: semilinearity of the module restriction, followed by functoriality of the two
pullbacks of regular functions along the commuting triangle of chart schemes. -/
theorem moduleChartMap_smul (f : X ⟶ Y) (M : Modules.{u, m} X) (V : Y.EtaleSite)
    {q r : ModuleChart f V} (a : q ⟶ r)
    (b : (structureSheaf.{u, m} Y).obj.obj (op V)) (m : M.val.obj (op r.left)) :
    M.val.map a.left.op (moduleChartScalar f V r b • m) =
      moduleChartScalar f V q b • M.val.map a.left.op m := by
  sorry

/-- Restriction between chart sections, viewed as a linear map over `Γ(V,𝒪_V)`.
Source: Stacks, Tag 03M8 (blueprint: def-sfb-space-ambient-module-operations). -/
def moduleChartMap (f : X ⟶ Y) (M : Modules.{u, m} X) (V : Y.EtaleSite)
    {q r : ModuleChart f V} (a : q ⟶ r) :
    (ModuleCat.restrictScalars (moduleChartScalar f V r).hom).obj
        (M.val.obj (op r.left)) ⟶
      (ModuleCat.restrictScalars (moduleChartScalar f V q).hom).obj
        (M.val.obj (op q.left)) :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (moduleChartScalar f V r).hom).obj
      (M.val.obj (op r.left)))
    (Y := (ModuleCat.restrictScalars (moduleChartScalar f V q).hom).obj
      (M.val.obj (op q.left)))
    { toFun := fun m ↦ M.val.map a.left.op m
      map_add' := (M.val.map a.left.op).hom.map_add
      map_smul' := moduleChartMap_smul f M V a }

/-- Identity law for the chart diagram.
Source: Stacks, Tag 03M8 (blueprint: def-sfb-space-ambient-module-operations).
Proof: the restriction of `M` along the identity is the identity on every section. -/
theorem moduleChartMap_id (f : X ⟶ Y) (M : Modules.{u, m} X) (V : Y.EtaleSite)
    (q : ModuleChart f V) : moduleChartMap f M V (𝟙 q) = 𝟙 _ := by
  sorry

/-- Composition law for the chart diagram.
Source: Stacks, Tag 03M8 (blueprint: def-sfb-space-ambient-module-operations).
Proof: both maps are the iterated module restriction along the composite chart map. -/
theorem moduleChartMap_comp (f : X ⟶ Y) (M : Modules.{u, m} X) (V : Y.EtaleSite)
    {q r t : ModuleChart f V} (a : q ⟶ r) (b : r ⟶ t) :
    moduleChartMap f M V (a ≫ b) = moduleChartMap f M V b ≫ moduleChartMap f M V a := by
  sorry

/-- The diagram whose limit is the compatible sections on all scheme charts of `X ×_Y V`.
Source: Stacks, Tags 03H7 and 03M8 (blueprint: def-sfb-space-ambient-module-operations). -/
def moduleChartDiagram (f : X ⟶ Y) (M : Modules.{u, m} X) (V : Y.EtaleSite) :
    (ModuleChart f V)ᵒᵖ ⥤ ModuleCat.{max (u + 1) m} ((structureSheaf.{u, m} Y).obj.obj (op V)) where
  obj q := (ModuleCat.restrictScalars (moduleChartScalar f V q.unop).hom).obj
    (M.val.obj (op q.unop.left))
  map a := moduleChartMap f M V a.unop
  map_id q := moduleChartMap_id f M V q.unop
  map_comp a b := moduleChartMap_comp f M V b.unop a.unop

/-- A normalized direct image: its sections are limits of the actual chart module diagram;
its maps are characterized by their components on EVERY chart. The projection identities
include both restrictions in the test scheme and morphisms of modules.
Source: Stacks, Tags 03H7 and 03M8 (blueprint: def-sfb-space-ambient-module-operations). -/
structure ModuleDirectImageModel (f : X ⟶ Y) where
  /-- Module direct image on the small étale sites. -/
  functor : Modules.{u, m} X ⥤ Modules.{u, m} Y
  /-- Projection of a section to a chart of the fibre product. -/
  projection (M : Modules.{u, m} X) (V : Y.EtaleSite) :
    (Functor.const (ModuleChart f V)ᵒᵖ).obj ((functor.obj M).val.obj (op V)) ⟶
      moduleChartDiagram f M V
  /-- Compatible sections are exactly the limit, with its specified projections. -/
  isLimit (M : Modules.{u, m} X) (V : Y.EtaleSite) :
    IsLimit (Cone.mk ((functor.obj M).val.obj (op V)) (projection M V))
  /-- Naturality for module morphisms, on every chart section. -/
  map_projection {M N : Modules.{u, m} X} (a : M ⟶ N) (V : Y.EtaleSite)
    (q : ModuleChart f V) (s : (functor.obj M).val.obj (op V)) :
    (projection N V).app (op q) ((functor.map a).val.app (op V) s) =
      a.val.app (op q.left) ((projection M V).app (op q) s)
  /-- Naturality for restrictions of the test scheme, on every chart section. -/
  restriction_projection (M : Modules.{u, m} X) {V W : Y.EtaleSite} (a : V ⟶ W)
    (q : ModuleChart f V) (s : (functor.obj M).val.obj (op W)) :
    (projection M V).app (op q) ((functor.obj M).val.map a.op s) =
      (projection M W).app (op ((moduleChartPost f a).obj q)) s

/-- The compatible-chart-section universal property is realized by a module direct image.
Source: Stacks, Tags 03H7, 03G8 and 03M8
(blueprint: def-sfb-space-ambient-module-operations).
Proof: extend each module to étale algebraic spaces by compatible sections. On a scheme
atlas this is the descent equalizer, so the result is a sheaf and is independent of the
atlas. Pullback of regular functions supplies the scalar action on every chart. Sections
on `V` are the compatible sections on `X ×_Y V`; restrictions and module maps act on
these same families componentwise. These are limits with the displayed projections.
The site of all charts has objects in universe `u+1`, contained in the ambient
coefficient universe. Its limits and the module sheafification therefore exist there.
The limit property and the two projection identities determine the functor up to its
unique normalized natural isomorphism; this is a universal-property construction. -/
theorem moduleDirectImageModel_nonempty (f : X ⟶ Y) :
    Nonempty (ModuleDirectImageModel f) := by
  sorry

/-- The chart universal property determines direct image up to a unique normalized iso.
Source: Stacks, Tags 03H7 and 03M8 (blueprint: def-sfb-space-ambient-module-operations).
Proof: the universal property gives the unique section map between the two limits on
`V`. The projection identities make these maps natural in `V` and in the module. Their
composites have the projections of the identity and hence equal the identity, by limit
uniqueness. The same argument proves uniqueness of the normalized natural isomorphism. -/
theorem moduleDirectImageModel_unique (f : X ⟶ Y) (D E : ModuleDirectImageModel f) :
    ∃! e : D.functor ≅ E.functor,
      ∀ (M : Modules.{u, m} X) (V : Y.EtaleSite) (q : ModuleChart f V)
        (s : (D.functor.obj M).val.obj (op V)),
        (E.projection M V).app (op q) ((e.hom.app M).val.app (op V) s) =
          (D.projection M V).app (op q) s := by
  sorry

/-- The normalized direct-image model, selected by its complete limit universal property.
Source: Stacks, Tags 03H7 and 03M8 (blueprint: def-sfb-space-ambient-module-operations). -/
def moduleDirectImageModel (f : X ⟶ Y) : ModuleDirectImageModel f :=
  Classical.choice (moduleDirectImageModel_nonempty f)

/-- Canonical module direct image, retaining the compatible-section model above.
Source: Stacks, Tag 03G8 (blueprint: def-sfb-space-ambient-module-operations). -/
def moduleDirectImage (f : X ⟶ Y) : Modules.{u, m} X ⥤ Modules.{u, m} Y :=
  (moduleDirectImageModel f).functor

/-- Tensor pullback exists as the left adjoint of the specified module direct image.
Source: Stacks, Tag 03D7 and Tag 03G8 (blueprint: def-sfb-space-ambient-module-operations).
Proof: on the enlarged étale ringed sites form the usual inverse image and extension of
scalars, and transport it through the scheme-chart equivalences. The tensor universal
property identifies its maps to `F` with maps to the compatible-section direct image.
This supplies the adjunction to the direct image already fixed above; uniqueness of a
left adjoint identifies any two such tensor constructions compatibly with their units. -/
theorem moduleDirectImage_isRightAdjoint (f : X ⟶ Y) :
    (moduleDirectImage f).IsRightAdjoint := by
  sorry

attribute [instance] moduleDirectImage_isRightAdjoint

/-- The tensor pullback, specified by its adjunction to the canonical direct image.
Source: Stacks, Tags 03D7 and 03G8 (blueprint: def-sfb-space-ambient-module-operations). -/
def moduleTensorPullback (f : X ⟶ Y) : Modules.{u, m} Y ⥤ Modules.{u, m} X :=
  (moduleDirectImage f).leftAdjoint

/-- The unit and counit fixing the normalization of tensor pullback.
Source: Stacks, Tag 03D7 (blueprint: def-sfb-space-ambient-module-operations). -/
def moduleTensorAdjunction (f : X ⟶ Y) : moduleTensorPullback f ⊣ moduleDirectImage f :=
  Adjunction.ofIsRightAdjoint (moduleDirectImage f)

/-- The local tensor `b ⊗ m`, for `m` represented on `V` and a chart over `V`.
The unit sends `m` to `1 ⊗ m`; projection to the chart and multiplication by `b` give
`b ⊗ m`. This uses the chosen adjunction, not a freely chosen map into the pullback.
Source: Stacks, Tags 03D7, 03LV (blueprint: def-sfb-space-ambient-module-operations). -/
def moduleTensorSection (f : X ⟶ Y) (M : Modules.{u, m} Y) (V : Y.EtaleSite)
    (q : ModuleChart f V) (b : (structureSheaf.{u, m} X).obj.obj (op q.left))
    (m : M.val.obj (op V)) : ((moduleTensorPullback f).obj M).val.obj (op q.left) :=
  b • @id (((moduleTensorPullback f).obj M).val.obj (op q.left))
    (((moduleDirectImageModel f).projection ((moduleTensorPullback f).obj M) V).app
      (op q) (((moduleTensorAdjunction f).unit.app M).val.app (op V) m))

end AmbientCoefficients

end AlgebraicGeometry.AlgebraicSpace
