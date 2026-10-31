/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import WeilConjectures.AlgebraicGeometry.EtaleAtlasPresentation
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import WeilConjectures.AlgebraicGeometry.RelativeSpecBaseChange
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.EtaleRelationQuotient
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Relative Spec for algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tags 081V and 081W; the property tests
are Tags 03ZQ and 0410 (blueprint: lem-sfb-space-relative-spec-correspondence).

The direct-image algebra is pinned to the existing compatible-chart-section limit.
The inverse equivalence is relative Spec, with its counit identification. Chart maps
and arbitrary base change retain their section normalizations, including zero algebras.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Spaces affine over `X`, with all maps over `X`. Affineness is representability
with the scheme affine property on every scheme test.
Source: Stacks, Morphisms of Spaces, Tags 03WG and 081V
(blueprint: lem-sfb-space-relative-spec-correspondence). -/
abbrev AffineOver (X : AlgebraicSpace S) :=
  ObjectProperty.FullSubcategory (fun Y : Over X ↦
    IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) Y.hom.hom.hom)

/-- The canonical algebra `f_* O_Z`, specified by its module limit and ring-valued
chart projections. These projections identify its sections with regular functions
on the fibre product, and fix its multiplication, unit and structure morphism.
Source: Stacks, Morphisms of Spaces, Tag 081V
(blueprint: lem-sfb-space-relative-spec-correspondence). -/
structure StructureAlgebraModel {Z X : AlgebraicSpace S} (f : Z ⟶ X) where
  /-- The algebra sheaf on the target. -/
  algebra : X.CommAlgebraSheaf
  /-- Its underlying module is the already specified direct image. -/
  underlying : algebra.toModule ≅
    (moduleDirectImage f).obj (SheafOfModules.unit Z.structureSheaf)
  /-- Restriction of functions to every compatible scheme chart. -/
  projection (V : X.EtaleSite) (q : ModuleChart f V) :
    algebra.right.obj.obj (op V) ⟶ Z.commStructureSheaf.obj.obj (op q.left)
  /-- The ring projections are precisely the existing module-limit projections. -/
  projection_underlying (V : X.EtaleSite) (q : ModuleChart f V)
      (s : algebra.right.obj.obj (op V)) :
    projection V q s =
      ((moduleDirectImageModel f).projection (SheafOfModules.unit Z.structureSheaf) V).app
        (op q) (underlying.hom.val.app (op V) s)
  /-- The structure map pulls regular functions back along the chart projection. -/
  projection_structure (V : X.EtaleSite) (q : ModuleChart f V) :
    algebra.hom.hom.app (op V) ≫ projection V q = Scheme.Γ.map q.hom.left.left.op

/-- A relative-Spec anti-equivalence, normalized as direct image on objects and maps,
with integral, finite, and algebra-finite-presentation tests. The chart and base-change
clauses are stated separately below, on this same data.
Source: Stacks, Morphisms of Spaces, Tags 081V, 081W, 03ZQ and 0410
(blueprint: lem-sfb-space-relative-spec-correspondence). -/
structure RelativeSpecData (X : AlgebraicSpace S) where
  /-- The section-normalized direct-image algebras. -/
  directImage (Y : AffineOver X) : StructureAlgebraModel Y.obj.hom
  /-- The contravariant equivalence with quasi-coherent algebra sheaves. -/
  equivalence : (AffineOver X)ᵒᵖ ≌ X.QCAlg
  /-- Its value is canonically the direct-image algebra. -/
  directImageIso (Y : AffineOver X) :
    (equivalence.functor.obj (op Y)).obj ≅ (directImage Y).algebra
  /-- On morphisms the algebra map is pullback of functions, on every compatible chart. -/
  map_projection {Y Z : AffineOver X} (h : Y ⟶ Z) (V : X.EtaleSite)
      (q : ModuleChart Y.obj.hom V) (r : ModuleChart Z.obj.hom V)
      (a : q.left.obj.left ⟶ r.left.obj.left)
      (ha : yoneda.map a ≫ r.left.obj.hom = q.left.obj.hom ≫ h.hom.left.hom.hom)
      (hp : a ≫ r.hom.left = q.hom.left) :
    (((directImageIso Z).inv ≫ (equivalence.functor.map h.op).hom ≫
        (directImageIso Y).hom).right.hom.app (op V)) ≫
        (directImage Y).projection V q =
      (directImage Z).projection V r ≫ Scheme.Γ.map a.left.op
  /-- Integral morphisms correspond exactly to integral algebras. -/
  integral_iff (Y : AffineOver X) :
    IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) Y.obj.hom.hom.hom ↔
      (directImage Y).algebra.IsIntegral
  /-- Finite morphisms correspond exactly to algebras finite as modules. -/
  finite_iff (Y : AffineOver X) :
    IsRepresentableWith (fun _ _ p ↦ IsFinite p.left) Y.obj.hom.hom.hom ↔
      (directImage Y).algebra.IsFinite
  /-- Finite presentation includes quasi-compactness and a quasi-compact diagonal. -/
  finitePresentation_iff (Y : AffineOver X) :
    (MapIsQuasiCompact Y.obj.hom.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal Y.obj.hom.hom.hom) ∧
      MapIsLocallyOfFinitePresentation Y.obj.hom) ↔
        (directImage Y).algebra.IsFinitePresentation

/-- Relative Spec is the inverse of the same normalized anti-equivalence.
Source: Stacks, Morphisms of Spaces, Tag 081W
(blueprint: lem-sfb-space-relative-spec-correspondence). -/
def RelativeSpecData.relativeSpec {X : AlgebraicSpace S} (C : RelativeSpecData X)
    (A : X.QCAlg) : AffineOver X :=
  (C.equivalence.inverse.obj A).unop

/-- The counit identifies an algebra with the functions on its relative spectrum.
Source: Stacks, Morphisms of Spaces, Tags 081V and 081W
(blueprint: lem-sfb-space-relative-spec-correspondence). -/
def RelativeSpecData.counitAlgebra {X : AlgebraicSpace S} (C : RelativeSpecData X)
    (A : X.QCAlg) : A.obj ≅ (C.directImage (C.relativeSpec A)).algebra :=
  (ObjectProperty.ι _).mapIso (C.equivalence.counitIso.app A).symm ≪≫
    C.directImageIso (C.relativeSpec A)

/-- The map from a scheme chart of relative Spec to the affine spectrum of its algebra
of sections. Its ring map is the counit followed by the actual restriction of functions.
Source: Stacks, Morphisms of Spaces, Tags 081V and 081W
(blueprint: lem-sfb-space-relative-spec-correspondence). -/
def RelativeSpecData.chartMap {X : AlgebraicSpace S} (C : RelativeSpecData X)
    (A : X.QCAlg) (V : X.EtaleSite) (q : ModuleChart (C.relativeSpec A).obj.hom V) :
    (C.relativeSpec A).obj.left.etaleForget.obj q.left ⟶
      Spec (A.obj.right.obj.obj (op V)) :=
  ((C.relativeSpec A).obj.left.etaleForget.obj q.left).toSpecΓ ≫
    Spec.map ((C.counitAlgebra A).hom.right.hom.app (op V) ≫
      (C.directImage (C.relativeSpec A)).projection V q)

/-- The affine-chart description, including the formula on algebra maps.
Source: Stacks, Morphisms of Spaces, Tags 081V and 081W
(blueprint: lem-sfb-space-relative-spec-correspondence). -/
def RelativeSpecData.HasChartFormula {X : AlgebraicSpace S} (C : RelativeSpecData X) :
    Prop :=
  (∀ (A : X.QCAlg) (V : X.EtaleSite), IsAffine (X.etaleForget.obj V) →
    ∀ q : ModuleChart (C.relativeSpec A).obj.hom V,
      IsPullback q.left.obj.hom (yoneda.map q.hom.left)
        (C.relativeSpec A).obj.hom.hom.hom V.obj.hom → IsIso (C.chartMap A V q)) ∧
  (∀ (A B : X.QCAlg) (φ : A ⟶ B) (V : X.EtaleSite),
    IsAffine (X.etaleForget.obj V) →
    ∀ (q : ModuleChart (C.relativeSpec B).obj.hom V)
      (r : ModuleChart (C.relativeSpec A).obj.hom V)
      (a : q.left.obj.left ⟶ r.left.obj.left),
      yoneda.map a ≫ r.left.obj.hom = q.left.obj.hom ≫
        (C.equivalence.inverse.map φ).unop.hom.left.hom.hom →
      a ≫ r.hom.left = q.hom.left →
      a.left ≫ C.chartMap A V r =
        C.chartMap B V q ≫ Spec.map (φ.hom.right.hom.app (op V)))

/-- The algebra structure on tensor pullback is fixed on local pure tensors. The
underlying module and tensor sections are exactly those of the dependency interface.
Source: Stacks, Morphisms of Spaces, Tag 081V, arbitrary base change
(blueprint: lem-sfb-space-relative-spec-correspondence). -/
def IsTensorAlgebraPullback {X' X : AlgebraicSpace S} (g : X' ⟶ X)
    (A : X.QCAlg) (B : X'.QCAlg)
    (e : B.obj.toModule ≅ (moduleTensorPullback g).obj A.obj.toModule) : Prop :=
  (∀ (V : X.EtaleSite) (q : ModuleChart g V),
    e.inv.val.app (op q.left) (moduleTensorSection g A.obj.toModule V q 1
        (1 : A.obj.right.obj.obj (op V))) =
      (1 : B.obj.right.obj.obj (op q.left))) ∧
  (∀ (V : X.EtaleSite) (q : ModuleChart g V)
      (b b' : X'.structureSheaf.obj.obj (op q.left)) (s t : A.obj.right.obj.obj (op V)),
    @id (B.obj.right.obj.obj (op q.left))
      (e.inv.val.app (op q.left) (moduleTensorSection g A.obj.toModule V q b s)) *
      @id (B.obj.right.obj.obj (op q.left))
        (e.inv.val.app (op q.left) (moduleTensorSection g A.obj.toModule V q b' t)) =
    e.inv.val.app (op q.left) (moduleTensorSection g A.obj.toModule V q (b * b') (s * t)))

/-- Normalization of the base-change arrow by `b ⊗ s ↦ b h^*(s)` on every compatible
scheme chart. Together with the cartesian square this fixes the canonical comparison,
so its uniqueness also gives naturality in algebra maps and in iterated base change.
Source: Stacks, Morphisms of Spaces, Tag 081V, last sentence of proof
(blueprint: lem-sfb-space-relative-spec-correspondence). -/
def IsRelativeSpecBaseChangeArrow (C : ∀ X : AlgebraicSpace S, RelativeSpecData X)
    {X' X : AlgebraicSpace S} (g : X' ⟶ X) (A : X.QCAlg) (B : X'.QCAlg)
    (e : B.obj.toModule ≅ (moduleTensorPullback g).obj A.obj.toModule)
    (h : ((C X').relativeSpec B).obj.left ⟶ ((C X).relativeSpec A).obj.left) : Prop :=
  IsPullback h ((C X').relativeSpec B).obj.hom ((C X).relativeSpec A).obj.hom g ∧
  ∀ (V : X.EtaleSite) (c : ModuleChart g V)
    (q : ModuleChart ((C X').relativeSpec B).obj.hom c.left)
    (r : ModuleChart ((C X).relativeSpec A).obj.hom V)
    (a : q.left.obj.left ⟶ r.left.obj.left),
    yoneda.map a ≫ r.left.obj.hom = q.left.obj.hom ≫ h.hom.hom →
    a ≫ r.hom.left = q.hom.left ≫ c.hom.left →
    ∀ (b : X'.structureSheaf.obj.obj (op c.left)) (s : A.obj.right.obj.obj (op V)),
      ((C X').directImage ((C X').relativeSpec B)).projection c.left q
        (((C X').counitAlgebra B).hom.right.hom.app (op c.left)
          (e.inv.val.app (op c.left) (moduleTensorSection g A.obj.toModule V c b s))) =
      @id (((C X').relativeSpec B).obj.left.commStructureSheaf.obj.obj (op q.left))
        ((Scheme.Γ.map q.hom.left.left.op) b) *
        @id (((C X').relativeSpec B).obj.left.commStructureSheaf.obj.obj (op q.left))
        ((Scheme.Γ.map a.left.op)
          (((C X).directImage ((C X).relativeSpec A)).projection V r
            (((C X).counitAlgebra A).hom.right.hom.app (op V) s)))

/-- The normalized anti-equivalence, chart formulas, arbitrary tensor base change,
and integral/finite/finite-presentation tests for algebraic spaces.
Source: Stacks, Morphisms of Spaces, Tags 081V, 081W, 03ZQ and 0410
(blueprint: lem-sfb-space-relative-spec-correspondence).

Proof:
1. Choose an affine-component étale atlas by lem-a1-space-affine-etale-cover and its
   relation by lem-a1-etale-atlas-presentation. Restrict the algebra and its operations;
   lem-sfb-space-qcoh-groupoid-equivalence supplies the descent isomorphism and cocycle.
   The restriction/tensor comparison is lem-trf-space-etale-module-pushforward-restriction.
2. Form the scheme spectra on the atlas and relation using
   lem-weil-pbc-affine-morphism-relative-spec. By lem-weil-pbc-relative-spec-base-change
   their source and target maps are étale. The cartesian source square and the monic
   original relation prove monicity. Unit, inverse and cocycle give reflexivity,
   symmetry and transitivity on all test schemes. Fibre products are supplied by
   lem-trf-space-fibre-products-etale-covers.
3. Take the quotient by lem-trf-etale-relation-quotient. Its pullback to the atlas is
   the constructed scheme spectrum: lift a section locally to the atlas, use the
   unique relation arrow to adjust its base, and use the identity arrow to prove
   uniqueness. Apply lem-sfb-space-affine-locality to conclude affineness.
4. By lem-trf-space-etale-module-pushforward-restriction the direct image restricts
   to the scheme direct image. The scheme counits descend by the fully faithful
   groupoid equivalence; their multiplicativity and unit equations hold on the atlas.
   Quasi-coherence is local by def-trf-space-quasi-coherent-module. Restriction to any
   affine étale chart gives the displayed spectrum and its normalized chart map.
5. Descend scheme maps and algebra maps through the relation. Their inverse operations
   and identity/composition equations hold on the atlas. The scheme counits descend
   to recover every affine space. The scheme morphism formula gives map_projection
   and HasChartFormula, hence the stated anti-equivalence on the actual categories.
6. For arbitrary g, lem-sfb-space-module-pullback-quasicoherent gives quasi-coherence
   of tensor pullback. Over an atlas of its source, pull back the original atlas;
   lem-trf-space-fibre-products-etale-covers gives a scheme étale cover. The localized
   tensor comparison and scheme relative-Spec base change identify the spectra there.
   The maps and inverses agree on overlaps and glue. On pure tensors the map is
   b tensor s mapped to b times the pullback of s. Full faithfulness proves its
   uniqueness; the same normalization gives naturality and successive-base-change
   compatibility, including identity maps.
7. Integral and finite properties are the affine ring tests on these charts. Pass
   between an affine-component atlas and all scheme tests using
   lem-sfb-integral-affine-cover-criterion, lem-weil-pbc-finite-local-on-target and
   lem-sfb-space-integral-finite-etale-locality. The empty atlas is allowed.
8. Affine scheme base changes are quasi-compact and quasi-separated by
   lem-weil-pbc-affine-morphism-permanence. Thus finite presentation reduces to local
   finite presentation. Apply lem-sfb-space-local-properties-chart-test and
   lem-weil-pbc-lfp-affine-opens-finite-presentation to identify this with algebra
   finite presentation on every affine étale chart, in both directions. -/
theorem space_relative_spec_correspondence (S : Scheme.{u}) :
    ∃ C : ∀ X : AlgebraicSpace S, RelativeSpecData X,
      (∀ X : AlgebraicSpace S, (C X).HasChartFormula) ∧
      ∀ (X' X : AlgebraicSpace S) (g : X' ⟶ X) (A : X.QCAlg),
        ∃ (B : X'.QCAlg)
          (e : B.obj.toModule ≅ (moduleTensorPullback g).obj A.obj.toModule),
          IsTensorAlgebraPullback g A B e ∧
          ∃! h : ((C X').relativeSpec B).obj.left ⟶ ((C X).relativeSpec A).obj.left,
            IsRelativeSpecBaseChangeArrow C g A B e h := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
