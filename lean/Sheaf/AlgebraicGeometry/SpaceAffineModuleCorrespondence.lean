/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Affine module correspondence for algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tag 08AI,
lemma-affine-equivalence-modules; Tag 081V, lemma-affine-equivalence-algebras
(blueprint: lem-sfb-space-affine-module-correspondence).

The algebra and module actions are normalized by the existing compatible-chart
projections. The affine-chart formula is an isomorphism of functors, so it also specifies
all module maps. Every module category and quasi-coherence predicate is Mathlib's.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The existing commutative algebra sheaf, viewed as a sheaf of rings.
Source: Stacks, Tag 08AI (blueprint: lem-sfb-space-affine-module-correspondence). -/
abbrev CommAlgebraSheaf.moduleRing (A : X.CommAlgebraSheaf) :
    Sheaf X.etaleTopology RingCat.{u} :=
  (sheafCompose X.etaleTopology (forget₂ CommRingCat.{u} RingCat.{u})).obj A.right

/-- Module sheaves over the direct-image algebra, with sectionwise algebra-linear maps.
Source: Stacks, Tag 08AI (blueprint: lem-sfb-space-affine-module-correspondence). -/
abbrev CommAlgebraSheaf.Modules (A : X.CommAlgebraSheaf) :=
  SheafOfModules.{u} A.moduleRing

/-- Forget the algebra action by the actual structure morphism of the algebra sheaf.
Source: Stacks, Tag 08AI (blueprint: lem-sfb-space-affine-module-correspondence). -/
def CommAlgebraSheaf.moduleForget (A : X.CommAlgebraSheaf) : A.Modules ⥤ X.Modules :=
  SheafOfModules.restrictScalars
    ((sheafCompose X.etaleTopology (forget₂ CommRingCat.{u} RingCat.{u})).map A.hom)

/-- Quasi-coherent algebra-modules use local presentations by arbitrary sums of the algebra.
Source: Stacks, Tag 08AI (blueprint: lem-sfb-space-affine-module-correspondence). -/
abbrev CommAlgebraSheaf.QCModules (A : X.CommAlgebraSheaf) :=
  (SheafOfModules.isQuasicoherent A.moduleRing).FullSubcategory

/-- A normalized affine module equivalence. This is conclusion data, not a hypothesis
substituting for the theorem. The direct-image isomorphism and projection equation fix
both the underlying direct image and its natural algebra action.
Source: Stacks, Tags 08AI and 081V
(blueprint: lem-sfb-space-affine-module-correspondence). -/
structure AffineModuleCorrespondence (p : Y ⟶ X) where
  /-- The existing normalized model of `p_* O_Y`. -/
  algebra : StructureAlgebraModel p
  /-- Its underlying structure module is quasi-coherent. -/
  algebra_quasiCoherent : algebra.algebra.toModule.IsQuasicoherent
  /-- Quasi-coherence over the algebra agrees with that over the structure sheaf. -/
  quasiCoherent_iff (M : algebra.algebra.Modules) :
    M.IsQuasicoherent ↔ ((algebra.algebra.moduleForget).obj M).IsQuasicoherent
  /-- The equivalence on the full categories of quasi-coherent modules. -/
  equivalence : Y.QCoh ≌ algebra.algebra.QCModules
  /-- Additivity of the direct-image equivalence. -/
  additive : equivalence.functor.Additive
  /-- Forgetting the action recovers the prescribed direct-image functor, naturally. -/
  directImageIso :
    equivalence.functor ⋙ ObjectProperty.ι _ ⋙ algebra.algebra.moduleForget ≅
      ObjectProperty.ι _ ⋙ moduleDirectImage p
  /-- The algebra action is multiplication of compatible sections on every scheme chart. -/
  action_projection (F : Y.QCoh) (V : X.EtaleSite) (q : ModuleChart p V)
      (a : algebra.algebra.right.obj.obj (op V))
      (s : (equivalence.functor.obj F).obj.val.obj (op V)) :
    ((moduleDirectImageModel p).projection F.obj V).app (op q)
        ((directImageIso.hom.app F).val.app (op V) (a • s)) =
      algebra.projection V q a •
        @id (F.obj.val.obj (op q.left))
          (((moduleDirectImageModel p).projection F.obj V).app (op q)
            ((directImageIso.hom.app F).val.app (op V) s))
  /-- On an affine chart its full fibre product is Spec of the algebra of sections;
  the ring map is exactly the regular-function projection. The inverse equivalence is
  the associated sheaf of M(V), naturally in every algebra-linear map of M. -/
  chart (V : X.EtaleSite) (hV : IsAffine (X.etaleForget.obj V))
      (q : ModuleChart p V)
      (hq : IsPullback q.left.obj.hom (yoneda.map q.hom.left) p.hom.hom V.obj.hom) :
    ∃ e : (Y.etaleForget.obj q.left) ≅ Spec (algebra.algebra.right.obj.obj (op V)),
      e.hom = (Y.etaleForget.obj q.left).toSpecΓ ≫ Spec.map (algebra.projection V q) ∧
      Nonempty ((equivalence.inverse ⋙ ObjectProperty.ι _ ⋙ schemeRestriction Y q.left) ≅
        (ObjectProperty.ι _ ⋙ SheafOfModules.evaluation algebra.algebra.moduleRing (op V) ⋙
          tilde.functor (algebra.algebra.right.obj.obj (op V)) ⋙
            Scheme.Modules.pullback e.hom))
  /-- Finite free algebra-modules correspond to finite free structure modules, also in
  rank zero. The isomorphisms live in the ambient module categories. -/
  finiteFree (n : ℕ) :
    ∃ F : Y.QCoh,
      Nonempty (F.obj ≅ SheafOfModules.free (R := Y.structureSheaf) (ULift.{u} (Fin n))) ∧
      Nonempty ((equivalence.functor.obj F).obj ≅
        SheafOfModules.free (R := algebra.algebra.moduleRing) (ULift.{u} (Fin n)))

/-- Étale restriction of modules over an algebra, using the given identification of
its restricted ring sheaf. The underlying sections and restriction maps are unchanged.
Source: Stacks, Tags 08AI and 03LX
(blueprint: lem-sfb-space-affine-module-correspondence). -/
def affineAlgebraRestriction {X' : AlgebraicSpace S} (g : X' ⟶ X)
    (hg : IsEtale g.hom.hom) (A : X.CommAlgebraSheaf) (B : X'.CommAlgebraSheaf)
    (e : B.moduleRing ≅ (etaleRingRestriction g hg).obj A.moduleRing) :
    A.Modules ⥤ B.Modules :=
  letI := etaleMap_isContinuous g hg
  SheafOfModules.pushforward (F := etaleMap g hg) e.hom

/-- Restriction on the actual full subcategories of quasi-coherent modules. The
quasi-coherence proof is supplied in the conclusion of the correspondence theorem.
Source: Stacks, Tags 08AI and 03LX
(blueprint: lem-sfb-space-affine-module-correspondence). -/
def affineQCohRestriction {Y' : AlgebraicSpace S} (h : Y' ⟶ Y)
    (hh : IsEtale h.hom.hom)
    (hq : ∀ F : Y.QCoh, ((pullback h hh).obj F.obj).IsQuasicoherent) :
    Y.QCoh ⥤ Y'.QCoh :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ pullback h hh) hq

/-- Affine direct image is the additive equivalence with quasi-coherent modules over
its function algebra, with the chart, morphism, finite-free and étale-base-change formulas.
Source: Stacks, Morphisms of Spaces, Tags 08AI and 081V; Properties of Spaces, Tag 03LX
(blueprint: lem-sfb-space-affine-module-correspondence).

Proof:
1. By lem-sfb-space-relative-spec-correspondence, the direct-image algebra is
quasi-coherent and the inverse image of an affine étale chart is its spectrum.
Choose an affine-component atlas by lem-a1-space-affine-etale-cover; its inverse
image is a scheme atlas by affineness and lem-trf-space-fibre-products-etale-covers.
2. An algebra-module presentation is a cokernel of sums of quasi-coherent structure
modules. Thus lem-sfb-space-qcoh-kernels-colimits proves underlying quasi-coherence.
3. Conversely, on Spec R the action on a quasi-coherent underlying module comes from
the C-module action on its sections by lem-sfb-space-qcoh-affine-chart-calculus and
lem-weil-pbc-affine-tilde-gamma-adjunction. A free C-module presentation sheafifies
to the required local algebra-module presentation; there is no finiteness assumption.
4. By lem-trf-space-etale-module-pushforward-restriction, direct image restricts to
the affine direct image. The affine pullback section formula
lem-weil-pbc-module-pullback-affine-sections identifies its sections over R' with
P tensor_R R', by p tensor (c tensor r') mapped to cp tensor r'. Hence it is
quasi-coherent and its action is the multiplication of compatible chart sections.
5. For the inverse associate to M the sheaf of M(U) over Spec C. Under further chart
restriction the preceding tensor formula identifies the two sheaves. Composition
multiplies scalars, proving the cocycle, identity and map compatibility.
6. Descend these sheaves and their maps by lem-sfb-space-qcoh-groupoid-equivalence,
using lem-trf-scheme-zariski-etale-quasi-coherent-equivalence on scheme charts.
Refine overlaps by affine opens; the overlap schemes need not be affine.
7. The tilde unit and counit identify the two composites with the identity, naturally
on section maps. Descent gives the equivalence; sectionwise addition proves additivity
and the tilde Hom bijection gives the displayed natural chart formula on morphisms.
8. For an étale base change, lem-trf-space-etale-module-pushforward-restriction
identifies direct-image sections and their algebra actions without changing them.
The two inverse constructions have the same affine section modules and cocycles,
so descent gives the comparison. Its projection normalization also proves compatibility
with successive base changes, including the identity and non-scheme base changes.
9. The free C-module of rank n associates to the free structure module of rank n.
The standard bases agree under the same overlap maps, hence descend. This includes n=0.
-/
theorem space_affine_module_correspondence (S : Scheme.{u}) :
    ∃ c : ∀ (Y X : AlgebraicSpace S) (p : Y ⟶ X),
      IsRepresentableWith (fun _ _ a ↦ IsAffineHom a.left) p.hom.hom →
        AffineModuleCorrespondence p,
      ∀ (Y X Y' X' : AlgebraicSpace S) (p : Y ⟶ X) (p' : Y' ⟶ X')
        (hp : IsRepresentableWith (fun _ _ a ↦ IsAffineHom a.left) p.hom.hom)
        (hp' : IsRepresentableWith (fun _ _ a ↦ IsAffineHom a.left) p'.hom.hom)
        (g : X' ⟶ X) (h : Y' ⟶ Y) (hg : IsEtale g.hom.hom)
        (square : IsPullback h.hom p'.hom p.hom g.hom),
        ∃ (hh : IsEtale h.hom.hom)
          (hq : ∀ F : Y.QCoh, ((pullback h hh).obj F.obj).IsQuasicoherent)
          (e : (c Y' X' p' hp').algebra.algebra.moduleRing ≅
            (etaleRingRestriction g hg).obj (c Y X p hp).algebra.algebra.moduleRing),
          (∀ (V : X'.EtaleSite) (q : ModuleChart p' V)
            (a : (c Y' X' p' hp').algebra.algebra.right.obj.obj (op V)),
            (c Y' X' p' hp').algebra.projection V q a =
              (c Y X p hp).algebra.projection ((etaleMap g hg).obj V)
                (moduleChartBaseChange p g h p' hg hh square.w V q)
                (e.hom.hom.app (op V) a)) ∧
          ∃ beta :
            (c Y X p hp).equivalence.functor ⋙ ObjectProperty.ι _ ⋙
                affineAlgebraRestriction g hg (c Y X p hp).algebra.algebra
                  (c Y' X' p' hp').algebra.algebra e ≅
              affineQCohRestriction h hh hq ⋙
                (c Y' X' p' hp').equivalence.functor ⋙ ObjectProperty.ι _,
            ∀ (F : Y.QCoh) (V : X'.EtaleSite) (q : ModuleChart p' V)
              (s : ((c Y X p hp).equivalence.functor.obj F).obj.val.obj
                (op ((etaleMap g hg).obj V))),
              ((moduleDirectImageModel p').projection ((pullback h hh).obj F.obj) V).app
                  (op q) (((c Y' X' p' hp').directImageIso.hom.app
                    ((affineQCohRestriction h hh hq).obj F)).val.app (op V)
                      ((beta.hom.app F).val.app (op V) s)) =
                ((moduleDirectImageModel p).projection F.obj ((etaleMap g hg).obj V)).app
                  (op (moduleChartBaseChange p g h p' hg hh square.w V q))
                  (((c Y X p hp).directImageIso.hom.app F).val.app
                    (op ((etaleMap g hg).obj V)) s) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
