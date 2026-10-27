module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Basic
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.TraceFormula.FlatFibreFreeNeighbourhood
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent

/-! # Flatness on a field fibre detects finite freeness near a relatively flat point

Source: Stacks Project, More on Morphisms of Spaces, Tags 0CZS and 05WY
(blueprint: lem-sfb-space-fibre-flat-free-criterion).

The auxiliary constructions are the field-valued morphism, its actual sheaf fibre product,
the first projection, and the tautological rational point introduced in the statement.
Flatness is tested on ordinary module stalks on every compatible pair of étale charts.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The actual Yoneda morphism associated to a field-valued representative.
Source: Stacks Project, Tag 05WY(2)
(blueprint: lem-sfb-space-fibre-flat-free-criterion). -/
def PointRepresentative.toMorphism {S : Scheme.{u}} {X : AlgebraicSpace S}
    (ξ : PointRepresentative X.obj.obj) : schemeSpace (Over.mk ξ.base) ⟶ X :=
  ObjectProperty.homMk ⟨yonedaEquiv.symm ξ.value⟩

/-- The field fibre X ×_Y Spec(K) for the representative ξ and y_K = f ξ.
Its sheaf pullback is an algebraic space by the recorded fibre-product theorem.
Source: Stacks Project, Tag 05WY(2), used in Tag 0CZS
(blueprint: lem-sfb-space-fibre-flat-free-criterion). -/
def representativeFibre {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ξ : PointRepresentative X.obj.obj) : AlgebraicSpace S :=
  ⟨Limits.pullback f.hom (ξ.toMorphism ≫ f).hom,
    (fibreProduct_isAlgebraicSpace X (schemeSpace (Over.mk ξ.base)) Y
      f (ξ.toMorphism ≫ f)).1⟩

/-- The first projection, along which the fibre module is tensor pullback.
Source: Stacks Project, Tag 05WY(2)
(blueprint: lem-sfb-space-fibre-flat-free-criterion). -/
def representativeFibreProjection {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ξ : PointRepresentative X.obj.obj) : representativeFibre f ξ ⟶ X :=
  ObjectProperty.homMk (Limits.pullback.fst f.hom (ξ.toMorphism ≫ f).hom)

/-- The tautological K-rational point (ξ,id) of the actual fibre product.
The universal-property lift fixes both projections, so no arbitrary point is chosen.
Source: Stacks Project, Tag 05WY, first paragraph of the proof
(blueprint: lem-sfb-space-fibre-flat-free-criterion). -/
def representativeFibreSection {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ξ : PointRepresentative X.obj.obj) :
    schemeSpace (Over.mk ξ.base) ⟶ representativeFibre f ξ :=
  ObjectProperty.homMk (Limits.pullback.lift ξ.toMorphism.hom (𝟙 _)
    (Category.id_comp _).symm)

/-- The class of the tautological K-rational point, retaining the given field and base map.
Source: Stacks Project, Tag 05WY(2), first paragraph of the proof
(blueprint: lem-sfb-space-fibre-flat-free-criterion). -/
def representativeFibrePoint {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ξ : PointRepresentative X.obj.obj) :
    Point (representativeFibre f ξ).obj.obj :=
  Quot.mk _ ⟨ξ.K, ξ.base, (representativeFibreSection f ξ).hom.hom.app _ (𝟙 _)⟩

/-- A finitely presented quasi-coherent module, flat over the target at x, is finite free
on an étale neighbourhood of x exactly when its field-fibre pullback is flat at (ξ,id).
Source: Stacks Project, Tags 0CZS(1),(4) and 05WY(1),(2)
(blueprint: lem-sfb-space-fibre-flat-free-criterion).

Proof:
1. Choose a surjective étale scheme chart of Y and then one of its pullback to X,
   using lem-a1-space-affine-etale-cover and lem-trf-space-fibre-products-etale-covers.
   Shrink source and target to affine opens around a lift of x. Open immersions are
   étale and compose (lem-weil-pbc-open-immersion-etale,
   lem-trf-space-chartwise-etale-permanence). The resulting scheme map is locally
   finitely presented by def-sfb-space-morphism-properties, and has a finitely presented
   section-ring map by lem-weil-pbc-lfp-affine-opens-finite-presentation. It is affine
   (lem-weil-pbc-morphism-affine-schemes-affine), hence quasi-compact and quasi-separated
   (lem-weil-pbc-affine-morphism-permanence), so it meets the scheme theorem's hypotheses.
2. Étale pullback is restriction (lem-trf-space-etale-module-pushforward-restriction)
   and preserves quasi-coherence (lem-sfb-space-module-pullback-quasicoherent).
   Use lem-trf-scheme-zariski-etale-quasi-coherent-equivalence to obtain the ordinary
   Zariski module G. Its finite presentation follows from
   lem-sfb-scheme-etale-module-exact-finiteness-comparison. The hypothesis makes G_u
   flat over the target stalk. Apply lem-sfb-space-fibre-flatness-chart-comparison to
   id_X over Y: fibre flatness for the prescribed representative is flatness of (G_v)_u
   over the source-fibre stalk. The pullback comparison identifies the scheme fibre
   module. Now lem-trf-flat-fibre-free-neighbourhood gives a free open neighbourhood.
   The Zariski/étale equivalence identifies its free module with the displayed free
   module on the slice. The open neighbourhood remains étale over X.
3. Conversely refine a finite free étale neighbourhood to compatible charts as in (1).
   Pullback of a finite free module is finite free: b tensor (a_i) maps to (b*a_i),
   with inverse (b_i) mapping to the sum of b_i tensor e_i. The same formula on the
   scheme fibre gives a finite free fibre stalk, which is flat by
   lem-sc-affine-standard-cover-finite-free-local-fp-flat. The chart comparison of
   lem-sfb-space-fibre-flatness-chart-comparison gives the asserted fibre flatness
   for every chosen ξ. These formulas include the empty basis, so r=0 and M=0 remain.
-/
theorem finiteFree_near_iff_representativeFibre_flat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : MapIsLocallyOfFinitePresentation f) (M : X.QCoh)
    (hM : M.obj.IsFinitePresentation) (x : Point X.obj.obj)
    (hflat : ∀ (U : X.EtaleSite) (V : Y.EtaleSite) (h : U.obj.left ⟶ V.obj.left),
      U.obj.hom ≫ f.hom.hom = yoneda.map h ≫ V.obj.hom →
      ∀ t : X.etaleForget.obj U, schemePointMap U.obj.hom t = x →
        Module.Flat ((Y.etaleForget.obj V).presheaf.stalk (h.left t))
          ((ModuleCat.restrictScalars (h.left.stalkMap t).hom).obj
            ((RingedSpace.moduleStalkFunctor (X.etaleForget.obj U).toRingedSpace t).obj
              ((X.schemeRestriction U).obj M.obj))))
    (ξ : PointRepresentative X.obj.obj) (hξ : Quot.mk _ ξ = x) :
    (∃ U : X.EtaleSite, x ∈ pointImage U.obj.hom ∧
      ∃ r : ℕ, Nonempty ((X.etalePullback U).obj M.obj ≅
        SheafOfModules.free (R := X.structureSheaf.over U) (ULift.{u} (Fin r)))) ↔
    (∀ (U V : (representativeFibre f ξ).EtaleSite) (h : U.obj.left ⟶ V.obj.left),
      U.obj.hom = yoneda.map h ≫ V.obj.hom →
      ∀ t : (representativeFibre f ξ).etaleForget.obj U,
        schemePointMap U.obj.hom t = representativeFibrePoint f ξ →
        Module.Flat (((representativeFibre f ξ).etaleForget.obj V).presheaf.stalk
            (h.left t))
          ((ModuleCat.restrictScalars (h.left.stalkMap t).hom).obj
            ((RingedSpace.moduleStalkFunctor
              ((representativeFibre f ξ).etaleForget.obj U).toRingedSpace t).obj
              (((representativeFibre f ξ).schemeRestriction U).obj
                ((moduleTensorPullback (representativeFibreProjection f ξ)).obj M.obj))))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
