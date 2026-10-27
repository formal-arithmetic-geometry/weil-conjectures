module

public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Flat.Basic

/-! # Dimension-filtered flatness on all étale charts

Source: Stacks Project, spaces-flat.tex, Tags 0CWS and 0CWT;
flat.tex, equation-flat-dimension-n
(blueprint: def-sfb-space-dimension-flat-condition).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The represented map of base schemes, retaining its actual Yoneda map.
Source: Stacks, Tag 0CWS, base-change notation
(blueprint: def-sfb-space-dimension-flat-condition). -/
def dimensionFlatBaseMap {S : Scheme.{u}} {B Y : Over S} (g : B ⟶ Y) :
    schemeSpace B ⟶ schemeSpace Y :=
  ObjectProperty.homMk ⟨yoneda.map g⟩

/-- The map from an étale chart of the actual base change to the test scheme.
Source: Stacks, Tag 0CWS, the map U to B
(blueprint: def-sfb-space-dimension-flat-condition). -/
def dimensionFlatChartMap {S : Scheme.{u}} {Y B : Over S} {X : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (g : B ⟶ Y)
    (U : (enlargedFibreProduct f (dimensionFlatBaseMap g)).EtaleSite) :
    U.obj.left ⟶ B :=
  yoneda.preimage (U.obj.hom ≫
    (Limits.pullback.snd f.hom (dimensionFlatBaseMap g).hom).hom)

/-- P_n(X,M;B): on every representable étale scheme chart of X times_Y B,
all stalks whose relative residue-field transcendence degree is at least n
are flat over the base local ring. Pullback is the recorded tensor pullback;
restriction to Zariski opens and both scalar maps are the canonical ones.
Source: Stacks, Tags 0CWS and 0CWT; flat.tex, equation-flat-dimension-n
(blueprint: def-sfb-space-dimension-flat-condition). -/
def dimensionFlatCondition {S : Scheme.{u}} {Y B : Over S} {X : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (M : X.Modules) (n : ℕ) (g : B ⟶ Y) : Prop :=
  ∀ (U : (enlargedFibreProduct f (dimensionFlatBaseMap g)).EtaleSite)
    (x : (enlargedFibreProduct f (dimensionFlatBaseMap g)).etaleForget.obj U),
    (n : Cardinal.{u}) ≤
      @Algebra.trdeg (B.left.residueField ((dimensionFlatChartMap f g U).left x))
        (((enlargedFibreProduct f (dimensionFlatBaseMap g)).etaleForget.obj U).residueField x)
        _ _ (((dimensionFlatChartMap f g U).left).residueFieldMap x).hom.toAlgebra →
    Module.Flat (B.left.presheaf.stalk ((dimensionFlatChartMap f g U).left x))
      ((ModuleCat.restrictScalars (((dimensionFlatChartMap f g U).left).stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor
          ((enlargedFibreProduct f (dimensionFlatBaseMap g)).etaleForget.obj U).toRingedSpace
          x).obj
          ((schemeRestriction (enlargedFibreProduct f (dimensionFlatBaseMap g)) U).obj
            ((moduleTensorPullback (enlargedFibreProductFst f (dimensionFlatBaseMap g))).obj
              M))))

end AlgebraicGeometry.AlgebraicSpace
