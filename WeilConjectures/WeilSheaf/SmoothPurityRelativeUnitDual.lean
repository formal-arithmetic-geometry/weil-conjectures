module

public import WeilConjectures.WeilSheaf.SmoothPurityRelativeDualityIso
public import WeilConjectures.PoincareDuality.Biduality.Constructible

/-! Express the relative exceptional unit using absolute Verdier duality. -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The projection formula, natural in its first argument, at a fixed second argument. -/
def purityExceptionalProjectionRight (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj l⟧) :
    boundedConstructibleLowerShriek l f ⋙ tensorRight K ≅
      tensorRight ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj l) l f).obj K) ⋙
        boundedConstructibleLowerShriek l f := by
  let t : boundedConstructibleLowerShriek l f ⋙ tensorRight K ⟶
      tensorRight ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj l) l f).obj K) ⋙
        boundedConstructibleLowerShriek l f :=
    { app M := (boundedConstructibleExceptionalProjection l f).app M |>.app K
      naturality M N g :=
        boundedConstructibleExceptionalProjectionMorphism_natural_left l f g K }
  have : ∀ M, IsIso (t.app M) := fun M ↦
    isIso_boundedConstructibleExceptionalProjection_app_app l f M K
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- Exceptional pullback commutes with internal Hom after pulling its first argument back. -/
def purityUpperShriekIhomIso (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj l⟧) :
    ihom K ⋙ boundedConstructibleUpperShriek l f ≅
      boundedConstructibleUpperShriek l f ⋙
        ihom ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj l) l f).obj K) :=
  Adjunction.ihomIsoOfExceptionalProjection (boundedConstructibleUpperShriekAdjunction l f)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj l) l f) K
    (purityExceptionalProjectionRight l f K)

/-- Biduality identifies the coefficient unit with the internal endomorphisms of the
absolute dualizing complex, including when the scheme is singular. -/
def purityUnitDualizingEndIso (Y : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj l⟧) ≅
      (ihom (dualizingComplex l Y)).obj (dualizingComplex l Y) := by
  have := isIso_verdierBiduality l (X := Y) (𝟙_ _)
  exact asIso (verdierBiduality l (X := Y) (𝟙_ _)) ≪≫
    ihomIsoOfIsoLeft (unitNatIso.app (dualizingComplex l Y)).symm (dualizingComplex l Y)

/-- The relative exceptional unit is the absolute dual of the pullback of the base's
absolute dualizing complex. -/
def purityUpperShriekUnitDualIso :
    (boundedConstructibleUpperShriek l f).obj (𝟙_ _) ≅
      (ihom ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj l) l f).obj
        (dualizingComplex l Y))).obj (dualizingComplex l X) :=
  (boundedConstructibleUpperShriek l f).mapIso (purityUnitDualizingEndIso l Y) ≪≫
    (purityUpperShriekIhomIso l f (dualizingComplex l Y)).app (dualizingComplex l Y) ≪≫
    (ihom _).mapIso (upperShriekDualizingComplexIso l f)

end AlgebraicGeometry.ProEtale.CondensedRing
