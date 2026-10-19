module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
public import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.CategoryTheory.SiteModuleSheafGluing
import WeilConjectures.RingTheory.SymmetricAlgebraBaseChange
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Finite locally free projective bundles and tautological geometry

Source: Stacks Project, Tags 01OB, 01O3 and 01OE (blueprint:
`lem-pur-projective-bundle-tautological-geometry`).  The proof is postponed to stage 3.

Main definitions: `ProjectiveBundleRealization`, `ProjectiveBundleFrameChart`,
`ProjectiveBundleBaseChangeDatum`, `ProjectiveBundleCoordinateGeometry`, and
`ProjectiveBundleTautologicalSystem`.
Main statement: `exists_projectiveBundleTautologicalGeometry`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback

/-- The unit-normalized comparison from the stipulated tensor pullback to Mathlib's
adjoint implementation. Uniqueness of left adjoints determines this comparison; thus all
pullback equations below also specify equations for tensor pullback, without choosing maps.
Source: Stacks, Tags 0095, 0096
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
noncomputable def projectiveBundleTensorPullbackIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Scheme.Modules.tensorPullback g ≅ Scheme.Modules.pullback g :=
  (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction g)

/-- Tensor-pullback identity, transported by the unit-normalized adjoint comparison.
Source: Stacks, Tags 0095, 0096 (blueprint: lem-pur-projective-bundle-tautological-geometry). -/
noncomputable def projectiveBundlePullbackId (X : Scheme.{u}) :
    Scheme.Modules.tensorPullback (𝟙 X) ≅ 𝟭 X.Modules :=
  projectiveBundleTensorPullbackIso (𝟙 X) ≪≫ Scheme.Modules.pullbackId X

/-- Tensor-pullback composition, using the canonical adjoint comparison.
Source: Stacks, Tags 0095, 0096 (blueprint: lem-pur-projective-bundle-tautological-geometry). -/
noncomputable def projectiveBundlePullbackComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.Modules.tensorPullback g ⋙ Scheme.Modules.tensorPullback f ≅
      Scheme.Modules.tensorPullback (f ≫ g) :=
  Functor.isoWhiskerRight (projectiveBundleTensorPullbackIso g) (Scheme.Modules.tensorPullback f) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pullback g) (projectiveBundleTensorPullbackIso f) ≪≫
    Scheme.Modules.pullbackComp f g ≪≫ (projectiveBundleTensorPullbackIso (f ≫ g)).symm

/-- Transport of tensor pullback along equality of the underlying scheme maps.
Source: Stacks, Tags 0095, 0096 (blueprint: lem-pur-projective-bundle-tautological-geometry). -/
noncomputable def projectiveBundlePullbackCongr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) : Scheme.Modules.tensorPullback f ≅ Scheme.Modules.tensorPullback g :=
  eqToIso (congrArg Scheme.Modules.tensorPullback h)

/-- The specified tensor-pullback adjunction; its universal property fixes the unit.
Source: Stacks, Tags 0095, 0096 (blueprint: lem-pur-projective-bundle-tautological-geometry). -/
noncomputable def projectiveBundlePullbackAdjunction {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Scheme.Modules.tensorPullback g ⊣ Scheme.Modules.pushforward g :=
  Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)

/-- Pulling back the unit module by tensor product gives the unit module.
Source: Stacks, Tags 0095, 0096 (blueprint: lem-pur-projective-bundle-tautological-geometry). -/
noncomputable def projectiveBundlePullbackUnitIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (Scheme.Modules.tensorPullback g).obj (Scheme.Modules.unit Y) ≅ Scheme.Modules.unit X :=
  (projectiveBundleTensorPullbackIso g).app (Scheme.Modules.unit Y) ≪≫
    Scheme.Modules.pullbackObjUnitIso g

/-- The actual pullback of a section, defined by the tensor-pullback adjunction unit.
Source: Stacks, Tags 0095, 0096 (blueprint: lem-pur-projective-bundle-tautological-geometry). -/
noncomputable def projectiveBundlePullbackSection {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {U : Y.Opens} (m : Γ(M, U)) :
    Γ((Scheme.Modules.tensorPullback g).obj M, g ⁻¹ᵁ U) :=
  ((projectiveBundlePullbackAdjunction g).unit.app M).app U m

attribute [local irreducible] projectiveBundleTensorPullbackIso
  projectiveBundlePullbackId projectiveBundlePullbackComp projectiveBundlePullbackCongr
  projectiveBundlePullbackAdjunction projectiveBundlePullbackUnitIso
  projectiveBundlePullbackSection

namespace Scheme

/-- The symmetric-degree submodule: products of exactly `d` degree-one generators.
Source: Stacks, Tag 01OB
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
def symmetricDegree (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (d : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  Submodule.span R {x | ∃ v : Fin d → M,
    x = ∏ i, SymmetricAlgebra.ι R M (v i)}

/-- An actual frame, rather than merely the proposition that one exists.
Source: Stacks, Tag 01OB
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
def ModuleFrame (B : Scheme.{u}) (F : B.Modules) (U : B.Opens) (r : ℕ) : Type u :=
  (Modules.tensorPullback U.ι).obj F ≅
    SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The symmetric algebra presented on the affine basis, with its actual symmetric grading,
algebra structure and canonical restriction maps.
Source: Stacks, Tag 01OB
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
structure SymmetricGradedAlgebraData (B : Scheme.{u}) (F : B.Modules) where
  data : B.GradedAlgebraData
  sectionEquiv : ∀ U : B.affineOpens,
    SymmetricAlgebra (B.presheaf.obj (op U.1)) (F.val.obj (op U.1)) ≃ₐ[
      B.presheaf.obj (op U.1)] data.obj U
  sectionEquiv_grade : ∀ (U : B.affineOpens) (d : ℕ) (x : SymmetricAlgebra
      (B.presheaf.obj (op U.1)) (F.val.obj (op U.1))),
    x ∈ symmetricDegree (B.presheaf.obj (op U.1)) (F.val.obj (op U.1)) d ↔
      sectionEquiv U x ∈ data.grading U d
  sectionEquiv_restriction : ∀ {U V : B.affineOpens} (h : U ≤ V) (x :
      SymmetricAlgebra (B.presheaf.obj (op V.1)) (F.val.obj (op V.1))),
    data.res h (sectionEquiv V x) =
      sectionEquiv U (SymmetricAlgebraSheaf.restriction F (homOfLE h).op x)

end Scheme

/-- Transport of the restriction of a global module across nested affine Proj charts.
Source: Stacks, Tag 01NR
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
noncomputable def tautologicalTransport
    (B : Scheme.{u}) (A : B.GradedAlgebraData) (L : A.relProj.Modules)
    {U V : B.affineOpens} (h : U ≤ V) :
    (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).obj
        ((Scheme.Modules.tensorPullback (A.relProjι V)).obj L) ≅
      (Scheme.Modules.tensorPullback (A.relProjι U)).obj L :=
  (projectiveBundlePullbackComp (A.relProjFunctor.map (homOfLE h))
    (A.relProjι V)).app L ≪≫
    (projectiveBundlePullbackCongr (A.relProjFunctor_map_relProjι (homOfLE h))).app L

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Compatible affine twist charts. The restriction isomorphisms are normalized on every
homogeneous degree-one section, so they are the homogeneous-localization maps.
Source: Stacks, Tags 01NR, 01MN
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
structure TautologicalTwistData (B : Scheme.{u}) (A : B.GradedAlgebraData)
    (L : A.relProj.Modules) where
  chart : ∀ U : B.affineOpens,
    (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅ Proj.twist (A.grading U) 1
  twistRestriction : ∀ {U V : B.affineOpens} (h : U ≤ V),
    (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).obj
        (Proj.twist (A.grading V) 1) ≅ Proj.twist (A.grading U) 1
  restriction_generator : ∀ {U V : B.affineOpens} (h : U ≤ V)
      (x : A.obj V) (hx : x ∈ A.grading V 1),
    (twistRestriction h).hom.app
        ((A.relProjFunctor.map (homOfLE h)) ⁻¹ᵁ ⊤)
        (projectiveBundlePullbackSection (A.relProjFunctor.map (homOfLE h))
          (Scheme.Modules.Hom.app (Proj.unitToTwist hx) ⊤ (1 : Γ(Proj (A.grading V), ⊤)))) =
      Scheme.Modules.Hom.app (Proj.unitToTwist ((A.res h).map_mem hx))
        ((A.relProjFunctor.map (homOfLE h)) ⁻¹ᵁ ⊤)
        (1 : Γ(Proj (A.grading U), (A.relProjFunctor.map (homOfLE h)) ⁻¹ᵁ ⊤))
  chart_overlap : ∀ {U V : B.affineOpens} (h : U ≤ V),
    tautologicalTransport B A L h ≪≫ chart U =
      (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).mapIso
        (chart V) ≪≫ twistRestriction h

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A projectivization of the actual symmetric algebra with its normalized tautological
quotient and compatible degree-one twist charts.
Source: Stacks, Tags 01OB, 01NR
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
structure ProjectiveBundleRealization (B : Scheme.{u}) (F : B.Modules) where
  A : B.SymmetricGradedAlgebraData F
  L : A.data.relProj.Modules
  quotient : (Scheme.Modules.tensorPullback A.data.relProjHom).obj F ⟶ L
  twists : TautologicalTwistData B A.data L
  quotient_generator : ∀ (U : B.affineOpens) (x : F.val.obj (op U.1))
      (hx : A.sectionEquiv U (SymmetricAlgebra.ι _ _ x) ∈ A.data.grading U 1),
    (twists.chart U).hom.app
        (A.data.relProjι U ⁻¹ᵁ (A.data.relProjHom ⁻¹ᵁ U.1))
        (projectiveBundlePullbackSection (A.data.relProjι U)
          (((projectiveBundlePullbackAdjunction A.data.relProjHom).homEquiv
            F L quotient).app U.1 x)) =
      Scheme.Modules.Hom.app (Proj.unitToTwist hx)
        (A.data.relProjι U ⁻¹ᵁ (A.data.relProjHom ⁻¹ᵁ U.1))
        (1 : Γ(Proj (A.data.grading U),
          A.data.relProjι U ⁻¹ᵁ (A.data.relProjHom ⁻¹ᵁ U.1)))

/-- The quotient section associated to the `i`th vector of a specified frame, on `p⁻¹U`.
Source: Stacks, Tag 01OB
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
noncomputable def projectiveBundleFrameSection
    {B : Scheme.{u}} {F : B.Modules} (D : ProjectiveBundleRealization B F)
    (n : ℕ) (U : B.Opens) (e : B.ModuleFrame F U (n + 1)) (i : ULift.{u} (Fin (n + 1))) :
    Scheme.Modules.unit (D.A.data.relProjHom ⁻¹ᵁ U).toScheme ⟶
      (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).obj D.L :=
  (projectiveBundlePullbackUnitIso (D.A.data.relProjHom ∣_ U)).inv ≫
    (Scheme.Modules.tensorPullback (D.A.data.relProjHom ∣_ U)).map
      (SheafOfModules.ιFree i ≫ e.inv) ≫
    ((projectiveBundlePullbackComp (D.A.data.relProjHom ∣_ U) U.ι).app F).hom ≫
    (projectiveBundlePullbackCongr (morphismRestrict_ι _ _)).hom.app F ≫
    ((projectiveBundlePullbackComp (D.A.data.relProjHom ⁻¹ᵁ U).ι
      D.A.data.relProjHom).app F).inv ≫
    (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).map D.quotient

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The frame determines a chart over `U`, its comparison with the polynomial projective
space, and the twist isomorphism carrying the ordered homogeneous coordinates to that frame.
Source: Stacks, Tags 01OB, 01OE
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
structure ProjectiveBundleFrameChart {B : Scheme.{u}} {F : B.Modules}
    (D : ProjectiveBundleRealization B F) (n : ℕ) (U : B.Opens)
    (e : B.ModuleFrame F U (n + 1)) where
  relativeChart : (D.A.data.relProjHom ⁻¹ᵁ U).toScheme ≅
    RelativeProjectiveSpace.scheme U.toScheme n
  relativeChart_over : relativeChart.hom ≫ RelativeProjectiveSpace.π U.toScheme n =
    D.A.data.relProjHom ∣_ U
  polynomialChart : RelativeProjectiveSpace.scheme U.toScheme n ≅
    ℙ(ULift.{u} (Fin (n + 1)); U.toScheme)
  polynomialChart_over : polynomialChart.hom ≫
    (ℙ(ULift.{u} (Fin (n + 1)); U.toScheme) ↘ U.toScheme) =
      RelativeProjectiveSpace.π U.toScheme n
  twist : (Scheme.Modules.tensorPullback (relativeChart.hom ≫ polynomialChart.hom)).obj
      (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) U.toScheme 1) ≅
    (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).obj D.L
  coordinate : ∀ i : ULift.{u} (Fin (n + 1)),
    (projectiveBundlePullbackUnitIso (relativeChart.hom ≫ polynomialChart.hom)).inv ≫
      (Scheme.Modules.tensorPullback (relativeChart.hom ≫ polynomialChart.hom)).map
        (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (n + 1))) U.toScheme i) ≫
      twist.hom = projectiveBundleFrameSection D n U e i

  generator : ∀ i : ULift.{u} (Fin (n + 1)),
    let φ := relativeChart.hom ≫ polynomialChart.hom
    let M := (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).obj D.L
    let W := φ ⁻¹ᵁ ProjectiveSpace.standardOpen (ULift.{u} (Fin (n + 1))) U.toScheme i
    Scheme.Modules.IsFreeGenerator
      (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (Scheme.Modules.Hom.app (projectiveBundleFrameSection D n U e i) ⊤
          (1 : Γ((D.A.data.relProjHom ⁻¹ᵁ U).toScheme, ⊤))))
  transition : ∀ i j : ULift.{u} (Fin (n + 1)),
    let φ := relativeChart.hom ≫ polynomialChart.hom
    let M := (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).obj D.L
    let W := φ ⁻¹ᵁ ProjectiveSpace.standardOpen (ULift.{u} (Fin (n + 1))) U.toScheme j
    M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (Scheme.Modules.Hom.app (projectiveBundleFrameSection D n U e i) ⊤
          (1 : Γ((D.A.data.relProjHom ⁻¹ᵁ U).toScheme, ⊤))) =
      φ.app (ProjectiveSpace.standardOpen (ULift.{u} (Fin (n + 1))) U.toScheme j)
          (ProjectiveSpace.coordRatio (ULift.{u} (Fin (n + 1))) U.toScheme j i) •
        M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
          (Scheme.Modules.Hom.app (projectiveBundleFrameSection D n U e j) ⊤
            (1 : Γ((D.A.data.relProjHom ⁻¹ᵁ U).toScheme, ⊤)))

/-- The universal quotient square defining the degree-one Stacks base-change theta.
Naming this equation prevents repeated expansion in the dependent record projections.
Source: Stacks, Tag 01O3
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
def projectiveBundleThetaQuotientLaw
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    (r : D'.A.data.relProj ⟶ D.A.data.relProj)
    (h : r ≫ D.A.data.relProjHom = D'.A.data.relProjHom ≫ g)
    (θ : (Scheme.Modules.tensorPullback r).obj D.L ≅ D'.L) : Prop :=
  (Scheme.Modules.tensorPullback r).map D.quotient ≫ θ.hom =
    ((projectiveBundlePullbackComp r D.A.data.relProjHom).app F).hom ≫
    (projectiveBundlePullbackCongr h).hom.app F ≫
    ((projectiveBundlePullbackComp D'.A.data.relProjHom g).app F).inv ≫
    (Scheme.Modules.tensorPullback D'.A.data.relProjHom).map e.inv ≫ D'.quotient

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The canonical base-change comparison. Its coefficient maps are fixed on degree-one
vectors, and its actual theta is fixed by the universal quotient square (the degree-one
part of Stacks 01O3). No arbitrary invertible module is introduced.
Source: Stacks, Tag 01O3
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
structure ProjectiveBundleBaseChangeDatum
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F) where
  comparison : Scheme.GradedAlgebraData.PullbackData g D.A.data D'.A.data
  generator : ∀ {U : B.affineOpens} {U' : B'.affineOpens}
      (h : U'.1 ≤ g ⁻¹ᵁ U.1) (x : F.val.obj (op U.1)),
    comparison.map h (D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ x)) =
      D'.A.sectionEquiv U' (SymmetricAlgebra.ι _ _ (e.inv.app U'.1
        (((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE h).op
          (projectiveBundlePullbackSection g x))))
  map : D'.A.data.relProj ⟶ D.A.data.relProj
  map_eq : map = comparison.relProjComparison
  over : map ≫ D.A.data.relProjHom = D'.A.data.relProjHom ≫ g
  theta : (Scheme.Modules.tensorPullback map).obj D.L ≅ D'.L
  theta_quotient : projectiveBundleThetaQuotientLaw D D' g e map over theta

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Coordinate geometry over a field: the coordinate hyperplane, its affine complement
with the stated ratios, all divisor line bundles, and the scheme-theoretic reduced point.
Source: blueprint sk-prop-an, proof Step 1; Stacks, Tags 01NG and 01MS
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
structure ProjectiveBundleCoordinateGeometry (K : Type u) [Field K] (n : ℕ) where
  hyperplane : ∀ hn : 1 ≤ n,
    (Scheme.Modules.Hom.zeroLocus (ProjectiveSpace.coordinateSection
      (ULift.{u} (Fin (n + 1))) (Spec (.of K)) ⟨0⟩)).subscheme ≅
        RelativeProjectiveSpace.scheme (Spec (.of K)) (n - 1)
  hyperplane_over : ∀ hn : 1 ≤ n,
    (hyperplane hn).hom ≫ RelativeProjectiveSpace.π (Spec (.of K)) (n - 1) =
      (Scheme.Modules.Hom.zeroLocus (ProjectiveSpace.coordinateSection
        (ULift.{u} (Fin (n + 1))) (Spec (.of K)) ⟨0⟩)).subschemeι ≫
          (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of K)) ↘ Spec (.of K))
  affine : AffineSpace (ULift.{u} (Fin n)) (Spec (.of K)) ≅
    (ProjectiveSpace.standardOpen (ULift.{u} (Fin (n + 1))) (Spec (.of K)) ⟨0⟩).toScheme
  affine_over : affine.hom ≫
      (ProjectiveSpace.standardOpen (ULift.{u} (Fin (n + 1))) (Spec (.of K)) ⟨0⟩).ι ≫
      (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of K)) ↘ Spec (.of K)) =
    (AffineSpace (ULift.{u} (Fin n)) (Spec (.of K)) ↘ Spec (.of K))
  ratios : ∀ i : Fin n,
    (affine.hom ≫ (ProjectiveSpace.standardOpen (ULift.{u} (Fin (n + 1)))
      (Spec (.of K)) ⟨0⟩).ι).appLE
        (ProjectiveSpace.standardOpen (ULift.{u} (Fin (n + 1))) (Spec (.of K)) ⟨0⟩)
        ⊤ (by simp) (ProjectiveSpace.coordRatio (ULift.{u} (Fin (n + 1)))
          (Spec (.of K)) ⟨0⟩ ⟨i.succ⟩) = AffineSpace.coord _ ⟨i⟩
  divisor : ∀ i : ULift.{u} (Fin (n + 1)),
    (Scheme.Modules.Hom.zeroLocus (ProjectiveSpace.coordinateSection
      (ULift.{u} (Fin (n + 1))) (Spec (.of K)) i)).IsInvertible
  divisorLineBundle : ∀ i : ULift.{u} (Fin (n + 1)),
    (Scheme.Modules.Hom.zeroLocus (ProjectiveSpace.coordinateSection
      (ULift.{u} (Fin (n + 1))) (Spec (.of K)) i)).toModules.dual ≅
        ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) (Spec (.of K)) 1
  point : (⨆ i : Fin n, Scheme.Modules.Hom.zeroLocus (ProjectiveSpace.coordinateSection
      (ULift.{u} (Fin (n + 1))) (Spec (.of K)) ⟨i.succ⟩)).subscheme ≅ Spec (.of K)
  point_over : point.hom =
    (⨆ i : Fin n, Scheme.Modules.Hom.zeroLocus (ProjectiveSpace.coordinateSection
      (ULift.{u} (Fin (n + 1))) (Spec (.of K)) ⟨i.succ⟩)).subschemeι ≫
        (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of K)) ↘ Spec (.of K))
  point_reduced : IsReduced
    (⨆ i : Fin n, Scheme.Modules.Hom.zeroLocus (ProjectiveSpace.coordinateSection
      (ULift.{u} (Fin (n + 1))) (Spec (.of K)) ⟨i.succ⟩)).subscheme
  point_in_chart : ∀ x : (⨆ i : Fin n, Scheme.Modules.Hom.zeroLocus
      (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (n + 1)))
        (Spec (.of K)) ⟨i.succ⟩)).subscheme,
    (⨆ i : Fin n, Scheme.Modules.Hom.zeroLocus (ProjectiveSpace.coordinateSection
      (ULift.{u} (Fin (n + 1))) (Spec (.of K)) ⟨i.succ⟩)).subschemeι x ∈
      ProjectiveSpace.standardOpen (ULift.{u} (Fin (n + 1))) (Spec (.of K)) ⟨0⟩

/-- The existing fixed-rank predicate, with the base explicit to avoid re-inferring the
site and its sheafification instances at every dependent occurrence. This is only an alias.
Source: Stacks, Tag 01C5
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
def projectiveBundleRank (B : Scheme.{u}) (n : ℕ) (F : B.Modules) : Prop :=
  F.IsFiniteLocallyFreeOfRank (n + 1)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A coherent family of the projective-bundle constructions. Module isomorphisms to a
pullback are included in the indexing to make the identity and composition equations typed
without pretending that iterated pullbacks are definitionally equal.
Source: Stacks, Tags 01OB, 01O3, 01OE
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
structure ProjectiveBundleTautologicalSystem (n : ℕ) where
  bundle : ∀ (B : Scheme.{u}) (F : B.Modules)
    (_hF : projectiveBundleRank B n F), ProjectiveBundleRealization B F
  invertible : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F),
    (bundle B F hF).L.IsInvertible
  proper : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F),
    IsProper (bundle B F hF).A.data.relProjHom
  frame : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F)
    (U : B.Opens) (e : B.ModuleFrame F U (n + 1)),
      ProjectiveBundleFrameChart (bundle B F hF) n U e
  pullback_rank : ∀ (B B' : Scheme.{u}) (F : B.Modules)
    (_hF : projectiveBundleRank B n F) (g : B' ⟶ B),
      projectiveBundleRank B' n ((Scheme.Modules.tensorPullback g).obj F)
  baseChange : ∀ {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (hF : projectiveBundleRank B n F) (hF' : projectiveBundleRank B' n F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F),
      ProjectiveBundleBaseChangeDatum (bundle B F hF) (bundle B' F' hF') g e
  baseChange_id : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F),
    (baseChange hF hF (𝟙 B) ((projectiveBundlePullbackId B).app F).symm).map =
      𝟙 (bundle B F hF).A.data.relProj
  baseChange_theta_id : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F),
    (baseChange hF hF (𝟙 B) ((projectiveBundlePullbackId B).app F).symm).theta =
      (projectiveBundlePullbackCongr (baseChange_id B F hF)).app (bundle B F hF).L ≪≫
        (projectiveBundlePullbackId (bundle B F hF).A.data.relProj).app (bundle B F hF).L
  baseChange_comp : ∀ {B₀ B₁ B₂ : Scheme.{u}} {F₀ : B₀.Modules} {F₁ : B₁.Modules}
    {F₂ : B₂.Modules} (h₀ : projectiveBundleRank B₀ n F₀)
    (h₁ : projectiveBundleRank B₁ n F₁) (h₂ : projectiveBundleRank B₂ n F₂)
    (g : B₁ ⟶ B₀) (h : B₂ ⟶ B₁)
    (e : F₁ ≅ (Scheme.Modules.tensorPullback g).obj F₀)
    (e' : F₂ ≅ (Scheme.Modules.tensorPullback h).obj F₁),
      (baseChange h₀ h₂ (h ≫ g) (e' ≪≫ (Scheme.Modules.tensorPullback h).mapIso e ≪≫
        (projectiveBundlePullbackComp h g).app F₀)).map =
      (baseChange h₁ h₂ h e').map ≫
        (baseChange h₀ h₁ g e).map
  baseChange_theta_comp : ∀ {B₀ B₁ B₂ : Scheme.{u}} {F₀ : B₀.Modules} {F₁ : B₁.Modules}
    {F₂ : B₂.Modules} (h₀ : projectiveBundleRank B₀ n F₀)
    (h₁ : projectiveBundleRank B₁ n F₁) (h₂ : projectiveBundleRank B₂ n F₂)
    (g : B₁ ⟶ B₀) (h : B₂ ⟶ B₁)
    (e : F₁ ≅ (Scheme.Modules.tensorPullback g).obj F₀)
    (e' : F₂ ≅ (Scheme.Modules.tensorPullback h).obj F₁),
      (baseChange h₀ h₂ (h ≫ g) (e' ≪≫ (Scheme.Modules.tensorPullback h).mapIso e ≪≫
        (projectiveBundlePullbackComp h g).app F₀)).theta =
      (projectiveBundlePullbackCongr (baseChange_comp h₀ h₁ h₂ g h e e')).app (bundle B₀ F₀ h₀).L ≪≫
        ((projectiveBundlePullbackComp (baseChange h₁ h₂ h e').map
          (baseChange h₀ h₁ g e).map).app (bundle B₀ F₀ h₀).L).symm ≪≫
        (Scheme.Modules.tensorPullback (baseChange h₁ h₂ h e').map).mapIso
          (baseChange h₀ h₁ g e).theta ≪≫ (baseChange h₁ h₂ h e').theta
  coordinate : ∀ (K : Type u) [Field K], ProjectiveBundleCoordinateGeometry K n
  rank_zero : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F)
    (_hzero : n = 0), ∃ _e : (bundle B F hF).L ≅
      (Scheme.Modules.tensorPullback (bundle B F hF).A.data.relProjHom).obj F,
      IsIso (bundle B F hF).A.data.relProjHom

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The natural projective-bundle geometry, specializing the coherent construction to
`B` and `F`. The system records identities and composition for the same chosen maps.
Source: Stacks, Tags 01OB, 01O3, 01OE
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
structure ProjectiveBundleTautologicalGeometry (B : Scheme.{u}) (n : ℕ) (F : B.Modules)
    [hF : F.IsFiniteLocallyFreeOfRank (n + 1)] where
  system : ProjectiveBundleTautologicalSystem.{u} n
  realization : ProjectiveBundleRealization B F
  selected : realization = system.bundle B F hF

/-- Finite locally free projective bundles and their tautological geometry.
Source: Stacks, Tags 01OB, 01O3, 01OE
(blueprint: lem-pur-projective-bundle-tautological-geometry).

Proof plan from the node:

1. Choose a Zariski cover trivializing $F$ and refine it by affine opens $V=\operatorname{Spec}R$,
using [def-amb-finite-locally-free-module]. In a chosen frame $v_0,\ldots,v_n$, [lem-weil-pbc-
quasi-coherent-symmetric-algebra] identifies the affine sections of $\operatorname{Sym}F$ with
$\operatorname{Sym}_R(R^{n+1})$. By [lem-weil-pbc-symmetric-algebra-free-module-polynomial], the
map sending $v_i$ to $T_i$ is an algebra isomorphism with $R[T_0,\ldots,T_n]$. It is graded: [lem-
weil-pbc-symmetric-algebra-graded] describes degree $d$ as the span of products of $d$ degree-one
generators, and the map and its inverse send each such product to a product of the same length.
The same construction works for a frame on any open $U$, since its affine restrictions agree on
their degree-one generators and hence agree as maps of symmetric algebra sheaves.

2. Apply the graded-equivalence clause of [prop-nagata-relative-proj-functoriality] to the frame
isomorphism in step 1. Relative Proj and its affine restriction data [def-nagata-relative-proj]
then identify $P|_U$ with $\operatorname{Proj}_U\operatorname{Sym}(\mathcal O_U^{n+1})=\mathbf
P^n_U$ [def-nagata-relative-projective-space]. On an affine base piece, $D_+(T_i)$ has structure
ring $H_i=(R[T_0,\ldots,T_n])_{(T_i),0}$, and these opens cover, by [prop-nagata-proj-standard-
open], since the variables generate the positive-degree ideal. This proves the scheme part of the
assertion about every frame, not just about the frames in the initial covering.

3. Here is the compatibility needed to glue the affine twists. For a degree-preserving algebra
isomorphism $\alpha:A\to C$, the map on the degree-one localization modules is
$a/f^m\mapsto\alpha(a)/\alpha(f)^m$, with $\deg a=m\deg f+1$; its inverse is the same formula for
$\alpha^{-1}$. The fraction relation is preserved by a ring map, and the formula commutes with the
localization restriction maps in [def-weil-pbc-proj-twisting-sheaf]. For restriction on the base,
use that same formula with the coefficient restriction map on a principal affine refinement, as in
the overlap data of [def-nagata-relative-proj]. For a principal base restriction $R\to R_s$, on a
frame chart both restrictions are the free module $H_i[1/s]T_i$: multiplication by $T_i$
identifies the degree-one fractions with the degree-zero ring, with inverse division by $T_i$.
Thus restrictions and frame changes induce compatible isomorphisms of the local twisting modules.
The identity and triple-overlap equations follow by applying the composite algebra map to the
numerator and denominator. Apply [lem-weil-pbc-site-module-sheaf-gluing] on the Zariski open site
of $P$ to these overlap isomorphisms to obtain the global module $L$. Its affine identifications
are precisely $\widetilde{(\operatorname{Sym}F)(1)}$; thus $L$ is the twisting module $\mathcal
O_P(1)$ specified in the statement. No intersection of affine base opens is assumed affine: the
formulas are checked on principal refinements inside affine pieces, and then on an affine covering
of each overlap.

4. On a frame chart $D_+(T_i)$, the definition of the shift in [def-weil-pbc-proj-twisting-sheaf]
gives $L=(A_{T_i})_1$, where $A=R[T_0,\ldots,T_n]$. Multiplication by $T_i$ gives an $H_i$-linear
isomorphism $H_i\to(A_{T_i})_1$, with inverse $a/T_i^m\mapsto a/T_i^{m+1}$; the two composites are
the identity by multiplication of fractions. On an overlap the generators satisfy
$T_i=(T_i/T_j)T_j$. Hence $L$ is locally free of rank one, so invertible by [def-sc-invertible-
module], and these trivializations identify it with [def-pc-projective-space-twist] by $e_i\mapsto
T_i$. The maps agree on overlaps by the displayed identity; they and their inverses glue by
applying the sheaf axiom to local sections. Together with step 2 this proves the asserted
identification of pairs in every frame.

5. To use properness for the precise projective-space interface, apply [lemma-nagata-relative-
proj-base-change-arbitrary] to $\mathcal O_{\operatorname{Spec}\mathbf Z}[T_0,\ldots,T_n]$ and
$U\to\operatorname{Spec}\mathbf Z$. The pullback algebra is $\mathcal O_U[T_0,\ldots,T_n]$: on
each affine piece this is [lem-weil-pbc-symmetric-algebra-base-change] applied to the free module,
with the polynomial identification of step 1. Thus $\mathbf P^n_U$ of step 2 is canonically
$\mathbf P(\{0,\ldots,n\};U)$ of [def-nagata-projective-space-base-change], over $U$. This latter
structural morphism is proper by [lemma-nagata-projective-space-base-change-proper]. Therefore $p$
is proper over every member of the frame cover, and [lemma-nagata-projective-target-local] gives
properness over $B$. These results require no Noetherian, finite-type-base, or separated-base
hypothesis.

6. Let $g:B'\to B$ be arbitrary. The pullback of $F$ is quasi-coherent by [lem-weil-pbc-module-
pullback-quasi-coherent], and its affine sections on $W=\operatorname{Spec}S\subseteq
g^{-1}(\operatorname{Spec}R)$ are $S\otimes_R F(\operatorname{Spec}R)$ by [lem-weil-pbc-module-
pullback-affine-sections] (interchanging the tensor factors). Apply [lem-weil-pbc-symmetric-
algebra-base-change] to obtain an isomorphism $$S\otimes_R\operatorname{Sym}_R
F(\operatorname{Spec}R)\xrightarrow{\sim}\operatorname{Sym}_S(S\otimes_R
F(\operatorname{Spec}R)).$$ It sends $s\otimes\iota(v)$ to $s\iota(1\otimes v)$. It and its
inverse preserve degree, since the homogeneous pieces are the spans of products of degree-one
generators [lem-weil-pbc-symmetric-algebra-graded]. These maps agree under restriction: both
restriction composites agree on coefficients and on every $\iota(v)$, hence on all products and
sums. By the sheaf axiom they give a canonical graded algebra isomorphism
$g^*\operatorname{Sym}F\cong\operatorname{Sym}(g^*F)$. The affine-section identifications here are
those of [lem-weil-pbc-quasi-coherent-symmetric-algebra].

7. Apply [lemma-nagata-relative-proj-base-change-arbitrary] to $\operatorname{Sym}F$ and the
graded-equivalence clause of [prop-nagata-relative-proj-functoriality] to step 6. This constructs
the asserted isomorphism $\mathbf P_{B'}(g^*F)\cong B'\times_B P$. To fix its map, use [lem-
nagata-affine-proj-scalar-extension] on the affine pieces in step 6. If $\beta$ is that graded
scalar-extension isomorphism and $\psi(a)=\beta(1\otimes a)$, the map to $P$ has inverse image
$D_+(\psi(f))$ of $D_+(f)$ and ring map $a/f^m\mapsto\psi(a)/\psi(f)^m$. These formulas determine
the map uniquely on the covering by the pulled-back frame charts; in particular this is the
canonical coefficient-pullback comparison, with no flatness condition on $g$.

8. Let $r:\mathbf P_{B'}(g^*F)\to P$ be the projection just constructed. On a pulled-back frame
chart the modules in $r^*L\to L'$ are free of rank one by step 4; define the map by $r^*T_i\mapsto
T'_i=\psi(T_i)$. In affine module coordinates this is an isomorphism: pullback of $H_iT_i$ is
$H'_i\otimes_{H_i}H_iT_i\cong H'_iT'_i$, by [lem-weil-pbc-module-pullback-affine-sections]. The
ring map of step 7 sends $T_i/T_j$ to $T'_i/T'_j$, so these maps agree on overlaps of standard
charts. Across changes of base frame, they too agree: on a degree-one fraction both formulas send
$a/f^m$ to $\psi(a)/\psi(f)^m$, using step 3 and the map on generators in step 6. Thus maps and
inverses glue by the sheaf axiom. This proves the canonical isomorphism $r^*\mathcal
O_P(1)\cong\mathcal O_{\mathbf P_{B'}(g^*F)}(1)$; it gives exactly the degree-one part of the
twist comparison, rather than assuming that part from the scheme-only base-change node. The
meaning of pullback is [def-pc-module-pullback], and the fraction description is [def-weil-pbc-
proj-twisting-sheaf].

9. For the identity base map the maps in steps 6--8 fix coefficients, degree-one generators, and
all fractions. For $B''\xrightarrow{h}B'\xrightarrow{g}B$, identify the iterated module pullbacks
by [def-pc-module-pullback]. On affine pieces with coefficient maps $R\to S\to T$, both symmetric-
algebra maps send $t\otimes(s\otimes\iota(v))$ to $t\,\overline{s}\,\iota(1\otimes v)$; the
corresponding maps on every Proj chart send $a/f^m$ to its image over $T$. By the uniqueness of
the chart-described morphism in [lem-nagata-affine-proj-scalar-extension] and [lem-weil-pbc-
scheme-morphism-gluing], the comparison scheme maps coincide. Their maps into the fibre products
coincide by the two projections [def-pc-fibre-product]. On the line modules both composites carry
the pulled-back generator $T_i$ to the same generator over $T$, so they coincide as well. This
proves identity and composition compatibility for both the scheme and twist isomorphisms.

10. Now let $K$ be any field and $n\geq1$. The quotient $K[T_0,\ldots,T_n]\twoheadrightarrow
K[T_1,\ldots,T_n]$, setting $T_0=0$, is graded and surjective. The closed-immersion clause of
[prop-nagata-relative-proj-functoriality] gives $\mathbf P^{n-1}_K\hookrightarrow\mathbf P^n_K$,
using [def-nagata-relative-projective-space] over the affine base. On $D_+(T_j)$ for $j\ne0$, the
map on dehomogenized rings sets $T_0/T_j$ equal to zero and fixes all other coordinates [lem-weil-
pbc-dehomogenization-polynomial-ring]. Its kernel is $(T_0/T_j)$: expand a polynomial in that one
variable as its constant term plus that variable times a polynomial. The source has no $D_+(T_0)$
chart. Thus this immersion is scheme-theoretically the subscheme $T_0=0$, not just a bijection on
points. Its twist restricts to the lower-dimensional twist, since the local generators $T_j$ and
ratios $T_j/T_k$ restrict to the identically named ones, as in step 4.

11. The complement of $T_0=0$ is $D_+(T_0)$: in its local trivialization the section $T_0$
vanishes exactly where its coefficient is in the point's maximal ideal. By [lem-weil-pbc-
projective-space-standard-charts], its non-vanishing locus is the standard open, and that chart
has coordinate algebra $K[t_1,\ldots,t_n]$, $t_i=T_i/T_0$. By [def-sbc-affine-space], this chart
is $\mathbf A^n_K$. The base-change model used by that chart theorem is the same one identified
with relative Proj in step 5, with the same generators by steps 4 and 8.

12. For any $i$, the equation of $D_i=\{T_i=0\}$ on $U_j=D_+(T_j)$ is $q_j=T_i/T_j$, by [lem-weil-
pbc-projective-space-standard-charts]. For $j=i$ this is $1$; for $j\ne i$ it is one polynomial
variable, a nonzerodivisor because multiplying by it shifts the monomial coefficients injectively.
Hence the ideal is an effective Cartier ideal [def-nagata-effective-cartier-ideal]. Its associated
line bundle is the dual ideal [def-pc-divisor-line-bundle]. Let $h_j$ be the dual generator with
$h_j(q_j)=1$. On $U_j\cap U_k$ one has $q_k=(T_j/T_k)q_j$, hence $h_j=(T_j/T_k)h_k$. These are
exactly the transitions for $\mathcal O(1)$ in [def-pc-projective-space-twist], so $e_j\mapsto
h_j$ glues to $\mathcal O(1)\cong\mathcal O(D_i)$. This also checks the sign of the twist: it is
$+1$.

13. The scheme-theoretic intersection $T_1=\cdots=T_n=0$ has empty intersection with $D_+(T_i)$
for $i\geq1$, because there the defining ideal contains $T_i/T_i=1$. By the covering and
coordinate-ring clauses of [lem-weil-pbc-projective-space-standard-charts], it is therefore
entirely in $D_+(T_0)=\mathbf A^n_K$, where its coordinate ring is
$K[t_1,\ldots,t_n]/(t_1,\ldots,t_n)\cong K$ (evaluation at zero, with inverse the constants). This
is a reduced point, with coordinates $t_1=\cdots=t_n=0$, hence the homogeneous point
$[1:0:\cdots:0]$. In particular no nilpotent thickening is hidden in the assertion about the
intersection.

14. Finally take $n=0$. Over any framed affine base open, the positive-degree ideal of $R[T]$ is
generated by $T$, so its entire Proj is $D_+(T)$ by [prop-nagata-proj-standard-open]. By [lem-
weil-pbc-dehomogenization-polynomial-ring] its degree-zero localization is the polynomial ring on
zero variables, namely $R$, with structure map the identity. Thus $p$ is locally an isomorphism to
the base; the local inverses agree because each is an inverse to $p$ on its open, and glue by
[lem-weil-pbc-scheme-morphism-gluing]. Moreover, step 4 identifies the twist with the free module
generated by $T$. The local isomorphism $F\to L$ over this base identification sends the frame $v$
to $T$. If $v'=uv$ for a unit $u$, then $T'=uT$ by the degree-one symmetric algebra map, so this
isomorphism is independent of the frame and glues. Hence $\mathcal O_P(1)$ corresponds to $F$,
including when $F$ is a nontrivial line bundle. All covering arguments also apply to the empty
base.
-/
theorem exists_projectiveBundleTautologicalGeometry
    (B : Scheme.{u}) (n : ℕ) (F : B.Modules)
    [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    Nonempty (ProjectiveBundleTautologicalGeometry B n F) := by
  sorry

end AlgebraicGeometry
