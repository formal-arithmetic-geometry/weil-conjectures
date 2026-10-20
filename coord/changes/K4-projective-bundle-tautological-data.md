# AlgebraicGeometry.projectiveBundleFrameSection

## Reason

Factor the data interfaces, preserving their mathematical meaning, out of the item to permit
separate construction lemmas without an import cycle. The item publicly imports the extracted module, so
its existing importers see the same declarations and elaborated signatures.

## Old

The declarations from `projectiveBundleTensorPullbackIso` through `projectiveBundleRank`
were in `Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry`.
Their definitions, verbatim:

```lean
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

```

## New

The declarations move to
`Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalData`; the item retains all original
public imports and uses
`public import Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalData`.
The existing `ProjectiveBundleTautologicalSystem`, `ProjectiveBundleTautologicalGeometry`
and main theorem signatures stay in the item, unchanged. No target meaning changes.
The sole body refactoring names the initial composite of `projectiveBundleFrameSection`
as `projectiveBundleFrameVector`. The section is then this vector followed by the
pulled-back quotient. Unfolding the new helper and reassociating composition by Category.assoc recovers
the old composite. The named equation below exposes the quotient factor directly.
The two maps are marked `@[no_expose]` and irreducible. The proved equation
`projectiveBundleFrameSection_eq` exposes only the final quotient factor, and
`projectiveBundleFrameVector_isIso` proves invertibility from invertibility of the
free inclusion. Downstream proofs use this API without unfolding the large composite.
This addresses the retained attempt's 60-second rank-zero compile timeout.
The previous profile spent 27.2 seconds in kernel checking
`quotient_isIso_on_frame_zero`; the new rank-zero file compiles in 8.4 seconds
and its complete axiom probe in 5.5 seconds. The data module with its probe
compiles in 8.4 seconds. The API theorem is proved in the defining module
before hiding the composite, so no downstream kernel expands the implementation. It changes
no map, proposition, signature, target statement, or geometric interpretation.
The geometry interface using this definition is submitted for semantic review again;
unfolding the named vector and applying Category.assoc recovers the original frame-section term, so the geometry
predicate retains its exact meaning. The target signatures do not mention this helper.

New frame-model and coherence records name strictly partial construction interfaces;
no data is chosen from mere unproved existence in a definition.

Explicit implementation:

```lean
@[no_expose]
noncomputable def projectiveBundleFrameVector
    {B : Scheme.{u}} {F : B.Modules} (D : ProjectiveBundleRealization B F)
    (n : ℕ) (U : B.Opens) (e : B.ModuleFrame F U (n + 1)) (i : ULift.{u} (Fin (n + 1))) :
    Scheme.Modules.unit (D.A.data.relProjHom ⁻¹ᵁ U).toScheme ⟶
      (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).obj
        ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F) :=
  (projectiveBundlePullbackUnitIso (D.A.data.relProjHom ∣_ U)).inv ≫
    (Scheme.Modules.tensorPullback (D.A.data.relProjHom ∣_ U)).map
      (SheafOfModules.ιFree i ≫ e.inv) ≫
    ((projectiveBundlePullbackComp (D.A.data.relProjHom ∣_ U) U.ι).app F).hom ≫
    (projectiveBundlePullbackCongr (morphismRestrict_ι _ _)).hom.app F ≫
    ((projectiveBundlePullbackComp (D.A.data.relProjHom ⁻¹ᵁ U).ι
      D.A.data.relProjHom).app F).inv

/-- A transported frame vector is invertible whenever its free inclusion is invertible.
This API avoids exposing the full pullback-comparison composite to downstream kernels.
Source: Stacks, Tag 01OB
(blueprint: def-pur-projective-bundle-tautological-data). -/
theorem projectiveBundleFrameVector_isIso
    {B : Scheme.{u}} {F : B.Modules} (D : ProjectiveBundleRealization B F)
    (n : ℕ) (U : B.Opens) (e : B.ModuleFrame F U (n + 1)) (i : ULift.{u} (Fin (n + 1)))
    [IsIso (SheafOfModules.ιFree (R := U.toScheme.ringCatSheaf) i)] :
    IsIso (projectiveBundleFrameVector D n U e i) := by
  unfold projectiveBundleFrameVector
  infer_instance

attribute [irreducible] projectiveBundleFrameVector

/-- The quotient section associated to the `i`th vector of a specified frame, on `p⁻¹U`.
Source: Stacks, Tag 01OB
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
@[no_expose]
noncomputable def projectiveBundleFrameSection
    {B : Scheme.{u}} {F : B.Modules} (D : ProjectiveBundleRealization B F)
    (n : ℕ) (U : B.Opens) (e : B.ModuleFrame F U (n + 1)) (i : ULift.{u} (Fin (n + 1))) :
    Scheme.Modules.unit (D.A.data.relProjHom ⁻¹ᵁ U).toScheme ⟶
      (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).obj D.L :=
  projectiveBundleFrameVector D n U e i ≫
    (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).map D.quotient

attribute [irreducible] projectiveBundleFrameSection

/-- The defining quotient equation, usable without unfolding the pullback comparisons.
Source: Stacks, Tag 01OB
(blueprint: def-pur-projective-bundle-tautological-data). -/
theorem projectiveBundleFrameSection_eq
    {B : Scheme.{u}} {F : B.Modules} (D : ProjectiveBundleRealization B F)
    (n : ℕ) (U : B.Opens) (e : B.ModuleFrame F U (n + 1)) (i : ULift.{u} (Fin (n + 1))) :
    projectiveBundleFrameSection D n U e i = projectiveBundleFrameVector D n U e i ≫
      (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).map D.quotient := by
  unfold projectiveBundleFrameSection
  rfl

```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry | K4 | public import of extracted data; proved rank-zero helper uses the explicit equation |
| Sheaf.AlgebraicGeometry.ProperFibrewiseAmpleProjective | unclaimed | same exported signatures and meanings; compiles without adaptation |
| Sheaf.AlgebraicGeometry.VectorProjectiveCompletion | K9 | same exported signatures and meanings; compiles without adaptation |
| Sheaf.AlgebraicGeometry.CompleteFlagBundle | E7 | same exported signatures and meanings; compiles without adaptation |
| Sheaf.Paper.PurityChernClasses | unclaimed | same exported signatures and meanings; compiles without adaptation |
| Sheaf.Paper.ChernFlagFormula | G4 | same exported signatures and meanings; compiles without adaptation |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | same exported signatures and meanings; compiles without adaptation |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | same exported signatures and meanings; compiles without adaptation |

## Status

landed 20261020T131130-L-1245318 2026-10-20 (merge of deliver/K4/Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry)

