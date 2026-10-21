module
public import Sheaf.Paper.ProfiniteDerivedEvaluation
public import Sheaf.Paper.RootTowerCoordinateFace
public import Sheaf.Paper.RootTowerLisseMorphismExtension
/-!
# Normalized compatible-root boundary comparison and naturality

Source: main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3),
agent expansion of the tame-boundary calculation.
(blueprint: def-sfb-root-boundary-comparison).

All coefficients retain every continuous function, including for incomplete algebraic closures.
All derived categories are ordinary and unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.RootBoundary
variable (F : Type u) [NormedField F]
variable (p : ℕ) {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R)
/-- The existing compatible prime-to-p root algebra, viewed as an affine scheme.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def tower : Scheme.{u} := Spec (.of (tameRootAlgebra p t))
/-- The quotient by all original boundary parameters.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
abbrev stratumRing := R ⧸ Ideal.span (Set.range t)
/-- The scheme-theoretic common-zero stratum, including the empty list of parameters.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def stratumScheme : Scheme.{u} := Spec (.of (stratumRing t))
/-- The closed inclusion of the common-zero stratum.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def stratumInclusion : stratumScheme t ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range t))))
/-- The root relations vanish when every root and every boundary parameter is set to zero.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison).

Proof: On each power relation the evaluated root is zero, its exponent is positive,
and the original parameter is zero in the quotient by the parameter ideal. On each
transition relation both sides evaluate to zero, because the quotient m/n is positive
for positive n dividing m. The kernel contains the generating relations, hence their ideal. -/
theorem roots_vanish : Ideal.span (tameRootRelations p t) ≤ RingHom.ker
    (MvPolynomial.eval₂Hom (Ideal.Quotient.mk (Ideal.span (Set.range t)))
      (fun _ : Fin r × TameRootOrder p ↦ 0)) := by
  sorry
/-- The actual quotient homomorphism setting every compatible root to zero.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def zeroRoots : tameRootAlgebra p t →+* stratumRing t :=
  Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom (Ideal.Quotient.mk (Ideal.span (Set.range t)))
      (fun _ : Fin r × TameRootOrder p ↦ 0)) (roots_vanish p t)
/-- The canonical map of the common-zero stratum into the full compatible-root tower.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def boundary : stratumScheme t ⟶ tower p t :=
  Spec.map (CommRingCat.ofHom (zeroRoots p t))
/-- The canonical boundary map lies over the stratum inclusion.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison).

Proof: The composite ring homomorphism from the base ring to the zero-root quotient
is the quotient map, since evaluation acts on constants by that quotient map. Apply
contravariance of Spec and the equality of these ring maps. -/
theorem boundary_square : boundary p t ≫ parameterRootProjection p t = stratumInclusion t := by
  sorry
/-- The recorded actual profinite test scheme, rather than a formal product or discrete set.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
abbrev test (X : Scheme.{u}) (P : Profinite.{u}) := (profiniteToProEtOf X).obj P
/-- The existing base-change map between actual profinite test schemes.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
abbrev testMap {X Y : Scheme.{u}} (f : X ⟶ Y) (P : Profinite.{u}) :=
  RootCoordinateFace.testMap f P
/-- The full-tower test projection to the affine base.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
abbrev qP (P : Profinite.{u}) := (test (tower p t) P).hom ≫ parameterRootProjection p t
/-- The existing open subscheme obtained by inverting the product of the original parameters.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
abbrev puncture := (parameterRootOpen p t).toScheme
/-- The punctured-tower test projection to the affine base.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
abbrev vP (P : Profinite.{u}) :=
  (test (puncture p t) P).hom ≫ (parameterRootOpen p t).ι ≫ parameterRootProjection p t
/-- The actual open inclusion between the two profinite test schemes.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
abbrev jP (P : Profinite.{u}) := testMap (parameterRootOpen p t).ι P
/-- The open-tower projection is the composite of the open inclusion and full projection.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison).

Proof: The defining pullback lift for the test map commutes with projection. Compose
this equality with the full-tower projection and reassociate the composites. -/
theorem puncture_square (P : Profinite.{u}) : jP p t P ≫ qP p t P = vP p t P := by
  sorry
/-- The actual boundary-test map lies over the stratum inclusion.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison).

Proof: The defining pullback lift for the boundary-test map commutes with its
projection. Compose with the full-tower projection, use boundary_square, and reassociate. -/
theorem test_boundary_square (P : Profinite.{u}) :
    testMap (boundary p t) P ≫ qP p t P = (test (stratumScheme t) P).hom ≫ stratumInclusion t := by
  sorry
/-- A module considered as an object of the unbounded derived category in degree zero.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
abbrev moduleAtZero {X : Scheme.{u}} (N : SiteMod F X) :
    DerivedCategory (SiteMod F X) :=
  (DerivedCategory.singleFunctor (SiteMod F X) 0).obj N
/-- The supplied module pulled exactly to the full-tower profinite test.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
abbrev testModule (N : SiteMod F (tower p t)) (P : Profinite.{u}) :
    DerivedCategory (SiteMod F (test (tower p t) P).left) :=
  (pullD F (test (tower p t) P).hom).obj (moduleAtZero F N)
/-- Boundary restriction of the derived direct image from the full-tower test.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
abbrev fullSource (N : SiteMod F (tower p t)) (P : Profinite.{u}) :
    DerivedCategory (SiteMod F (stratumScheme t)) :=
  (pullD F (stratumInclusion t)).obj ((pushD F (qP p t P)).obj (testModule F p t N P))
/-- Boundary restriction of the derived direct image from the punctured-tower test.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
abbrev openSource (N : SiteMod F (tower p t)) (P : Profinite.{u}) :
    DerivedCategory (SiteMod F (stratumScheme t)) :=
  (pullD F (stratumInclusion t)).obj
    ((pushD F (vP p t P)).obj ((pullD F (jP p t P)).obj (testModule F p t N P)))
/-- The actual inverse-image/direct-image unit for the puncture, pushed to the base and
restricted to the stratum. The composition is the recorded canonical comparison.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def openUnit (N : SiteMod F (tower p t)) (P : Profinite.{u}) :
    fullSource F p t N P ⟶ openSource F p t N P :=
  (pullD F (stratumInclusion t)).map
    ((pushD F (qP p t P)).map
      ((derivedAdjunction F (jP p t P)).unit.app (testModule F p t N P)) ≫
    (pushComp F (jP p t P) (qP p t P)).hom.app _ ≫
    eqToHom (congrArg (fun f ↦ (pushD F f).obj
      ((pullD F (jP p t P)).obj (testModule F p t N P))) (puncture_square p t P)))
/-- The existing adjunction mate for the actual boundary square.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def boundaryExchange (N : SiteMod F (tower p t)) (P : Profinite.{u}) :=
  (RootCoordinateFace.exchange (coefficients F) (testMap (boundary p t) P)
    (test (stratumScheme t) P).hom (qP p t P) (stratumInclusion t)
    (test_boundary_square p t P)).app (testModule F p t N P)
/-- The canonical pullback-composition identification along the actual boundary-test square.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def boundaryPullback (P : Profinite.{u}) :
    ((CondensedRing.upperStar (coefficients F) (test (tower p t) P).hom) ⋙
      CondensedRing.upperStar (coefficients F) (testMap (boundary p t) P)) ≅
    CondensedRing.upperStar (coefficients F) (boundary p t) ⋙
      CondensedRing.upperStar (coefficients F) (test (stratumScheme t) P).hom :=
  (CondensedRing.upperStarComp (coefficients F) (testMap (boundary p t) P)
    (test (tower p t) P).hom).symm ≪≫
    eqToIso (congrArg (CondensedRing.upperStar (coefficients F))
      (pullback.lift_snd _ _ _)) ≪≫
    CondensedRing.upperStarComp (coefficients F) (test (stratumScheme t) P).hom (boundary p t)
/-- The degree-zero embedding for modules on a scheme.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def zeroFunctor (X : Scheme.{u}) : SiteMod F X ⥤ DerivedCategory (SiteMod F X) :=
  DerivedCategory.singleFunctor (SiteMod F X) 0
/-- The degree-zero embedding for internal modules on the profinite point.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def pointZeroFunctor : PointMod F ⥤ DerivedCategory (PointMod F) :=
  DerivedCategory.singleFunctor (PointMod F) 0
/-- The supplied ordinary boundary identification transported to degree zero.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def boundaryIdentification (N : SiteMod F (tower p t)) (B : PointMod F)
    (e : (CondensedRing.upperStar (coefficients F) (boundary p t)).obj N ≅
      (pointPull F (stratumScheme t)).obj B) :
    (pullD F (boundary p t)).obj ((zeroFunctor F (tower p t)).obj N) ≅
      (pointPullD F (stratumScheme t)).obj ((pointZeroFunctor F).obj B) :=
  (CondensedRing.upperStar (coefficients F) (boundary p t)).mapDerivedCategorySingleFunctor 0
    |>.app N |>.trans ((zeroFunctor F (stratumScheme t)).mapIso e) |>.trans
      (((pointPull F (stratumScheme t)).mapDerivedCategorySingleFunctor 0).app B).symm
/-- The exact derived form of the canonical boundary pullback-composition identification.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def boundaryPullbackD (P : Profinite.{u}) :
    pullD F (test (tower p t) P).hom ⋙ pullD F (testMap (boundary p t) P) ≅
      pullD F (boundary p t) ⋙ pullD F (test (stratumScheme t) P).hom :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (boundaryPullback F p t P) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
/-- The exact derived form of the recorded point pullback-composition identification.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def pointPullCompD {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pointPullD F Y ⋙ pullD F f ≅ pointPullD F X :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointPullComp F f)
/-- The supplied boundary-model identification pulled to the actual profinite test.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def boundaryModelDerivedMap (N : SiteMod F (tower p t)) (P : Profinite.{u})
    (B : PointMod F)
    (e : (CondensedRing.upperStar (coefficients F) (boundary p t)).obj N ≅
      (pointPull F (stratumScheme t)).obj B) :
    (pullD F (testMap (boundary p t) P)).obj (testModule F p t N P) ⟶
      (pointPullD F (test (stratumScheme t) P).left).obj ((pointZeroFunctor F).obj B) :=
  (boundaryPullbackD F p t P).hom.app (moduleAtZero F N) ≫
    (pullD F (test (stratumScheme t) P).hom).map (boundaryIdentification F p t N B e).hom ≫
    (pointPullCompD F (test (stratumScheme t) P).hom).hom.app ((pointZeroFunctor F).obj B)
/-- The canonical restriction of full-tower sections to the supplied boundary model,
formed from the actual exchange adjunct and the supplied identification.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def fullRestriction (N : SiteMod F (tower p t)) (P : Profinite.{u})
    (B : PointMod F)
    (e : (CondensedRing.upperStar (coefficients F) (boundary p t)).obj N ≅
      (pointPull F (stratumScheme t)).obj B) :
    fullSource F p t N P ⟶
      (pushD F (test (stratumScheme t) P).hom).obj
        ((pointPullD F (test (stratumScheme t) P).left).obj ((pointZeroFunctor F).obj B)) :=
  boundaryExchange F p t N P ≫
    (pushD F (test (stratumScheme t) P).hom).map (boundaryModelDerivedMap F p t N P B e)
/-- The pulled-back derived internal functions of the profinite parameter with values in the model.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
abbrev target (B : PointMod F) (P : Profinite.{u}) :=
  (pointPullD F (stratumScheme t)).obj ((parameterFunctions F P).obj ((pointZeroFunctor F).obj B))
/-- The canonical boundary comparison: the open unit and parameter evaluation are
isomorphisms, and the comparison is normalized by their composite being full-tower restriction.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def NormalizedComparison (N : SiteMod F (tower p t)) (B : PointMod F)
    (e : (CondensedRing.upperStar (coefficients F) (boundary p t)).obj N ≅
      (pointPull F (stratumScheme t)).obj B) (P : Profinite.{u}) : Prop :=
  IsIso (openUnit F p t N P) ∧
    IsIso ((derivedEvaluation F (stratumScheme t) P).app ((pointZeroFunctor F).obj B)) ∧
    ∃ α : openSource F p t N P ≅ target F t B P,
      openUnit F p t N P ≫ α.hom ≫
        (derivedEvaluation F (stratumScheme t) P).app ((pointZeroFunctor F).obj B) =
        fullRestriction F p t N P B e
/-- The map on punctured derived direct images induced by a map of supplied extensions.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def sourceModuleMap {N N' : SiteMod F (tower p t)} (f : N ⟶ N') (P : Profinite.{u}) :
    openSource F p t N P ⟶ openSource F p t N' P :=
  (pullD F (stratumInclusion t)).map
    ((pushD F (vP p t P)).map ((pullD F (jP p t P)).map
      ((pullD F (test (tower p t) P).hom).map ((zeroFunctor F (tower p t)).map f))))
/-- The map on derived internal functions induced by a map of boundary models.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def targetModuleMap {B B' : PointMod F} (f : B ⟶ B') (P : Profinite.{u}) :
    target F t B P ⟶ target F t B' P :=
  (pointPullD F (stratumScheme t)).map
    ((parameterFunctions F P).map ((pointZeroFunctor F).map f))
/-- Restriction of derived internal functions along a continuous parameter map.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def targetParameterMap (B : PointMod F) {P P' : Profinite.{u}} (f : P' ⟶ P) :
    target F t B P ⟶ target F t B P' :=
  (pointPullD F (stratumScheme t)).map
    ((parameterFunctionsMap F f).app ((pointZeroFunctor F).obj B))
/-- The actual test map commutes with its structural projection.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison).

Proof: The test map is the pullback lift of the parameter projection and the
structural map composed with the supplied scheme morphism. Its second projection
is therefore exactly the structural projection followed by that morphism. -/
theorem testMap_projection {X Y : Scheme.{u}} (g : X ⟶ Y) (P : Profinite.{u}) :
    testMap g P ≫ (test Y P).hom = (test X P).hom ≫ g := by
  sorry
/-- The actual restriction of punctured-tower sections along a continuous parameter map.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def sourceParameterMap (N : SiteMod F (tower p t)) {P P' : Profinite.{u}} (f : P' ⟶ P) :
    openSource F p t N P ⟶ openSource F p t N P' := by
  let a := ((profiniteToProEtOf (puncture p t)).map f).left
  let K := (pullD F (jP p t P)).obj (testModule F p t N P)
  have w : a ≫ vP p t P = vP p t P' := by
    dsimp [a, vP]
    rw [← Category.assoc, ← Category.assoc, MorphismProperty.Over.w,
      Category.assoc]
  have w' : a ≫ jP p t P ≫ (test (tower p t) P).hom =
      jP p t P' ≫ (test (tower p t) P').hom := by
    calc
      _ = a ≫ ((test (puncture p t) P).hom ≫ (parameterRootOpen p t).ι) :=
        congrArg (a ≫ ·) (testMap_projection (parameterRootOpen p t).ι P)
      _ = (test (puncture p t) P').hom ≫ (parameterRootOpen p t).ι := by
        rw [← Category.assoc]
        exact congrArg (· ≫ (parameterRootOpen p t).ι)
          (MorphismProperty.Over.w ((profiniteToProEtOf (puncture p t)).map f))
      _ = _ := (testMap_projection (parameterRootOpen p t).ι P').symm
  let z := (moduleAtZero F N)
  let e : pullD F (test (tower p t) P).hom ⋙ pullD F (jP p t P) ⋙ pullD F a ≅
      pullD F (test (tower p t) P').hom ⋙ pullD F (jP p t P') :=
    Functor.isoWhiskerLeft _ (pullComp F a (jP p t P)).symm ≪≫
      (pullComp F (a ≫ jP p t P) (test (tower p t) P).hom).symm ≪≫
      eqToIso (congrArg (pullD F) (by simpa only [Category.assoc] using w')) ≪≫
      pullComp F (jP p t P') (test (tower p t) P').hom
  exact (pullD F (stratumInclusion t)).map
    (sectionRestriction F a (vP p t P) K ≫
      eqToHom (congrArg (fun v ↦ (pushD F v).obj ((pullD F a).obj K)) w) ≫
      (pushD F (vP p t P')).map (e.hom.app z))
/-- The equation identifying a proposed comparison with actual full-tower restriction.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def Normalization (N : SiteMod F (tower p t)) (B : PointMod F)
    (e : (CondensedRing.upperStar (coefficients F) (boundary p t)).obj N ≅
      (pointPull F (stratumScheme t)).obj B) (P : Profinite.{u})
    (α : openSource F p t N P ≅ target F t B P) : Prop :=
  openUnit F p t N P ≫ α.hom ≫
    (derivedEvaluation F (stratumScheme t) P).app ((pointZeroFunctor F).obj B) =
    fullRestriction F p t N P B e
/-- The supplied derived module pulled to the actual punctured-tower test.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def pulledOpenModule (N : SiteMod F (tower p t)) (P : Profinite.{u}) :=
  (pullD F (jP p t P)).obj (testModule F p t N P)
/-- Canonical exact pullback of the internal-functions target along a stratum map.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def targetPullback {X : Scheme.{u}} (g : X ⟶ stratumScheme t) (B : PointMod F)
    (P : Profinite.{u}) :
    (pullD F g).obj (target F t B P) ⟶
      (pointPullD F X).obj ((parameterFunctions F P).obj ((pointZeroFunctor F).obj B)) :=
  (pointPullCompD F g).hom.app ((parameterFunctions F P).obj ((pointZeroFunctor F).obj B))
/-- The actual exchange arrow on punctured direct images, followed by the supplied
map of pulled-back coefficient modules; it is not an arbitrarily chosen base-change map.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def sourceBaseChange
    {R' : Type u} [CommRing R'] {r' : ℕ} (p' : ℕ) (t' : Fin r' → R')
    (g : Spec (.of R') ⟶ Spec (.of R))
    (h : stratumScheme t' ⟶ stratumScheme t)
    (ws : h ≫ stratumInclusion t = stratumInclusion t' ≫ g)
    (N : SiteMod F (tower p t)) (N' : SiteMod F (tower p' t'))
    (P P' : Profinite.{u})
    (a : (test (puncture p' t') P').left ⟶ (test (puncture p t) P).left)
    (w : a ≫ vP p t P = vP p' t' P' ≫ g)
    (f : (pullD F a).obj (pulledOpenModule F p t N P) ⟶
      pulledOpenModule F p' t' N' P') :
    (pullD F h).obj (openSource F p t N P) ⟶ openSource F p' t' N' P' :=
  ((pullComp F h (stratumInclusion t)).inv.app _ ≫
    eqToHom (congrArg (fun v ↦ (pullD F v).obj
      ((pushD F (vP p t P)).obj (pulledOpenModule F p t N P))) ws) ≫
    (pullComp F (stratumInclusion t') g).hom.app _) ≫
    (pullD F (stratumInclusion t')).map
      ((RootCoordinateFace.exchange (coefficients F) a (vP p' t' P') (vP p t P) g w).app
        (pulledOpenModule F p t N P) ≫ (pushD F (vP p' t' P')).map f)
/-- The isomorphism whose forward arrow identifies the pulled boundary module
with the pulled supplied model.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def boundaryModelDerivedIso (N : SiteMod F (tower p t)) (P : Profinite.{u})
    (B : PointMod F)
    (e : (CondensedRing.upperStar (coefficients F) (boundary p t)).obj N ≅
      (pointPull F (stratumScheme t)).obj B) :
    (pullD F (testMap (boundary p t) P)).obj (testModule F p t N P) ≅
      (pointPullD F (test (stratumScheme t) P).left).obj ((pointZeroFunctor F).obj B) :=
  (boundaryPullbackD F p t P).app (moduleAtZero F N) ≪≫
    (pullD F (test (stratumScheme t) P).hom).mapIso (boundaryIdentification F p t N B e) ≪≫
    (pointPullCompD F (test (stratumScheme t) P).hom).app ((pointZeroFunctor F).obj B)
/-- The direct image of the constant model along the actual parameter projection.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def boundaryParameterSource (B : PointMod F) (P : Profinite.{u}) :=
  (pushD F (test (stratumScheme t) P).hom).obj
    ((pointPullD F (test (stratumScheme t) P).left).obj ((pointZeroFunctor F).obj B))
/-- Transport of parameter functions by evaluation, the actual exchange adjunct,
the supplied boundary arrow, and inverse evaluation in the target.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def parameterTargetTransport
    {R' : Type u} [CommRing R'] {r' : ℕ} (t' : Fin r' → R')
    (h : stratumScheme t' ⟶ stratumScheme t)
    (P P' : Profinite.{u})
    (b : (test (stratumScheme t') P').left ⟶ (test (stratumScheme t) P).left)
    (w : b ≫ (test (stratumScheme t) P).hom = (test (stratumScheme t') P').hom ≫ h)
    (B B' : PointMod F)
    (f : (pullD F b).obj
      ((pointPullD F (test (stratumScheme t) P).left).obj ((pointZeroFunctor F).obj B)) ⟶
      (pointPullD F (test (stratumScheme t') P').left).obj ((pointZeroFunctor F).obj B'))
    (hβ : IsIso ((derivedEvaluation F (stratumScheme t') P').app ((pointZeroFunctor F).obj B'))) :
    (pullD F h).obj (target F t B P) ⟶ target F t' B' P' :=
  (pullD F h).map ((derivedEvaluation F (stratumScheme t) P).app ((pointZeroFunctor F).obj B)) ≫
    (RootCoordinateFace.exchange (coefficients F) b (test (stratumScheme t') P').hom
      (test (stratumScheme t) P).hom h w).app
        ((pointPullD F (test (stratumScheme t) P).left).obj ((pointZeroFunctor F).obj B)) ≫
    (pushD F (test (stratumScheme t') P').hom).map f ≫
    @inv _ _ _ _ ((derivedEvaluation F (stratumScheme t') P').app
      ((pointZeroFunctor F).obj B')) hβ
/-- The existing exact pullback-composition identification associated to a commuting square.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def squarePull {X' X Y' Y : Scheme.{u}}
    (a : X' ⟶ X) (q' : X' ⟶ Y') (q : X ⟶ Y) (g : Y' ⟶ Y)
    (w : a ≫ q = q' ≫ g) :=
  RootCoordinateFace.squareUpper (coefficients F) a q' q g w
/-- The arrow on the punctured module induced by an action or morphism on the full tower.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def familyOpenMap
    {R' : Type u} [CommRing R'] {r' : ℕ} (p' : ℕ) (t' : Fin r' → R')
    (N : SiteMod F (tower p t)) (N' : SiteMod F (tower p' t'))
    (P P' : Profinite.{u})
    (u : (test (tower p' t') P').left ⟶ (test (tower p t) P).left)
    (a : (test (puncture p' t') P').left ⟶ (test (puncture p t) P).left)
    (w : a ≫ jP p t P = jP p' t' P' ≫ u)
    (f : (pullD F u).obj (testModule F p t N P) ⟶ testModule F p' t' N' P') :
    (pullD F a).obj (pulledOpenModule F p t N P) ⟶ pulledOpenModule F p' t' N' P' :=
  (squarePull F a (jP p' t' P') (jP p t P) u w).inv.app (testModule F p t N P) ≫
    (pullD F (jP p' t' P')).map f
/-- The corresponding boundary-model arrow induced by that same full-tower action.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def familyBoundaryMap
    {R' : Type u} [CommRing R'] {r' : ℕ} (p' : ℕ) (t' : Fin r' → R')
    (N : SiteMod F (tower p t)) (N' : SiteMod F (tower p' t'))
    (B B' : PointMod F)
    (e : (CondensedRing.upperStar (coefficients F) (boundary p t)).obj N ≅
      (pointPull F (stratumScheme t)).obj B)
    (e' : (CondensedRing.upperStar (coefficients F) (boundary p' t')).obj N' ≅
      (pointPull F (stratumScheme t')).obj B')
    (P P' : Profinite.{u})
    (u : (test (tower p' t') P').left ⟶ (test (tower p t) P).left)
    (b : (test (stratumScheme t') P').left ⟶ (test (stratumScheme t) P).left)
    (w : b ≫ testMap (boundary p t) P = testMap (boundary p' t') P' ≫ u)
    (f : (pullD F u).obj (testModule F p t N P) ⟶ testModule F p' t' N' P') :=
  (pullD F b).map (boundaryModelDerivedIso F p t N P B e).inv ≫
    (squarePull F b (testMap (boundary p' t') P') (testMap (boundary p t) P) u w).inv.app
      (testModule F p t N P) ≫
    (pullD F (testMap (boundary p' t') P')).map f ≫
    (boundaryModelDerivedIso F p' t' N' P' B' e').hom
/-- The comparison square for morphisms of supplied extensions and boundary models.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def ModuleNaturality : Prop :=
  ∀ {N N' : SiteMod F (tower p t)}
    {B B' : PointMod F}
    (e : (CondensedRing.upperStar (coefficients F) (boundary p t)).obj N ≅
      (pointPull F (stratumScheme t)).obj B)
    (e' : (CondensedRing.upperStar (coefficients F) (boundary p t)).obj N' ≅
      (pointPull F (stratumScheme t)).obj B')
    (f : N ⟶ N') (g : B ⟶ B')
    (_w : (CondensedRing.upperStar (coefficients F) (boundary p t)).map f ≫ e'.hom =
      e.hom ≫ (pointPull F (stratumScheme t)).map g)
    (P : Profinite.{u}) (_h : NormalizedComparison F p t N B e P)
    (_h' : NormalizedComparison F p t N' B' e' P)
    (α : openSource F p t N P ≅ target F t B P)
    (α' : openSource F p t N' P ≅ target F t B' P)
    (_hα : Normalization F p t N B e P α) (_hα' : Normalization F p t N' B' e' P α'),
    sourceModuleMap F p t f P ≫ α'.hom = α.hom ≫ targetModuleMap F t g P

/-- The comparison square for every continuous map of profinite parameters.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def ParameterNaturality : Prop :=
  ∀ (N : SiteMod F (tower p t)) (B : PointMod F)
    (e : (CondensedRing.upperStar (coefficients F) (boundary p t)).obj N ≅
      (pointPull F (stratumScheme t)).obj B)
    {P P' : Profinite.{u}} (f : P' ⟶ P)
    (_h : NormalizedComparison F p t N B e P) (_h' : NormalizedComparison F p t N B e P')
    (α : openSource F p t N P ≅ target F t B P)
    (α' : openSource F p t N P' ≅ target F t B P')
    (_hα : Normalization F p t N B e P α) (_hα' : Normalization F p t N B e P' α'),
    sourceParameterMap F p t N f ≫ α'.hom = α.hom ≫ targetParameterMap F t B f

/-- The comparison square on entire base-changed test schemes for a compatible tower
morphism and its module action. This includes continuous profinite families,
before point evaluation.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def FamilyNaturality : Prop :=
  ∀ {R' : Type u} [CommRing R'] {r' : ℕ} (p' : ℕ) (t' : Fin r' → R')
    (g : Spec (.of R') ⟶ Spec (.of R)) [WeaklyEtale g]
    (h : stratumScheme t' ⟶ stratumScheme t)
    (ws : h ≫ stratumInclusion t = stratumInclusion t' ≫ g)
    (N : SiteMod F (tower p t)) (N' : SiteMod F (tower p' t'))
    (B B' : PointMod F)
    (e : (CondensedRing.upperStar (coefficients F) (boundary p t)).obj N ≅
      (pointPull F (stratumScheme t)).obj B)
    (e' : (CondensedRing.upperStar (coefficients F) (boundary p' t')).obj N' ≅
      (pointPull F (stratumScheme t')).obj B')
    (P P' : Profinite.{u})
    (u : (test (tower p' t') P').left ⟶ (test (tower p t) P).left)
    (_wu : u ≫ qP p t P = qP p' t' P' ≫ g)
    (a : (test (puncture p' t') P').left ⟶ (test (puncture p t) P).left)
    (wa : a ≫ jP p t P = jP p' t' P' ≫ u)
    (wav : a ≫ vP p t P = vP p' t' P' ≫ g)
    (b : (test (stratumScheme t') P').left ⟶ (test (stratumScheme t) P).left)
    (wb : b ≫ (test (stratumScheme t) P).hom = (test (stratumScheme t') P').hom ≫ h)
    (wbi : b ≫ testMap (boundary p t) P = testMap (boundary p' t') P' ≫ u)
    (f : (pullD F u).obj (testModule F p t N P) ⟶ testModule F p' t' N' P')
    (_hn : NormalizedComparison F p t N B e P)
    (hn' : NormalizedComparison F p' t' N' B' e' P')
    (α : openSource F p t N P ≅ target F t B P)
    (α' : openSource F p' t' N' P' ≅ target F t' B' P')
    (_hα : Normalization F p t N B e P α) (_hα' : Normalization F p' t' N' B' e' P' α'),
    sourceBaseChange F p t p' t' g h ws N N' P P' a wav
      (familyOpenMap F p t p' t' N N' P P' u a wa f) ≫ α'.hom =
    (pullD F h).map α.hom ≫ parameterTargetTransport F t t' h P P' b wb B B'
      (familyBoundaryMap F p t p' t' N N' B B' e e' P P' u b wbi f) hn'.2.1

/-- The normalized comparison for every finite-dimensional model and supplied lisse extension,
together with module, parameter, pro-etale-base-change and family naturality.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-comparison). -/
def Assertion (E : Type u) [Field E] [Algebra E F] : Prop :=
  (∀ (M : Type u) [AddCommGroup M] [Module E M] [FiniteDimensional E M]
    (N : SiteMod F (tower p t)),
    IsLisseCoefficientModule (coefficients F) N →
    ∀ e : (CondensedRing.upperStar (coefficients F) (boundary p t)).obj N ≅
      (pointPull F (stratumScheme t)).obj (model F E M),
    ∀ P : Profinite.{u}, NormalizedComparison F p t N (model F E M) e P) ∧
    ModuleNaturality F p t ∧ ParameterNaturality F p t ∧ FamilyNaturality F p t
end AlgebraicGeometry.ProEtale.RootBoundary
