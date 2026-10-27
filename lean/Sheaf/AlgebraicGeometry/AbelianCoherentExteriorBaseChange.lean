module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

public import Sheaf.AlgebraicGeometry.AbelianSpacePoincareData
public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Sheaf.AlgebraicGeometry.RelativeDualizingTracePair
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.RegularGroupSpace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePullbackTensorComparison
public import Sheaf.CategoryTheory.RingedSiteModuleCupProduct
public import Sheaf.Algebra.Homology.RingedSiteGlobalHomIdentification
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat

import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import WeilConjectures.AlgebraicGeometry.PerfectAffineBoundedProjective
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import Sheaf.AlgebraicGeometry.AbelianVariety.StructureSheafH1Dimension
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.AlgebraicGeometry.CoherentGroupBialgebra
import Sheaf.RingTheory.BoundedBialgebraExterior
import WeilConjectures.AlgebraicGeometry.AffinePerfectHomColimit
import Sheaf.AlgebraicGeometry.SpaceAffineBaseHigherImageSections
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine

/-! # Exterior coherent cohomology of relative abelian spaces

Source: Milne, Abelian Varieties, I Remark 8.7(e) and I Lemma 12.2, for the field
inputs; Stacks, Tags 0CTM and 08IR, for perfect pushforward and derived base change.
The relative assertion is the agent-stated prerequisite recorded in the DAG, rather
than a theorem attributed to Milne
(blueprint: lem-sfb-abelian-coherent-exterior-base-change).

## Main definitions and statement
- `Presentation` transports the canonical ordinary and derived module functors.
- `ExteriorOnCharts` fixes the graded isomorphism on pure wedges and restrictions.
- `exchange` and `BaseChangeNormalization` specify both base-change comparisons.
- `BaseChangeProducts` states their compatibility with cups and exterior maps.
- `AffineConclusion` records the additive-cohomology and finite-projectivity clauses.
- `abelian_coherent_exterior_base_change` states the complete relative theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.RingedSiteCup

namespace AlgebraicGeometry.AlgebraicSpace.CoherentExterior

/-- The published tensor corner on the actual small affine etale model.
Source: Stacks 03G7, 039Z, 06YU
(blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def corner {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  CategoryTheory.RingedSiteGlobalHomIdentification.corner X.smallStructureSheaf
    X.derivedDualityModel.closed

/-- Its existing K-flat representative comparison.
Source: Stacks 06YU (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def model {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  CategoryTheory.RingedSiteGlobalHomIdentification.tensorModel X.smallStructureSheaf
    X.derivedDualityModel.closed X.derivedDualityModel.models

/-- The computation counit of a ringed presentation on actual cochain complexes,
including both quotient-to-homotopy comparison isomorphisms.
Source: Stacks 06YY (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def presentationCounit {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (e : SheafOfModules.RingedTensorEdge (corner Y) (corner X))
    (P : CochainComplex Y.SmallModules ℤ) :
    e.left.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P) :=
  e.left.map ((DerivedCategory.quotientCompQhIso Y.SmallModules).inv.app P) ≫
    e.epsilon.app ((HomotopyCategory.quotient Y.SmallModules (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map ((e.pullback.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso X.SmallModules).hom.app _

/-- A presentation of the canonical ringed morphism through equivalent small module
models. The unit equations fix both adjunctions, and the computation-counit equation
fixes the derived comparison on every representative. These are conclusions of the
geometric theorem, not additional geometric hypotheses.
Source: Stacks 03D7, 07A6 (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
structure Presentation {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (e : SheafOfModules.RingedTensorEdge (corner Y) (corner X)) where
  ordinaryPull : e.pullback ≅ smallModuleTensorPullback f
  ordinaryPush : e.pushforward ≅ smallModuleDirectImage f
  derivedPull : e.left = spaceDerivedPullback f
  derivedPush : e.right = derivedDirectImage f
  ordinaryUnit : ∀ M : Y.SmallModules,
    e.moduleAdjunction.unit.app M ≫
      e.pushforward.map (ordinaryPull.hom.app M) ≫
      ordinaryPush.hom.app ((smallModuleTensorPullback f).obj M) =
        (spaceSmallTensorAdjunction f).unit.app M
  derivedAdjunction : HEq e.derivedAdjunction (spaceDerivedAdjunction f)
  [ordinaryAdditive : (smallModuleTensorPullback f).Additive]
  computation : ∀ P : CochainComplex Y.SmallModules ℤ,
    HEq (presentationCounit e P ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex ordinaryPull.hom (.up ℤ)).app P))
      ((spaceDerivedPullbackCounit f).app P)

/-- The higher module direct image of the structure module, in nonnegative degree.
Source: Stacks 079V (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
abbrev image {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (n : ℕ) :=
  (DerivedCategory.homologyFunctor Y.SmallModules (n : ℤ)).obj
    ((derivedDirectImage f).obj X.derivedStructure)

/-- The same cohomology using a presentation; `Presentation` identifies it with `image`.
Source: Stacks 079V (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
abbrev piece {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (e : SheafOfModules.RingedTensorEdge (corner Y) (corner X)) (n : ℕ) :=
  (cohomology (corner Y) (n : ℤ)).obj
    (e.right.obj ((degreeZero (corner X)).obj (SheafOfModules.unit X.smallStructureRings)))

/-- The relative cup product with coefficient multiplication, using the dependency's
canonical tensor-of-counits construction, followed only by the degree equality.
Source: Stacks 0B6C, 0FPJ (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def product {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (e : SheafOfModules.RingedTensorEdge (corner Y) (corner X)) (p q : ℕ) :
    piece e p ⊗ piece e q ⟶ piece e (p + q) :=
  moduleCupWith e (model Y) (model X)
    (SheafOfModules.unit X.smallStructureRings) (SheafOfModules.unit X.smallStructureRings)
    (SheafOfModules.unit X.smallStructureRings)
    ((λ_ (SheafOfModules.unit X.smallStructureRings)).hom) p q ≫
      eqToHom (congrArg (fun z : ℤ ↦ (cohomology (corner Y) z).obj
        (e.right.obj ((degreeZero (corner X)).obj
          (SheafOfModules.unit X.smallStructureRings)))) (Nat.cast_add p q).symm)

/-- Cup of two sections on an affine etale chart, including the sheaf tensor map.
Source: Stacks 03EK, 0B6C (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def cup {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (e : SheafOfModules.RingedTensorEdge (corner Y) (corner X)) (p q : ℕ)
    (U : Y.SmallEtaleModelᵒᵖ) (x : (piece e p).val.obj U) (y : (piece e q).val.obj U) :
    (piece e (p + q)).val.obj U :=
  (product e p q).val.app U
    (SheafOfModules.RingedTensor.pure Y.smallStructureSheaf (piece e p) (piece e q) U x y)

/-- Structural degree-zero map, with the canonical comparison from an ordinary
module to its derived direct image.
Source: Stacks 03G8, 079V (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def zero {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    SheafOfModules.unit Y.smallStructureRings ⟶ image f 0 :=
  traceSmallStructureMap f ≫
    (smallModuleDirectImage f).toRightDerivedZero.app
      (SheafOfModules.unit X.smallStructureRings) ≫
    ((smallModuleDirectImage f).homologyRightDerivedFunctorObjSingleFunctorIso
      (SheafOfModules.unit X.smallStructureRings) 0).inv

/-- The cohomology identification forced by a presentation's recorded direct image.
Source: Stacks 079V (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def presentationImage {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (e : SheafOfModules.RingedTensorEdge (corner Y) (corner X))
    (he : Presentation f e) (n : ℕ) : piece e n ≅ image f n :=
  eqToIso (congrArg (fun F : X.DerivedModules ⥤ Y.DerivedModules ↦
    (DerivedCategory.homologyFunctor Y.SmallModules (n : ℤ)).obj
      (F.obj X.derivedStructure)) he.derivedPush)

/-- The type of degreewise exterior comparisons on affine etale charts.
Source: Stacks 03G7, 0FPJ (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
abbrev ChartExterior {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (e : SheafOfModules.RingedTensorEdge (corner Y) (corner X)) :=
  ∀ (U : Y.SmallEtaleModelᵒᵖ) (n : ℕ),
    (⋀[Y.smallStructureSheaf.obj.obj U]^n ((piece e 1).val.obj U)) ≃ₗ[
      Y.smallStructureSheaf.obj.obj U] (piece e n).val.obj U

/-- The structural-unit, identity, cup-product and restriction normalizations of a
specified family of exterior comparisons. Pure wedges span, so the equations
specify the canonical graded algebra isomorphism, including degree zero.
Source: Stacks 03G7, 0FPJ; Milne I 12.2
(blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def ExteriorOnChartsWith {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (e : SheafOfModules.RingedTensorEdge (corner Y) (corner X))
    (he : Presentation f e) (w : ChartExterior e) : Prop :=
    (∀ (U : Y.SmallEtaleModelᵒᵖ) (r : Y.smallStructureSheaf.obj.obj U),
      (presentationImage f e he 0).hom.val.app U
        (w U 0 (r • exteriorPower.ιMulti _ 0 (fun i ↦ Fin.elim0 i))) =
          (zero f).val.app U r) ∧
    (∀ (U : Y.SmallEtaleModelᵒᵖ) (x : (piece e 1).val.obj U),
      w U 1 (exteriorPower.ιMulti _ 1 (fun _ ↦ x)) = x) ∧
    (∀ (U : Y.SmallEtaleModelᵒᵖ) (p q : ℕ)
      (x : Fin p → (piece e 1).val.obj U) (y : Fin q → (piece e 1).val.obj U),
      cup e p q U (w U p (exteriorPower.ιMulti _ p x))
          (w U q (exteriorPower.ιMulti _ q y)) =
        w U (p + q) (exteriorPower.ιMulti _ (p + q) (Fin.append x y))) ∧
    (∀ (U V : Y.SmallEtaleModelᵒᵖ) (a : U ⟶ V) (n : ℕ)
      (x : Fin n → (piece e 1).val.obj U),
      (piece e n).val.map a (w U n (exteriorPower.ιMulti _ n x)) =
        w V n (exteriorPower.ιMulti _ n (fun i ↦ (piece e 1).val.map a (x i))))

/-- Existence of the normalized exterior algebra isomorphism on the affine etale basis.
Source: Stacks 03G7, 0FPJ; Milne I 12.2
(blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def ExteriorOnCharts {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (e : SheafOfModules.RingedTensorEdge (corner Y) (corner X))
    (he : Presentation f e) : Prop :=
  ∃ w : ChartExterior e, ExteriorOnChartsWith f e he w

/-- The canonical derived exchange mate, followed by multiplication on the pulled
back structure module. This definition makes sense for every base map.
Source: Stacks 08IR (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def exchange {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : h ≫ f = f' ≫ g) :
    (spaceDerivedPullback g).obj ((derivedDirectImage f).obj X.derivedStructure) ⟶
      (derivedDirectImage f').obj X'.derivedStructure :=
  let K := (derivedDirectImage f).obj X.derivedStructure
  let paths : (spaceDerivedPullback f').obj ((spaceDerivedPullback g).obj K) ⟶
      (spaceDerivedPullback h).obj ((spaceDerivedPullback f).obj K) :=
    (spaceDerivedPullbackComp g f').inv.app K ≫
      eqToHom (congrArg (fun k : X' ⟶ Y ↦ (spaceDerivedPullback k).obj K) sq.symm) ≫
      (spaceDerivedPullbackComp f h).hom.app K
  (spaceDerivedAdjunction f').homEquiv _ _
    (paths ≫
      (spaceDerivedPullback h).map ((spaceDerivedAdjunction f).counit.app X.derivedStructure)) ≫
    (derivedDirectImage f').map (traceDerivedStructureMap h)

/-- Normalization of the higher-image comparison on every representative on which
pullback is computed termwise. The cycle lift is fixed by its inclusion equation;
the cohomology equation is the usual cocycle base-change formula. Quantifying over
all representatives also fixes identity and composition comparisons. No comparison
is chosen arbitrarily, and no flatness is required of the base map.
Source: Stacks 08IR, 0H9A
(blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def BaseChangeNormalization {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : h ≫ f = f' ≫ g)
    (c : ∀ n : ℕ, (smallModuleTensorPullback g).obj (image f n) ≅ image f' n) : Prop :=
  ∀ (P : CochainComplex Y.SmallModules ℤ)
    (a : DerivedCategory.Q.obj P ≅ (derivedDirectImage f).obj X.derivedStructure)
    (l : (spaceDerivedPullback g).obj (DerivedCategory.Q.obj P) ≅
      (smallTensorPullbackComplex g).obj P),
    l.hom = (spaceDerivedPullbackCounit g).app P →
    ∀ n : ℕ, ∃ z : (smallModuleTensorPullback g).obj (P.cycles (n : ℤ)) ⟶
        (((smallModuleTensorPullback g).mapHomologicalComplex (.up ℤ)).obj P).cycles (n : ℤ),
      z ≫ (((smallModuleTensorPullback g).mapHomologicalComplex (.up ℤ)).obj P).iCycles
          (n : ℤ) = (smallModuleTensorPullback g).map (P.iCycles (n : ℤ)) ∧
      (smallModuleTensorPullback g).map
          (P.homologyπ (n : ℤ) ≫
            (DerivedCategory.homologyFunctorFactors Y.SmallModules (n : ℤ)).inv.app P ≫
            (DerivedCategory.homologyFunctor Y.SmallModules (n : ℤ)).map a.hom) ≫
          (c n).hom =
        z ≫ (((smallModuleTensorPullback g).mapHomologicalComplex (.up ℤ)).obj P).homologyπ
          (n : ℤ) ≫
        (DerivedCategory.homologyFunctorFactors Y'.SmallModules (n : ℤ)).inv.app _ ≫
        (DerivedCategory.homologyFunctor Y'.SmallModules (n : ℤ)).map
          (l.inv ≫ (spaceDerivedPullback g).map a.hom ≫ exchange f g h f' sq)

/-- The canonical higher-image comparison on a local pulled-back section, transported
through the two ringed presentations. The local tensor is the already recorded
adjunction-unit construction, not a freely selected section map.
Source: Stacks 03D7, 0H9A (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def baseChangeSection {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (e : SheafOfModules.RingedTensorEdge (corner Y) (corner X)) (he : Presentation f e)
    (e' : SheafOfModules.RingedTensorEdge (corner Y') (corner X'))
    (he' : Presentation f' e')
    (c : ∀ n : ℕ, (smallModuleTensorPullback g).obj (image f n) ≅ image f' n)
    (n : ℕ) {G : Over S} {x : yoneda.obj G ⟶ Y'.obj.obj}
    (U : SingleComplex.Neighbourhood G x)
    (V : SingleComplex.Neighbourhood G (x ≫ g.hom.hom))
    (a : ((SingleComplex.neighbourhoodChart (x := x)).obj U).obj.left ⟶
      ((SingleComplex.neighbourhoodChart (x := x ≫ g.hom.hom)).obj V).obj.left)
    (ha : SingleComplex.Compatible g U V a) (b : (SingleComplex.ringDiagram x).obj (op U))
    (m : (piece e n).val.obj (op V.right)) : (piece e' n).val.obj (op U.right) :=
  (presentationImage f' e' he' n).inv.val.app (op U.right)
    ((c n).hom.val.app (op U.right)
      (SingleComplex.localSection g (image f n) U V a ha b
        ((presentationImage f e he n).hom.val.app (op V.right) m)))

/-- Base change preserves both the relative cup product and the exterior isomorphisms.
The two equations respectively send b tensor (v cup w) to (b tensor v) cup
(1 tensor w), and b tensor the wedge comparison to b times the wedge comparison
of the pulled-back degree-one classes. All compatible affine charts are tested;
these local tensors generate tensor pullback. The same comparisons c occur in
`BaseChangeNormalization`, so no unrelated multiplicative equivalence is used.
Source: Stacks 0H9A; proof step 7 of the blueprint prerequisite
(blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def BaseChangeProducts {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (c : ∀ n : ℕ, (smallModuleTensorPullback g).obj (image f n) ≅ image f' n) : Prop :=
  ∃ (e : SheafOfModules.RingedTensorEdge (corner Y) (corner X)) (he : Presentation f e)
    (e' : SheafOfModules.RingedTensorEdge (corner Y') (corner X'))
    (he' : Presentation f' e') (w : ChartExterior e) (w' : ChartExterior e'),
    ExteriorOnChartsWith f e he w ∧ ExteriorOnChartsWith f' e' he' w' ∧
    ∀ (G : Over S) (x : yoneda.obj G ⟶ Y'.obj.obj)
      (U : SingleComplex.Neighbourhood G x)
      (V : SingleComplex.Neighbourhood G (x ≫ g.hom.hom))
      (a : ((SingleComplex.neighbourhoodChart (x := x)).obj U).obj.left ⟶
        ((SingleComplex.neighbourhoodChart (x := x ≫ g.hom.hom)).obj V).obj.left)
      (ha : SingleComplex.Compatible g U V a)
      (b : (SingleComplex.ringDiagram x).obj (op U)),
      (∀ (p q : ℕ) (m : (piece e p).val.obj (op V.right))
        (n : (piece e q).val.obj (op V.right)),
        baseChangeSection f g f' e he e' he' c (p + q) U V a ha b
            (cup e p q (op V.right) m n) =
          cup e' p q (op U.right)
            (baseChangeSection f g f' e he e' he' c p U V a ha b m)
            (baseChangeSection f g f' e he e' he' c q U V a ha 1 n)) ∧
      (∀ (n : ℕ) (v : Fin n → (piece e 1).val.obj (op V.right)),
        baseChangeSection f g f' e he e' he' c n U V a ha b
            (w (op V.right) n (exteriorPower.ιMulti _ n v)) =
          b • w' (op U.right) n (exteriorPower.ιMulti _ n
            (fun i ↦ baseChangeSection f g f' e he e' he' c 1 U V a ha 1 (v i))))

/-- The actual base change of a relative abelian space to a scheme parameter.
Source: Stacks 02X2 (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
abbrev family {S : Scheme.{u}} (A : AlgebraicSpace S) (T : Over S) :=
  Poincare.product (groupSpaceProjection A) (groupSpaceProjection (schemeSpace T))

/-- Its projection to the parameter scheme, retaining the actual sheaf fibre product.
Source: Stacks 02X2 (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def projection {S : Scheme.{u}} (A : AlgebraicSpace S) (T : Over S) :
    family A T ⟶ schemeSpace T :=
  Poincare.snd (groupSpaceProjection A) (groupSpaceProjection (schemeSpace T))

/-- Zariski realization of the higher image on a represented scheme.
Source: Stacks 03G7, 039Z (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
abbrev zariskiImage {S : Scheme.{u}} (A : AlgebraicSpace S) (T : Over S) (n : ℕ) :=
  (Poincare.schemeModule T).obj (image (projection A T) n)

/-- Actual additive-sheaf cohomology, as specified by the cup-product dependency.
Source: Stacks 03FD (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
abbrev additiveH {S : Scheme.{u}} (X : AlgebraicSpace S) (n : ℕ) :=
  ((Sheaf.Γ X.smallEtaleModelTopology AddCommGrpCat.{u}).rightDerived n).obj
    ((SheafOfModules.toSheaf _).obj (SheafOfModules.unit X.smallStructureRings))

/-- The affine base action on additive cohomology is induced by the actual regular
function pullbacks, followed by the existing module-to-additive cohomology comparison.
Source: Stacks 03FD, 0B6C (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
abbrev affineHModule {S : Scheme.{u}} (R : Type u) [CommRing R]
    (T : Over S) (a : T.left ≅ Spec (.of R)) (X : AlgebraicSpace S)
    (f : X ⟶ schemeSpace T) (n : ℕ) : Module R (additiveH X n) :=
  letI : Module (scalars (corner X)) (additiveH X n) :=
    globalCohomologyModule (corner X) (SheafOfModules.unit X.smallStructureRings) n
  Module.compHom (R := scalars (corner X)) (additiveH X n)
    (affineGlobalScalar R T a X f)

/-- Affine additive cohomology with its structural base-ring module structure.
Source: Stacks 03FD, 08EX (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def affineH {S : Scheme.{u}} (R : Type u) [CommRing R]
    (T : Over S) (a : T.left ≅ Spec (.of R)) (X : AlgebraicSpace S)
    (f : X ⟶ schemeSpace T) (n : ℕ) : ModuleCat.{u} R :=
  @ModuleCat.of R _ (additiveH X n) _ (affineHModule R T a X f n)

/-- Pulling a scalar back and applying the canonical zeroth derived-sections unit.
Source: Stacks 03FD, 03G7 (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def affineZero {S : Scheme.{u}} (R : Type u) [CommRing R]
    (T : Over S) (a : T.left ≅ Spec (.of R)) (X : AlgebraicSpace S)
    (f : X ⟶ schemeSpace T) (r : R) : additiveH X 0 :=
  (Sheaf.Γ X.smallEtaleModelTopology AddCommGrpCat.{u}).toRightDerivedZero.app
    ((SheafOfModules.toSheaf _).obj (SheafOfModules.unit X.smallStructureRings))
    ((globalUnderlyingSections (corner X)).hom.app
      (SheafOfModules.unit X.smallStructureRings)
      (SheafOfModules.Hom.mk (PresheafOfModules.sectionsSMul
        (SheafOfModules.unit X.smallStructureRings).val (affineGlobalScalar R T a X f r))))

/-- Cup product on the actual additive-sheaf cohomology, with multiplication in O.
Source: Stacks 0B6C, 0FPJ (blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def affineCup {S : Scheme.{u}} (X : AlgebraicSpace S) (p q : ℕ)
    (x : additiveH X p) (y : additiveH X q) : additiveH X (p + q) :=
  globalCupWith (corner X) (model X)
    (SheafOfModules.unit X.smallStructureRings) (SheafOfModules.unit X.smallStructureRings)
    (SheafOfModules.unit X.smallStructureRings)
    ((λ_ (SheafOfModules.unit X.smallStructureRings)).hom) p q x y

/-- The affine clauses, with finite projectivity rather than freeness. The tilde
comparison uses the given affine identification of T; all degrees are retained.
Source: Stacks 08EX, 01C6; Milne I 12.2
(blueprint: lem-sfb-abelian-coherent-exterior-base-change). -/
def AffineConclusion {S : Scheme.{u}} (A : AlgebraicSpace S) (T : Over S)
    (R : Type u) [CommRing R] (a : T.left ≅ Spec (.of R)) : Prop :=
  (∀ n : ℕ, Module.Finite R (affineH R T a (family A T) (projection A T) n) ∧
    Module.Projective R (affineH R T a (family A T) (projection A T) n)) ∧
  (∃ N : ℕ, ∀ n : ℕ, N < n → Subsingleton (additiveH (family A T) n)) ∧
  (∀ n : ℕ, Nonempty
    ((Scheme.Modules.tensorPullback a.inv).obj (zariskiImage A T n) ≅
      tilde (affineH R T a (family A T) (projection A T) n))) ∧
  ∃ w : ∀ n : ℕ,
      (⋀[R]^n (affineH R T a (family A T) (projection A T) 1)) ≃ₗ[R]
        affineH R T a (family A T) (projection A T) n,
    (∀ r : R, w 0 (r • exteriorPower.ιMulti R 0 (fun i ↦ Fin.elim0 i)) =
      affineZero R T a (family A T) (projection A T) r) ∧
    (∀ x : additiveH (family A T) 1,
      w 1 (exteriorPower.ιMulti R 1 (fun _ ↦ x)) = x) ∧
    (∀ (p q : ℕ) (x : Fin p → additiveH (family A T) 1)
      (y : Fin q → additiveH (family A T) 1),
      affineCup (family A T) p q (w p (exteriorPower.ιMulti R p x))
          (w q (exteriorPower.ιMulti R q y)) =
        w (p + q) (exteriorPower.ιMulti R (p + q) (Fin.append x y)))

/-- Coherent cohomology of a proper smooth commutative group space with abelian
geometric fibres is exterior on degree one, Zariski finite locally free, and compatible
with every base change. Its affine cohomology uses the actual underlying additive
sheaf; the base action and all cup maps have been fixed above.
Source: Milne, Abelian Varieties, I Remark 8.7(e), printed p.37, and I Lemma 12.2,
printed p.55 (field inputs); Stacks 0CTM, 08IR (relative assembly).
(blueprint: lem-sfb-abelian-coherent-exterior-base-change).

Proof:
1. On etale scheme charts smoothness gives flatness by [lem-pc-smooth-flat]. Thus $a$ is flat.
   By [lem-sfb-space-flat-proper-fp-locality], every $A_T\to T$ is flat, proper and finitely
   presented, hence quasi-compact and quasi-separated. Each geometric fibre is a proper smooth
   connected group scheme over an algebraically closed field, so [lem-sc-abelian-variety-
   characterization] makes it geometrically integral, in particular reduced; it is connected by
   hypothesis and nonempty because of the identity section. Apply [lem-sfb-space-geometric-h0]:
   $\mathcal O_T\to f_*\mathcal O_{A_T}$ is the canonical isomorphism for every $T$, including
   nonreduced $T$.

2. Work over an affine open $U=\operatorname{Spec}R\subseteq S$, so $R$ is Noetherian. The
   module $\mathcal O_{A_U}$ is quasi-coherent of finite presentation (free of rank one over
   itself) and flat over $U$ by step 1. Thus [lem-sfb-proper-flat-space-derived-base-change]
   applies with $\mathcal F=\mathcal O_{A_U}$. It gives a Zariski perfect complex
   $K_U=R\epsilon_{U,*}Ra_{U,*}\mathcal O_{A_U}$ and its canonical small-etale counit
   identification with $Ra_{U,*}\mathcal O_{A_U}$. By [lem-pc-perfect-affine-bounded-
   projective], $K_U$ is represented by the tilde of a bounded finite-projective $R$-complex.
   The equivalence [lem-pc-affine-qcoh-derived-equivalence], whose inverse is derived global
   sections, identifies this with the perfect $R$-complex $K=R\Gamma(A_U,\mathcal O)$.

3. Use [lem-sfb-flat-space-derived-external-cup] on all finite powers of $A_U$. On $K$ let $\mu$
   be cup product, $u$ structural pullback, $\varepsilon=e^*$ at the identity section, and
   $\Delta=\kappa_{A_U,A_U}^{-1}m^*$ for the group law $m$. Naturality identifies the pullbacks
   of the two group identities $m(m\times1)=m(1\times m)$ and $m(e\times1)=m(1\times e)=1$ with
   coassociativity and the two counit identities for $\Delta$. Since $m^*$ and $e^*$ preserve
   products and units and $\kappa$ is multiplicative, $\Delta$ and $\varepsilon$ are algebra
   maps. Thus $K$ is a commutative bialgebra object in $D(R)$. For every $R\to B$, the same node
   identifies $B\otimes_R^{\mathbf L}K$ with $R\Gamma(A_B,\mathcal O)$ as a bialgebra object,
   via the canonical comparison.

4. Fix a geometric point $\operatorname{Spec}\Omega\to U$. Its fibre $G=A_\Omega$ is a proper
   smooth geometrically connected group scheme, hence an abelian variety [def-sc-abelian-
   variety]; [lem-sc-abelian-variety-characterization] makes it geometrically integral. Put
   $g=\dim G$. By [lem-sfb-abelian-structure-h1-dimension], $\dim_\Omega H^1(G,\mathcal O)=g$.
   Proper coherent finiteness [lem-fin-proper-coherent-finite-dimensional] makes each $H^i$
   finite dimensional. The finite-type $\Omega$-scheme $G$ is Noetherian, and [lem-sc-
   noetherian-cohomology-above-dimension] gives $H^i=0$ for $i>g$. The bialgebra [lem-sfb-
   coherent-group-bialgebra] has $H^0=\Omega$, the signed product and the required coproduct and
   counit. Apply [lem-sfb-bounded-bialgebra-top-degree-exterior] over the algebraically closed,
   hence perfect, field $\Omega$: the actual multiplication identifies its coherent cohomology
   with $\bigwedge^*H^1$. By the scheme comparison in [lem-sfb-flat-space-derived-external-cup],
   this is precisely the residue bialgebra of step 3, with the small-etale cup product.

5. For a point $s\in U$, set $R_s=\mathcal O_{U,s}$ and $k_s=\kappa(s)$. The perfect complex
   $K_s=R_s\otimes_R^{\mathbf L}K$ has the bialgebra maps of step 3. Field extension from $k_s$
   to an algebraic closure is faithfully flat; cohomology of a complex of vector spaces and its
   cup maps commute with this extension. Step 4 therefore says already over $k_s$ that the
   product on $H^*(k_s\otimes_{R_s}^{\mathbf L}K_s)$ is exterior on degree one: squares vanish
   after the injective scalar extension, and the kernel and cokernel of each exterior-product
   map become zero. Apply [lem-sfb-perfect-derived-bialgebra-exterior-rigidity] to $K_s$. It has
   a bounded finite free zero-differential model, $H^1(K_s)$ is free, and cup product is
   exterior on it. This is an application to a Noetherian local ring; no smoothness of a
   relative Picard functor is used.

6. The isomorphism at $s$ spreads to a principal neighbourhood. Indeed write $K$ as its bounded
   finite-projective model $P$ and let $E$ be the bounded zero-differential complex of finite
   free $R$-modules with the ranks given by step 5 at $s$. The directed system of rings $R_f$,
   with $f\notin\mathfrak p_s$ and refinements by products, has colimit $R_s$. Apply [lem-pc-
   affine-perfect-hom-colimit] to $P,E$: the two inverse derived isomorphisms over $R_s$ lift to
   some $R_f$, and their two composite equalities lift after a further refinement by the
   injectivity part of that same colimit bijection. Thus $K|_{D(f)}\simeq E|_{D(f)}$, and all
   its cohomology modules are finite free there. Since $s$ was arbitrary, the sheaves
   $R^ia_*\mathcal O_A$ are Zariski finite locally free. By [lem-sfb-space-affine-relative-cup-
   sections](i) for $A_{D(f)}\to D(f)$, the relative cup product on sections over $D(f)$ is the
   cup product of $H^*(A_{D(f)},\mathcal O)$, which is $H^*(K)_f$ with its product by the base-
   change clause of [lem-sfb-flat-space-derived-external-cup] for $R\to R_f$; by part (ii) for
   the open immersions $D(fh)\subseteq D(f)$ these identifications commute with restriction.
   Hence at each Zariski stalk the relative cup product is the product of $H^*(K_s)$, and the
   square-zero identities and exterior-product isomorphisms of step 5 hold at every Zariski
   stalk. So squares of local sections are zero and the canonical wedge maps of relative cup
   products are isomorphisms: their kernels and cokernels have all stalks zero. This establishes
   the exterior algebra assertion over $S$, with $V_S=R^1a_*\mathcal O_A$.

7. For arbitrary $g:T\to S$, [lem-sfb-flat-space-derived-pushforward-base-change] gives the
   canonical isomorphism $Lg^*Ra_*\mathcal O_A\simeq Rf_*\mathcal O_{A_T}$. On each zero-
   differential finite free chart from step 6, $Lg^*$ is ordinary tensor on that model and the
   differentials remain zero for every base map. Thus its degree-$i$ map is precisely
   $g^*R^ia_*\mathcal O_A\xrightarrow{\sim}R^if_*\mathcal O_{A_T}$, including nonflat $g$.
   Product compatibility: for an affine open $\operatorname{Spec}B$ of $T$ mapping into a
   principal open $D(f)$ of $S$, [lem-sfb-space-affine-relative-cup-sections](i),(ii) for
   $\operatorname{Spec}B\to D(f)$ identify the relative cup products with the global ones and
   the base-change map on sections with the pullback $H^i(A_{D(f)},\mathcal O)\to
   H^i(A_B,\mathcal O)$, i.e. with the comparison $B\otimes_{R_f}^{\mathbf L}K_f\to
   R\Gamma(A_B,\mathcal O)$, which respects products by [lem-sfb-flat-space-derived-external-
   cup]. So both sides send $1\otimes(v_1\smile\cdots\smile v_i)$ to the cup of the pulled-back
   classes. These formulas determine the wedge maps and glue. Applied to $T'\to T$, identity and
   composition coherence of the derived comparisons shows that the resulting isomorphisms are
   the canonical higher-direct-image comparisons requested in the statement. No Noetherian or
   reducedness assumption on $T$ or $T'$ entered this tensor calculation.

8. If $T=\operatorname{Spec}R$, use [lem-sfb-space-affine-base-higher-image-sections] with
   $M=\mathcal O_{A_T}$ to identify $H^i(A_T,\mathcal O)$ with $\Gamma(T,R^if_*\mathcal O)$. By
   [lem-trf-scheme-zariski-etale-quasi-coherent-equivalence], the latter sheaf is the etale
   association of its Zariski quasi-coherent module, whose affine associated-module description
   gives $\widetilde{H^i}=R^if_*\mathcal O$. By [lem-pc-finite-flat-affine-sections-projective],
   these sections, in particular $V=H^1$, are finite projective. By [lem-sfb-space-affine-
   relative-cup-sections](i),(ii) these identifications carry the global cup product to the
   relative one and commute with restriction to principal opens. The wedge comparison on
   sections is an isomorphism: localize at a finite principal cover trivializing $V_T$, where it
   sends each ordered basis wedge to the corresponding cup product; these maps agree on
   overlaps. This gives exactly $\bigwedge_R^iV\simeq H^i$, including $H^0=R$. A finite
   trivializing cover of the quasi-compact affine $T$ bounds the local ranks of $V_T$ by some
   finite $N$, so the ordered-wedge bases show $\bigwedge^iV_T=0$ for $i>N$. Hence $H^i=0$ for
   $i>N$. The empty affine scheme (zero ring) and rank zero give the same formulas.
-/
theorem abelian_coherent_exterior_base_change
    {S : Scheme.{u}} [IsLocallyNoetherian S] (A : AlgebraicSpace S)
    (group : CommutativeSpaceGroup A)
    (hA : Poincare.IsAbelianFamily (groupSpaceProjection A)) :
    ∀ T : Over S,
      IsIso (zero (projection A T)) ∧
      (zariskiImage A T 1).IsFiniteLocallyFree ∧
      (∃ (e : SheafOfModules.RingedTensorEdge (corner (schemeSpace T)) (corner (family A T)))
        (he : Presentation (projection A T) e), ExteriorOnCharts (projection A T) e he) ∧
      (∀ (T' : Over S) (g : T' ⟶ T) (X' : AlgebraicSpace S)
        (h : X' ⟶ family A T) (f' : X' ⟶ schemeSpace T')
        (hp : IsPullback h.hom f'.hom (projection A T).hom (groupSchemeMap g).hom),
        IsIso (exchange (projection A T) (groupSchemeMap g) h f'
          (ObjectProperty.hom_ext _ hp.w)) ∧
        ∃ c : ∀ n : ℕ,
            (smallModuleTensorPullback (groupSchemeMap g)).obj (image (projection A T) n) ≅
              image f' n,
          BaseChangeNormalization (projection A T) (groupSchemeMap g) h f'
            (ObjectProperty.hom_ext _ hp.w) c ∧
          BaseChangeProducts (projection A T) (groupSchemeMap g) f' c) ∧
      ∀ (R : Type u) [CommRing R] (a : T.left ≅ Spec (.of R)),
        AffineConclusion A T R a := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentExterior
