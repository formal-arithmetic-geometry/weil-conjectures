module

public import Sheaf.AlgebraicGeometry.EquivariantCoherentGroups
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.LocalUniformHigherDirectImageBound
import Sheaf.AlgebraicGeometry.NoetherianProperBoundedCoherentImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.ExactDerivedCohomologyCoherence
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Sheaf.AlgebraicGeometry.DerivedBaseChangeVerticalPasting
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.FinitePostnikovIsomorphism
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Proper pushforward in equivariant coherent Grothendieck groups

Source: Milne, Algebraic Groups, Section 22d, Theorem 22.50, supporting proper
pushforward construction; Stacks Tags 02O5, 02O6, 02KH, 0ATL, 0ATM and 08HY.
(blueprint: lem-sfb-equivariant-coherent-proper-pushforward)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.EquivariantCoherent

open ProperPushforwardData


variable (k : Type u) [Field k]

/-- The canonical identification of a flat derived pullback with the termwise exact
pullback, using the same left-derived counit as `schemeDerivedBaseChangeMap`.
Source: Stacks 015F, 08HY
(blueprint: lem-sfb-equivariant-coherent-proper-pushforward). -/
def exactPullbackComparison
    [d : ∀ S : Scheme.{u}, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [(Scheme.Modules.tensorPullback g).Additive]
    [PreservesFiniteLimits (Scheme.Modules.tensorPullback g)]
    [PreservesFiniteColimits (Scheme.Modules.tensorPullback g)] :
    @derivedPullback X Y g (d Y) (d X) ≅
      @Functor.mapDerivedCategory
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ (d Y)
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _ _ (d X)
        (Scheme.Modules.tensorPullback g) _ _ _ := by
  let F : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := Scheme.Modules.tensorPullback g
  let ε := (Classical.choose (Classical.choose_spec
    (@exists_derivedPullbackComposition.{u, u + 1} d))) g
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  have : (derivedPullback g).IsLeftDerivedFunctor ε W :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec (@exists_derivedPullbackComposition.{u, u + 1} d)))) g
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh
  exact Functor.leftDerivedUnique F.mapDerivedCategory (derivedPullback g) ε
    F.mapDerivedCategoryFactorsh.hom W



/-- Higher-image exchange is the cohomology of the canonical derived base-change map.
Its source uses the normalized exact-pullback cohomology comparison of
`def-sfb-exact-derived-cohomology-comparison`; its target uses the normalized single
comparison. No map or cohomology identification is selected arbitrarily.
Source: Stacks 015F, 02N7, 08HY
(blueprint: lem-sfb-equivariant-coherent-proper-pushforward). -/
def higherBaseChange
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (h : g' ≫ f = f' ≫ g)
    (eg : PreservesFiniteLimits (Scheme.Modules.tensorPullback g) ∧
      PreservesFiniteColimits (Scheme.Modules.tensorPullback g))
    (eg' : PreservesFiniteLimits (Scheme.Modules.tensorPullback g') ∧
      PreservesFiniteColimits (Scheme.Modules.tensorPullback g'))
    (q : ℕ) (M : X.Modules) :
    (Scheme.Modules.tensorPullback g).obj
        ((@schemeModuleHigherDirectImage X Y (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) f (q : ℤ)).obj M) ⟶
      (@schemeModuleHigherDirectImage X' Y' (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) f' (q : ℤ)).obj
          ((Scheme.Modules.tensorPullback g').obj M) := by
  letI := fun S : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings S.toRingedSpace))
  letI := eg.1
  letI := eg.2
  letI := eg'.1
  letI := eg'.2
  letI := (Classical.choose exists_derivedPullbackComposition) g
  letI := (Classical.choose exists_derivedPullbackComposition) g'
  let E := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
  let K := (schemeDerivedDirectImage f).obj E
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings Y'.toRingedSpace)) (q : ℤ)
  let F : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y'.toRingedSpace) := Scheme.Modules.tensorPullback g
  let F' : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X'.toRingedSpace) := Scheme.Modules.tensorPullback g'
  let θ := (F.mapDerivedCategoryHomologyFunctorIso
    (q : ℤ)).app K
  let c := (exactPullbackComparison g).app K
  let s := (exactPullbackComparison g').app E ≪≫
    (F'.mapDerivedCategorySingleFunctor 0).app M
  exact θ.hom ≫ H.map c.inv ≫ H.map (schemeDerivedBaseChangeMap f f' g g' h E) ≫
    H.map ((schemeDerivedDirectImage f').map s.hom)



set_option maxHeartbeats 800000 in
-- Product-square maps require unifying the shared higher-image localization instances.
/-- All degrees of the output action are fixed by the canonical projection and action
exchanges, not merely by naturality in the coherent module. Exactness witnesses are
proofs, supplied by flatness of both product projections and action morphisms.
The equation is theta_out ; beta_a = beta_p ; R^q f_G(theta_in), after transport.
Source: Stacks 02N7, 08HY, 015F
(blueprint: lem-sfb-equivariant-coherent-proper-pushforward). -/
def IsHigherPushforward {G : ProperPushforwardData.Group k} {X Y : Space k G} (f : ProperMap k X Y)
    (q : ℕ) {DX : ActionGroupoidModel G.scheme X.scheme}
    {DY : ActionGroupoidModel G.scheme Y.scheme} (M : Coherent DX) (N : Coherent DY)
    (e : underlying N ≅
      (higher k (G := G) (X := X) (Y := Y) f.map q).obj (underlying M)) : Prop :=
  ∀ (ha : target G.scheme X.scheme ≫ f.map.left =
        (lift (fst G.scheme X.scheme) (snd G.scheme X.scheme ≫ f.map)).left ≫
          target G.scheme Y.scheme)
    (hp : source G.scheme X.scheme ≫ f.map.left =
        (lift (fst G.scheme X.scheme) (snd G.scheme X.scheme ≫ f.map)).left ≫
          source G.scheme Y.scheme)
    (eaY : PreservesFiniteLimits (Scheme.Modules.tensorPullback
        (target G.scheme Y.scheme)) ∧
      PreservesFiniteColimits (Scheme.Modules.tensorPullback
        (target G.scheme Y.scheme)))
    (epY : PreservesFiniteLimits (Scheme.Modules.tensorPullback
        (source G.scheme Y.scheme)) ∧
      PreservesFiniteColimits (Scheme.Modules.tensorPullback (source G.scheme Y.scheme)))
    (eaX : PreservesFiniteLimits (Scheme.Modules.tensorPullback
        (target G.scheme X.scheme)) ∧
      PreservesFiniteColimits (Scheme.Modules.tensorPullback
        (target G.scheme X.scheme)))
    (epX : PreservesFiniteLimits (Scheme.Modules.tensorPullback
        (source G.scheme X.scheme)) ∧
      PreservesFiniteColimits (Scheme.Modules.tensorPullback (source G.scheme X.scheme))),
    (actionIso k (G := G) (X := Y) N).hom ≫
      (Scheme.Modules.tensorPullback
        (target G.scheme Y.scheme)).map e.hom ≫
      higherBaseChange f.map.left
        (lift (fst G.scheme X.scheme) (snd G.scheme X.scheme ≫ f.map)).left
        (target G.scheme Y.scheme)
        (target G.scheme X.scheme) ha eaY eaX q (underlying M) =
    (Scheme.Modules.tensorPullback (source G.scheme Y.scheme)).map e.hom ≫
      higherBaseChange f.map.left
        (lift (fst G.scheme X.scheme) (snd G.scheme X.scheme ≫ f.map)).left
        (source G.scheme Y.scheme) (source G.scheme X.scheme) hp epY epX q (underlying M) ≫
      (@schemeModuleHigherDirectImage (G.scheme ⊗ X.scheme).left
        (G.scheme ⊗ Y.scheme).left (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _)
        (lift (fst G.scheme X.scheme) (snd G.scheme X.scheme ≫ f.map)).left (q : ℤ)).map
        (actionIso k (G := G) (X := X) M).hom



/-- The ordinary pushforward action is pinned by the two ordinary base-change maps.
The equation is theta_out ; beta_a = beta_p ; f_G*(theta_in), written
without choosing an inverse. Square equalities are merely transport proofs.
Source: Stacks 02N7, 08HY (blueprint: lem-sfb-equivariant-coherent-proper-pushforward). -/
def IsOrdinaryPushforward {G : ProperPushforwardData.Group k} {X Y : Space k G}
    (f : ProperMap k X Y)
    {DX : ActionGroupoidModel G.scheme X.scheme}
    {DY : ActionGroupoidModel G.scheme Y.scheme} (M : Coherent DX) (N : Coherent DY)
    (e : (underlying N) ≅ (Scheme.Modules.pushforward f.map.left).obj (underlying M)) : Prop :=
  ∀ (ha : target G.scheme X.scheme ≫ f.map.left =
        (lift (fst G.scheme X.scheme) (snd G.scheme X.scheme ≫ f.map)).left ≫
          target G.scheme Y.scheme)
    (hp : source G.scheme X.scheme ≫ f.map.left =
        (lift (fst G.scheme X.scheme) (snd G.scheme X.scheme ≫ f.map)).left ≫
          source G.scheme Y.scheme),
    (actionIso k (G := G) (X := Y) N).hom ≫
      (Scheme.Modules.tensorPullback
        (target G.scheme Y.scheme)).map e.hom ≫
      Scheme.Modules.moduleBaseChangeMap f.map.left
        (lift (fst G.scheme X.scheme) (snd G.scheme X.scheme ≫ f.map)).left
        (target G.scheme Y.scheme)
        (target G.scheme X.scheme) ha (underlying M) =
    (Scheme.Modules.tensorPullback (source G.scheme Y.scheme)).map e.hom ≫
      Scheme.Modules.moduleBaseChangeMap f.map.left
        (lift (fst G.scheme X.scheme) (snd G.scheme X.scheme ≫ f.map)).left
        (source G.scheme Y.scheme) (source G.scheme X.scheme) hp (underlying M) ≫
      (Scheme.Modules.pushforward
        (lift (fst G.scheme X.scheme) (snd G.scheme X.scheme ≫ f.map)).left).map
        (actionIso k (G := G) (X := X) M).hom


/-- All the structures and compatibilities in equivariant proper pushforward. Ring and
module structures are theorem witnesses, pinned to actual tensor coactions and sheaf tensors;
no definition selects an arbitrary ring, module structure, sheaf, or pushforward map.
Source: Milne 22d, Stacks 02O5, 02O6, 02KH
(blueprint: lem-sfb-equivariant-coherent-proper-pushforward). -/
structure ProperPushforwardSystem where
  model : ∀ (G : ProperPushforwardData.Group k) (X : Space k G),
    ActionGroupoidModel G.scheme X.scheme
  pointEquivalence : ∀ G : ProperPushforwardData.Group k,
    GZero (model G (point k G)) ≃+ RepresentationGZero k Γ(G.scheme.left, ⊤)
  point_class : ∀ G : ProperPushforwardData.Group k,
    IsPointEquivalence k G (model G (point k G)) (pointEquivalence G)
  representationRing : ∀ G : ProperPushforwardData.Group k,
    CommRing (RepresentationGZero k Γ(G.scheme.left, ⊤))
  representationRing_spec : ∀ G : ProperPushforwardData.Group k,
    IsRepresentationRing (representationRing G)
  moduleAction : ∀ (G : ProperPushforwardData.Group k) (X : Space k G),
    @Module (RepresentationGZero k Γ(G.scheme.left, ⊤)) (GZero (model G X))
      (representationRing G).toSemiring inferInstance
  moduleAction_spec : ∀ (G : ProperPushforwardData.Group k) (X : FiniteSpace k G),
    IsRepresentationAction k (model G X.space) (representationRing G)
      (moduleAction G X.space)
  tensor_class : ∀ (G : ProperPushforwardData.Group k) (X : Space k G)
    (V : Representation k G.scheme)
    (M : Coherent (model G X)),
    ∃ (P : Coherent (model G X)) (n : ℕ) (b : Module.Basis (Fin n) k V.space)
      (e : (∐ fun _ : Fin n ↦ underlying M) ≅ underlying P),
      (moduleAction G X).smul (representationClass V) (classOf M) = classOf P ∧
      ∀ j : Fin n,
        (Scheme.Modules.tensorPullback (source G.scheme X.scheme)).map
            (Sigma.ι (fun _ : Fin n ↦ underlying M) j ≫ e.hom) ≫
            (actionIso k (G := G) (X := X) P).hom =
          ∑ i : Fin n, (actionIso k (G := G) (X := X) M).hom ≫
            (Scheme.Modules.tensorPullback (target G.scheme X.scheme)).map
              (Sigma.ι (fun _ : Fin n ↦ underlying M) i ≫ e.hom) ≫
            ((Scheme.Modules.tensorPullback (target G.scheme X.scheme)).obj
              (underlying P)).smulHom
                ((fst G.scheme X.scheme).left.appTop
                  ((TensorProduct.lid k Γ(G.scheme.left, ⊤))
                    (((b.coord i).rTensor Γ(G.scheme.left, ⊤)) (V.coaction (b j)))))
  image : ∀ (G : ProperPushforwardData.Group k) (X Y : FiniteSpace k G)
    (_f : ProperMap k X.space Y.space)
    (_q : ℕ) (_M : Coherent (model G X.space)), Coherent (model G Y.space)
  imageComparison : ∀ (G : ProperPushforwardData.Group k) (X Y : FiniteSpace k G)
    (f : ProperMap k X.space Y.space) (q : ℕ) (M : Coherent (model G X.space)),
    underlying (image G X Y f q M) ≅
      (higher k (G := G) (X := X.space) (Y := Y.space) f.map q).obj (underlying M)
  pullbackExact : ∀ (G : ProperPushforwardData.Group k) (X : Space k G),
    (PreservesFiniteLimits (Scheme.Modules.tensorPullback (source G.scheme X.scheme)) ∧
      PreservesFiniteColimits (Scheme.Modules.tensorPullback (source G.scheme X.scheme))) ∧
    (PreservesFiniteLimits (Scheme.Modules.tensorPullback
        (target G.scheme X.scheme)) ∧
      PreservesFiniteColimits (Scheme.Modules.tensorPullback
        (target G.scheme X.scheme)))
  imageAction : ∀ (G : ProperPushforwardData.Group k) (X Y : FiniteSpace k G)
    (f : ProperMap k X.space Y.space) (q : ℕ) (M : Coherent (model G X.space)),
    IsHigherPushforward k f q M (image G X Y f q M) (imageComparison G X Y f q M)
  naturality : ∀ (G : ProperPushforwardData.Group k) (X Y : FiniteSpace k G)
    (f : ProperMap k X.space Y.space) (q : ℕ) (M N : Coherent (model G X.space))
    (a : M ⟶ N), ∃ b : image G X Y f q M ⟶ image G X Y f q N,
      underlyingMap b = (imageComparison G X Y f q M).hom ≫
        (higher k (G := G) (X := X.space) (Y := Y.space) f.map q).map (underlyingMap a) ≫
          (imageComparison G X Y f q N).inv
  vanishing : ∀ (G : ProperPushforwardData.Group k) (X Y : FiniteSpace k G)
    (f : ProperMap k X.space Y.space) (M : Coherent (model G X.space)),
    ∃ n : ℕ, ∀ q : ℕ, n < q → IsZero (underlying (image G X Y f q M))
  ordinary : ∀ (G : ProperPushforwardData.Group k) (X Y : FiniteSpace k G)
    (f : ProperMap k X.space Y.space) (M : Coherent (model G X.space)),
    underlying (image G X Y f 0 M) ≅
      (Scheme.Modules.pushforward f.map.left).obj (underlying M)
  ordinaryAction : ∀ (G : ProperPushforwardData.Group k) (X Y : FiniteSpace k G)
    (f : ProperMap k X.space Y.space) (M : Coherent (model G X.space)),
    IsOrdinaryPushforward k f M (image G X Y f 0 M) (ordinary G X Y f M)
  push : ∀ (G : ProperPushforwardData.Group k) (X Y : FiniteSpace k G)
    (_f : ProperMap k X.space Y.space),
    GZero (model G X.space) →+ GZero (model G Y.space)
  euler : ∀ (G : ProperPushforwardData.Group k) (X Y : FiniteSpace k G)
    (f : ProperMap k X.space Y.space) (M : Coherent (model G X.space)) (n : ℕ),
    (∀ q : ℕ, n < q → IsZero (underlying (image G X Y f q M))) →
    push G X Y f (classOf M) =
      ∑ q ∈ Finset.range (n + 1), (-1 : ℤ) ^ q • classOf (image G X Y f q M)
  linearity : ∀ (G : ProperPushforwardData.Group k) (X Y : FiniteSpace k G)
    (f : ProperMap k X.space Y.space) (r : RepresentationGZero k Γ(G.scheme.left, ⊤))
    (z : GZero (model G X.space)),
    push G X Y f ((moduleAction G X.space).smul r z) =
      (moduleAction G Y.space).smul r (push G X Y f z)
  composition : ∀ (G : ProperPushforwardData.Group k) (X Y Z : FiniteSpace k G)
    (f : ProperMap k X.space Y.space) (g : ProperMap k Y.space Z.space)
    (h : ProperMap k X.space Z.space), h.map = f.map ≫ g.map →
    ∀ z : GZero (model G X.space), push G X Z h z = push G Y Z g (push G X Y f z)
  closedImmersion : ∀ (G : ProperPushforwardData.Group k) (X Y : FiniteSpace k G)
    (f : ProperMap k X.space Y.space), IsClosedImmersion f.map.left →
    ∀ M : Coherent (model G X.space),
      push G X Y f (classOf M) = classOf (image G X Y f 0 M)
  cohomology : ∀ (G : ProperPushforwardData.Group k) (X : FiniteSpace k G)
    (f : ProperMap k X.space (point k G)) (M : Coherent (model G X.space)),
    ∃ (V : ℕ → Representation k G.scheme) (n : ℕ),
      (∀ q : ℕ, Nonempty ((V q).space ≅ cohomologyVector k (G := G) (X := X.space) M q)) ∧
      (∀ q : ℕ, IsAssociated k (V q) (image G X (finitePoint k G) f q M)) ∧
      (∀ q : ℕ, n < q → Subsingleton (V q).space) ∧
      pointEquivalence G (push G X (finitePoint k G) f (classOf M)) =
        ∑ q ∈ Finset.range (n + 1), (-1 : ℤ) ^ q • representationClass (V q)
  restricted : ∀ (G : ProperPushforwardData.Group k) (H : ClosedSubgroup k G) (X : Space k G),
    RestrictedSpace k H X
  restrictedObject : ∀ (G : ProperPushforwardData.Group k) (H : ClosedSubgroup k G) (X : Space k G)
    (_M : Coherent (model G X)), Coherent (model H.group ((restricted G H X).space k))
  restrictionAction : ∀ (G : ProperPushforwardData.Group k) (H : ClosedSubgroup k G) (X : Space k G)
    (M : Coherent (model G X)), IsRestriction k (restricted G H X) M
      (model H.group ((restricted G H X).space k)) (restrictedObject G H X M)
  restrict : ∀ (G : ProperPushforwardData.Group k) (H : ClosedSubgroup k G) (X : Space k G),
    GZero (model G X) →+ GZero (model H.group ((restricted G H X).space k))
  restrict_class : ∀ (G : ProperPushforwardData.Group k) (H : ClosedSubgroup k G) (X : Space k G)
    (M : Coherent (model G X)), restrict G H X (classOf M) =
      classOf (restrictedObject G H X M)
  restrictedMap : ∀ (G : ProperPushforwardData.Group k) (H : ClosedSubgroup k G)
    (X Y : FiniteSpace k G)
    (_f : ProperMap k X.space Y.space),
    ProperMap k ((restricted G H X.space).space k) ((restricted G H Y.space).space k)
  restrictedMap_eq : ∀ (G : ProperPushforwardData.Group k) (H : ClosedSubgroup k G)
    (X Y : FiniteSpace k G)
    (f : ProperMap k X.space Y.space), (restrictedMap G H X Y f).map = f.map
  restriction_push : ∀ (G : ProperPushforwardData.Group k) (H : ClosedSubgroup k G)
    (X Y : FiniteSpace k G)
    (f : ProperMap k X.space Y.space) (z : GZero (model G X.space)),
    restrict G H Y.space (push G X Y f z) =
      push H.group ((restricted G H X.space).finiteSpace k)
        ((restricted G H Y.space).finiteSpace k) (restrictedMap G H X Y f)
        (restrict G H X.space z)


/-- Proper equivariant pushforward, including the representation-ring action,
composition, closed-subgroup restriction, rational cohomology and closed immersions.
Source: Milne 22d supporting construction; Stacks 02O5, 02O6, 02KH, 08HY, 0ATL, 0ATM
(blueprint: lem-sfb-equivariant-coherent-proper-pushforward).

Proof:
1. Finite-type schemes over k are Noetherian (lem-weil-pbc-finite-type-over-noetherian).
   Coherent higher direct images are coherent and eventually zero (lem-pc-coherent-hi,
   lem-pc-local-uniform-higher-direct-image-bound).
2. The projection and action squares are cartesian and flat. The action square is
   conjugate to projection by (g,x) mapping to (g,gx), with inverse using g inverse.
3. Construct their derived exchange by the unit/composition mate
   (def-pc-derived-base-change-map). Flat base change (lem-pc-flat-base-change-cohom)
   and finite Postnikov induction (lem-weil-pbc-finite-postnikov-isomorphism) make it
   invertible on bounded quasi-coherent complexes.
4. Define the output action as inverse(beta_a) composed with Rf_G(theta) and beta_p.
   Mate pasting (lem-weil-pbc-mate-pasting) and the input identity and cocycle give
   the output identity and cocycle on the whole product schemes.
5. Take cohomology using exact flat pullbacks and the normalized comparisons
   (lem-pur-exact-derived-cohomology-coherence). The long exact sequence is equivariant,
   including its boundary maps (lem-sf-derived-homology-long-exact); coherent kernels
   and cokernels exist (lem-weil-pbc-coherent-kernel-cokernel-locnoeth).
6. In a finite exact sequence write each term as its incoming image plus outgoing
   image in G0; alternating image classes cancel. This proves additivity of Euler
   classes and descent to the presented groups. Tensor is exact in both variables.
7. A basis of a finite rational module makes tensor a finite direct sum. The universal
   regular action matrix commutes with higher direct images; thus push is R(G)-linear.
8. Apply Rg to the finite canonical truncation triangles of Rf(M). Euler cancellation
   telescopes (lem-pc-noetherian-proper-bounded-coherent-image,
   lem-pod-texact-truncation-triangle-comparison, lem-weil-pbc-truncation-triangle).
9. The derived composition isomorphism is equivariant by vertical exchange pasting
   (lem-sfb-derived-base-change-vertical-pasting). Step 8 then gives composition of push.
10. Pull the action formula back along a closed subgroup and paste the exchanges.
    Both outer projection/action maps remain flat, even for nonreduced subgroups.
    Top-cohomology comparison (lem-weil-pbc-derived-pullback-top-cohomology) descends
    the derived identity to ordinary higher images, so restriction commutes with push.
11. Over Spec k the universal group element gives the counital coassociative rational
    coaction (lem-sfb-linearized-qcoherent-cohomology-coaction). Coherence makes the
    cohomology finite-dimensional. The affine module dictionary identifies G0 with R(G).
12. A closed immersion is affine (lem-weil-pbc-closed-immersion-integral-separated-uc);
    positive higher images vanish (lem-pc-affine-morphism-hi). The remaining ordinary
    pushforward has sections M(f inverse U) and is the usual extension by zero.
-/
theorem equivariant_coherent_proper_pushforward : Nonempty (ProperPushforwardSystem k) := by
  sorry

end AlgebraicGeometry.EquivariantCoherent
