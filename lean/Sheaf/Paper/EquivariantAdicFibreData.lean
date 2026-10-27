/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.ContinuousModuleSectionModel
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Equivariant finite quotient and actual adic fibre data

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.4(1), equivariant expansion
(blueprint: def-sfb-equivariant-adic-fibre-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.EquivariantAdicFibre
open ContinuousModule

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The recorded valuation ring with the topology induced by the extension norm.
Source: BS Definition 6.8.1 (blueprint: def-sfb-equivariant-adic-fibre-data). -/
abbrev Integers := Padic.coefficientExtensionIntegers l E

/-- Positive-level finite modules, with their actual quotient transitions and actions.
Indices n denote the exponent n+1. Freeness is expressed over A by the standard A_n^d.
Open stabilizers are joint continuity of the actions on the discrete finite levels.
Source: BS Proposition 6.8.4(1), equivariant expansion, steps 1--2 and 5
(blueprint: def-sfb-equivariant-adic-fibre-data). -/
structure FiniteData (G : Profinite.{u}) [Group G] [IsTopologicalGroup G] where
  rank : ℕ
  tower : ℕᵒᵖ ⥤ ModuleCat.{u} (Integers l E)
  free : ∀ n : ℕ, Nonempty (tower.obj (op n) ≃ₗ[Integers l E]
    (Fin rank → Padic.coefficientExtensionRing l E (n + 1)))
  quotient : ∀ n : ℕ,
    Function.Surjective (tower.map (homOfLE (Nat.le_succ n)).op).hom ∧
    LinearMap.ker (tower.map (homOfLE (Nat.le_succ n)).op).hom =
      Padic.coefficientExtensionIdeal l E (n + 1) •
        (⊤ : Submodule (Integers l E) (tower.obj (op (n + 1))))
  action : ∀ n : ℕ, G →* (tower.obj (op n) ≃ₗ[Integers l E] tower.obj (op n))
  continuous : ∀ (n : ℕ) (v : tower.obj (op n)),
    IsOpen {g : G | action n g v = v}
  equivariant : ∀ (n : ℕ) (g : G) (v : tower.obj (op (n + 1))),
    tower.map (homOfLE (Nat.le_succ n)).op (action (n + 1) g v) =
      action n g (tower.map (homOfLE (Nat.le_succ n)).op v)

variable {l E}

/-- A finite level with its required discrete topology, keeping its original module.
Source: BS Proposition 6.8.4(1) (blueprint: def-sfb-equivariant-adic-fibre-data). -/
abbrev Level {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    (D : FiniteData l E G) (n : ℕ) := D.tower.obj (op n)

/-- Finite-level sections have exactly the discrete topology.
Source: BS Proposition 6.8.4(1) (blueprint: def-sfb-equivariant-adic-fibre-data). -/
instance levelTopology {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    (D : FiniteData l E G) (n : ℕ) : TopologicalSpace (Level D n) := ⊥

/-- Discreteness of the specified finite-level topology.
Source: BS Proposition 6.8.4(1) (blueprint: def-sfb-equivariant-adic-fibre-data). -/
instance levelDiscrete {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    (D : FiniteData l E G) (n : ℕ) : DiscreteTopology (Level D n) :=
  discreteTopology_bot _

/-- The actual compatible-sections module, rather than an unspecified free module.
Source: BS Proposition 6.8.4(1), step 4
(blueprint: def-sfb-equivariant-adic-fibre-data). -/
abbrev Fibre {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    (D : FiniteData l E G) := ModuleCat.sectionsSubmodule D.tower

/-- The inverse-limit topology, induced from the product of discrete levels.
Source: BS Proposition 6.8.4(1), step 4
(blueprint: def-sfb-equivariant-adic-fibre-data). -/
instance fibreTopology {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    (D : FiniteData l E G) : TopologicalSpace (Fibre D) :=
  TopologicalSpace.induced Subtype.val
    (@Pi.topologicalSpace ℕᵒᵖ (fun j ↦ D.tower.obj j) (fun _ ↦ ⊥))

/-- The induced topology makes compatible sections a topological additive group.
Source: BS Proposition 6.8.4(1), step 4
(blueprint: def-sfb-equivariant-adic-fibre-data).
Proof: each discrete factor is a topological additive group; their product is one.
The compatible sections form an additive subgroup, and its topology is the subspace topology. -/
theorem fibre_isTopologicalAddGroup {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    (D : FiniteData l E G) : IsTopologicalAddGroup (Fibre D) := by
  let : ∀ j : ℕᵒᵖ, TopologicalSpace (D.tower.obj j) := fun _ ↦ ⊥
  let : ∀ j : ℕᵒᵖ, DiscreteTopology (D.tower.obj j) :=
    fun _ ↦ discreteTopology_bot _
  exact topologicalAddGroup_induced (ModuleCat.sectionsSubmodule D.tower).subtype

/-- The named construction proof supplies the additive-topology instance.
Source: BS Proposition 6.8.4(1) (blueprint: def-sfb-equivariant-adic-fibre-data). -/
instance fibreTopologicalAdd {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    (D : FiniteData l E G) : IsTopologicalAddGroup (Fibre D) :=
  fibre_isTopologicalAddGroup D

/-- The actual projection to the nth finite level, with exponent n+1.
Source: BS Proposition 6.8.4(1) (blueprint: def-sfb-equivariant-adic-fibre-data). -/
def projection {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    (D : FiniteData l E G) (n : ℕ) : Fibre D →ₗ[Integers l E] Level D n :=
  (LinearMap.proj (op n)).comp (ModuleCat.sectionsSubmodule D.tower).subtype

/-- Multiplication by a constant, on the point's actual continuous coefficient sheaf.
Source: BS Lemma 6.8.2 (blueprint: def-sfb-equivariant-adic-fibre-data). -/
def multiply (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (a : A) :
    (ring A).X ⟶ (ring A).X :=
  ⟨{ app := fun S ↦ AddCommGrpCat.ofHom
      { toFun := fun f ↦ ULift.up (ContinuousMap.const S.unop a * f.down)
        map_zero' := congrArg ULift.up (mul_zero _)
        map_add' := fun f g ↦ congrArg ULift.up (mul_add _ f.down g.down) }
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The actual scalar endomorphism of the underlying abelian sheaf of an internal module.
Source: BS Lemma 6.8.2 (blueprint: def-sfb-equivariant-adic-fibre-data). -/
def scalar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) (a : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    N.X ⟶ N.X :=
  (λ_ N.X).inv ≫
    ((Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map a) ▷ N.X) ≫
    ModObj.smul (M := condensedRingObj Λ X) (X := N.X)


/-- Actual descent, transported by an isomorphism to a continuous section model.
The endomorphism is over the entire parameter scheme X[G]. It runs from the projection
side to the action side, inverse to the canonical deck descent a^*F ≅ pr^*F: at a point
(x,g) it sends the fibre over x to the fibre over g·x. For the left action given by
`ProfiniteCoefficientAction` (h·(g·x) = (hg)·x), only this direction can equal
(x,g,v) ↦ (x,g,g·v) for a group homomorphism g ↦ (v ↦ g·v); the opposite arrow would
force an anti-homomorphism.
Source: BS Proposition 6.8.4(1), step 9
(blueprint: def-sfb-equivariant-adic-fibre-data). -/
def descentEnd
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X B : Scheme.{u}} {G : Profinite.{u}}
    (a : coefficientParameter X G ⟶ X) (u : X ⟶ B)
    (hu : a ≫ u = coefficientParameterProjection X G ≫ u)
    (N : Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B))
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (h : (cartesianCoefficientLift Λ u).obj N ≅ ((upperStarFromPoint X).mapMod Λ).obj M) :
    (((upperStarFromPoint (coefficientParameter X G)).mapMod Λ).obj M).X ⟶
      (((upperStarFromPoint (coefficientParameter X G)).mapMod Λ).obj M).X :=
  (pullIso Λ M (coefficientParameterProjection X G)).inv ≫
    ((cartesianCoefficientLift Λ (coefficientParameterProjection X G)).map h.inv).hom ≫
    (liftUnderlying Λ (coefficientParameterProjection X G)
      ((cartesianCoefficientLift Λ u).obj N)).hom ≫
    (upperStar Ab.{u + 1} (coefficientParameterProjection X G)).map
      (liftUnderlying Λ u N).hom ≫
    (upperStarComp Ab.{u + 1} (coefficientParameterProjection X G) u).inv.app N.X ≫
    (upperStarCongr Ab.{u + 1} hu).inv.app N.X ≫
    (upperStarComp Ab.{u + 1} a u).hom.app N.X ≫
    (upperStar Ab.{u + 1} a).map (liftUnderlying Λ u N).inv ≫
    (liftUnderlying Λ a ((cartesianCoefficientLift Λ u).obj N)).inv ≫
    ((cartesianCoefficientLift Λ a).map h.hom).hom ≫
    (pullIso Λ M a).hom


/-- Equality of the whole parameter-sheaf arrow with the variable-label action.
Source: BS Proposition 6.8.4(1), step 9
(blueprint: def-sfb-equivariant-adic-fibre-data). -/
def SectionAction
    {V : Type u} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    {X : Scheme.{u}} {G : Profinite.{u}}
    (M : Sheaf (Scheme.ProEt.topology (coefficientParameter X G)) Ab.{u + 1})
    (ψ : M.obj ≅ schemeFunctions V (coefficientParameter X G))
    (f : M ⟶ M) (ρ : G → V → V) : Prop :=
  ∀ (U : (coefficientParameter X G).ProEtᵒᵖ) (v : M.obj.obj U) (x : U.unop.left),
    (ψ.hom.app U (f.hom.app U v)).down x =
      ρ (profiniteTestProjection X G (U.unop.hom x)) ((ψ.hom.app U v).down x)

/-- The exact action formula on every section over X[G], including variable group labels.
Source: BS Proposition 6.8.4(1), step 9
(blueprint: def-sfb-equivariant-adic-fibre-data). -/
def HasDescentAction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {V : Type u} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    {X B : Scheme.{u}} {G : Profinite.{u}}
    (a : coefficientParameter X G ⟶ X) (u : X ⟶ B)
    (hu : a ≫ u = coefficientParameterProjection X G ≫ u)
    (N : Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B))
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (ψ : (((upperStarFromPoint (coefficientParameter X G)).mapMod Λ).obj M).X.obj ≅
      schemeFunctions V (coefficientParameter X G))
    (h : (cartesianCoefficientLift Λ u).obj N ≅ ((upperStarFromPoint X).mapMod Λ).obj M)
    (ρ : G → V → V) : Prop :=
  SectionAction (((upperStarFromPoint (coefficientParameter X G)).mapMod Λ).obj M).X
    ψ (descentEnd Λ a u hu N M h) ρ


/-- A lisse module with its actual scalar cokernels and quotient projections.
Source: BS Lemma 6.8.2 and Proposition 6.8.4(1)
(blueprint: def-sfb-equivariant-adic-fibre-data). -/
structure ScalarQuotients (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (B : Scheme.{u}) (s : ℕ → A) where
  module : SchemeModules A B
  lisse : IsLisseCoefficientModule (ring A).X module
  quotient : ℕ → SchemeModules A B
  quotientMap : ∀ n, module ⟶ quotient n
  zero : ∀ n, scalar (ring A).X B (MonObj.one ≫ multiply A (s n)) module ≫
    (quotientMap n).hom = 0
  cokernel : ∀ n, Nonempty (IsColimit (CokernelCofork.ofπ (quotientMap n).hom (zero n)))
  transition : ∀ n, quotient (n + 1) ⟶ quotient n
  transition_projection : ∀ n, quotientMap (n + 1) ≫ transition n = quotientMap n

/-- The given lisse module, its actual scalar quotients, and the prescribed finite charts.
Cokernel universal properties fix the quotient projections; the transition equations
fix the actual successive quotient maps. All finite charts use full continuous sections,
which are precisely the finite constant sheaves for the discrete finite modules.
Source: BS Proposition 6.8.4(1), hypotheses of the equivariant expansion
(blueprint: def-sfb-equivariant-adic-fibre-data). -/
structure Data (B X : Scheme.{u}) (u : X ⟶ B) [WeaklyEtale u]
    (G : Profinite.{u}) [Group G] [IsTopologicalGroup G]
    (a : ProfiniteCoefficientAction X G)
    (hu : a.act ≫ u = coefficientParameterProjection X G ≫ u)
    (D : FiniteData l E G) extends ScalarQuotients (Integers l E) B
      (fun n ↦ Padic.coefficientExtensionUniformizer l E ^ (n + 1)) where
  finiteModel : ∀ n, Model (Integers l E) (Level D n)
  phi : ∀ n, (cartesianCoefficientLift (ring (Integers l E)).X u).obj (quotient n) ≅
    (pull (Integers l E) X).obj (finiteModel n).object
  finiteTransition : ∀ n, (finiteModel (n + 1)).object ⟶ (finiteModel n).object
  finiteTransition_formula : ∀ n, RepresentsMap (finiteModel (n + 1)) (finiteModel n)
    (D.tower.map (homOfLE (Nat.le_succ n)).op).hom (finiteTransition n)
  phi_transition : ∀ n,
    (cartesianCoefficientLift (ring (Integers l E)).X u).map (transition n) ≫ (phi n).hom =
      (phi (n + 1)).hom ≫ (pull (Integers l E) X).map (finiteTransition n)
  phi_action : ∀ n, HasDescentAction (ring (Integers l E)).X a.act u hu (quotient n)
    (finiteModel n).object ((finiteModel n).scheme _) (phi n)
    (fun g v ↦ D.action n g v)


/-- The actual algebraic scalar extension E tensor_A Q, without a completion.
Source: BS Proposition 6.8.4(1), step 5
(blueprint: def-sfb-equivariant-adic-fibre-data). -/
abbrev Rational {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    (D : FiniteData l E G) := E ⊗[Integers l E] Fibre D

/-- The finite-dimensional E-module topology; in a basis it is the norm product topology.
Source: BS Proposition 6.8.4(1), step 5
(blueprint: def-sfb-equivariant-adic-fibre-data). -/
instance rationalTopology {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    (D : FiniteData l E G) : TopologicalSpace (Rational D) := moduleTopology E (Rational D)

/-- The specified scalar-extension topology is the module topology.
Source: BS Proposition 6.8.4(1) (blueprint: def-sfb-equivariant-adic-fibre-data). -/
instance rationalModuleTopology {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    (D : FiniteData l E G) : IsModuleTopology E (Rational D) := ⟨rfl⟩

/-- Topological addition in the scalar-extension topology.
Source: BS Proposition 6.8.4(1) (blueprint: def-sfb-equivariant-adic-fibre-data). -/
instance rationalTopologicalAdd {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    (D : FiniteData l E G) : IsTopologicalAddGroup (Rational D) :=
  IsModuleTopology.topologicalAddGroup E (Rational D)


/-- The actual inclusion of integral into rational coefficients, by postcomposition.
Source: BS Lemma 6.8.2(2) (blueprint: def-sfb-equivariant-adic-fibre-data). -/
def coefficientMap : (ring (Integers l E)).X ⟶ (ring E).X :=
  Profinite.continuousMapRingObjMapOfUniverse
    (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val

/-- The existing postcomposition map preserves the recorded ring operations.
Source: BS Lemma 6.8.2(2) (blueprint: def-sfb-equivariant-adic-fibre-data). -/
instance coefficientMap_mon : IsMonHom (coefficientMap (l := l) (E := E)) :=
  Profinite.isMonHom_continuousMapRingObjMapOfUniverse _ _

/-- The coefficient inclusion after the specified point inverse image.
Source: BS Lemma 6.8.2(2) (blueprint: def-sfb-equivariant-adic-fibre-data). -/
def schemeCoefficientMap (B : Scheme.{u}) :
    condensedRingObj (ring (Integers l E)).X B ⟶ condensedRingObj (ring E).X B :=
  (upperStarFromPoint B).map (coefficientMap (l := l) (E := E))

/-- The pulled-back coefficient inclusion is a ring-object map.
Source: BS Lemma 6.8.2(2) (blueprint: def-sfb-equivariant-adic-fibre-data). -/
instance schemeCoefficientMap_mon (B : Scheme.{u}) :
    IsMonHom (schemeCoefficientMap (l := l) (E := E) B) :=
  inferInstanceAs (IsMonHom ((upperStarFromPoint B).map
    (coefficientMap (l := l) (E := E))))


/-- Ordinary localization along A to E. The maps are the extension-of-scalars unit.
Inverting the uniformizer and inverting ell coincide in this coefficient field.
Source: BS Lemma 6.8.2(2), expansion step 8
(blueprint: def-sfb-equivariant-adic-fibre-data). -/
abbrev localize (B : Scheme.{u}) : SchemeModules (Integers l E) B ⥤ SchemeModules E B :=
  Mod.extendScalars (schemeCoefficientMap (l := l) (E := E) B)

/-- The parameter map for a refinement and a continuous group homomorphism.
Source: BS Proposition 6.8.4(1), step 11
(blueprint: def-sfb-equivariant-adic-fibre-data). -/
def parameterRefinement {X X' : Scheme.{u}} (r : X' ⟶ X)
    {G G' : Profinite.{u}} [Group G] [Group G'] (γ : G' →ₜ* G) :
    coefficientParameter X' G' ⟶ coefficientParameter X G :=
  ((profiniteToProEtOf X').map (CompHausLike.ofHom _ γ.toContinuousMap)).left ≫
    coefficientParameterMap r G

/-- The actual refinement map on abelian inverse images, with both composition comparisons.
Source: BS Proposition 6.8.4(1), steps 10--11
(blueprint: def-sfb-equivariant-adic-fibre-data). -/
def refinementArrow
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {B X X' : Scheme.{u}} {u : X ⟶ B} {u' : X' ⟶ B}
    (r : X' ⟶ X) (hr : r ≫ u = u')
    {N N' : Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B)}
    (f : N ⟶ N') :
    ((cartesianCoefficientLift Λ r).obj ((cartesianCoefficientLift Λ u).obj N)).X ⟶
      ((cartesianCoefficientLift Λ u').obj N').X :=
  (liftUnderlying Λ r _).hom ≫
    (upperStar Ab.{u + 1} r).map (liftUnderlying Λ u N).hom ≫
    (upperStarComp Ab.{u + 1} r u).inv.app N.X ≫
    (upperStarCongr Ab.{u + 1} hr).hom.app N.X ≫
    (upperStar Ab.{u + 1} u').map f.hom ≫ (liftUnderlying Λ u' N').inv

/-- Compatible finite data over a refinement, including the actual finite quotient squares.
Identity refinements are allowed, so this also includes morphisms over the same slice.
Source: BS Proposition 6.8.4(1), steps 10--11
(blueprint: def-sfb-equivariant-adic-fibre-data). -/
structure Morphism {B X X' : Scheme.{u}} {u : X ⟶ B} {u' : X' ⟶ B}
    [WeaklyEtale u] [WeaklyEtale u']
    {G G' : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    [Group G'] [IsTopologicalGroup G']
    {a : ProfiniteCoefficientAction X G} {a' : ProfiniteCoefficientAction X' G'}
    {hu : a.act ≫ u = coefficientParameterProjection X G ≫ u}
    {hu' : a'.act ≫ u' = coefficientParameterProjection X' G' ≫ u'}
    {D : FiniteData l E G} {D' : FiniteData l E G'}
    (P : Data B X u G a hu D) (P' : Data B X' u' G' a' hu' D')
    (r : X' ⟶ X) [WeaklyEtale r] (hr : r ≫ u = u') (γ : G' →ₜ* G) where
  equivariant_scheme : a'.act ≫ r = parameterRefinement r γ ≫ a.act
  moduleMap : P.module ⟶ P'.module
  finiteMap : ∀ n, Level D n →ₗ[Integers l E] Level D' n
  finiteMap_transition : ∀ (n : ℕ) (v : Level D (n + 1)),
    finiteMap n (D.tower.map (homOfLE (Nat.le_succ n)).op v) =
      D'.tower.map (homOfLE (Nat.le_succ n)).op (finiteMap (n + 1) v)
  finiteMap_equivariant : ∀ (n : ℕ) (g : G') (v : Level D n),
    finiteMap n (D.action n (γ g) v) = D'.action n g (finiteMap n v)
  finiteSheafMap : ∀ n, (P.finiteModel n).object ⟶ (P'.finiteModel n).object
  finiteSheafMap_formula : ∀ n, RepresentsMap (P.finiteModel n) (P'.finiteModel n)
    (finiteMap n) (finiteSheafMap n)
  finite_square : ∀ n,
    ((cartesianCoefficientLift (ring (Integers l E)).X r).map
      ((cartesianCoefficientLift (ring (Integers l E)).X u).map (P.quotientMap n) ≫
        (P.phi n).hom)).hom ≫
      (pullIso (ring (Integers l E)).X (P.finiteModel n).object r).hom ≫
      ((pull (Integers l E) X').map (finiteSheafMap n)).hom =
    refinementArrow (ring (Integers l E)).X r hr moduleMap ≫
      ((cartesianCoefficientLift (ring (Integers l E)).X u').map (P'.quotientMap n) ≫
        (P'.phi n).hom).hom



end AlgebraicGeometry.ProEtale.EquivariantAdicFibre
