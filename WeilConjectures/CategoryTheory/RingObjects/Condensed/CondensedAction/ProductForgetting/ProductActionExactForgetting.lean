/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.CondensedActionModule
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.InternalBar.CondensedInternalBarResolution
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Topology.Algebra.MulAction
import WeilConjectures.CategoryTheory.InternalActionSite.SheafActionGrothendieckInflation
import WeilConjectures.CategoryTheory.InternalActionSite.SheafProductFixedAdjunction
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing

/-! # Exact induction and conservative forgetting of a commuting profinite action

Source: blueprint, direct-image stability proof, paragraph (3), agent-extracted
relative cyclic calculation; Stacks Tags 03DI, 03EV, 0GMW, 015Z, 015F and 05RT.
The combined external reference is WANTED in the extracted DAG source.
(blueprint: lem-sfb-product-action-exact-forgetting).

The specification keeps the existing internal action categories and free-module adjunction.
The free object, its generators, the tensor product and extension by zero are actual
constructions. Existence below supplies normalized induction data, never an arbitrary map.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace Profinite.CondensedAction.ProductForgetting

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

variable (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

variable (J : Type u) [TopologicalSpace J] [Group J] [IsTopologicalGroup J]

variable (P : Type u) [TopologicalSpace P] [Group P] [IsTopologicalGroup P]

end Profinite.CondensedAction.ProductForgetting

namespace Profinite.CondensedAction.ProductForgetting

/-- The existing reconstructed sheaf of section rings.
Source: paragraph (3), internal-to-sectionwise identification
(blueprint: lem-sfb-product-action-exact-forgetting). -/
abbrev ringSheaf :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ CommRingCat RingCat)).obj
    (InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) R.X)

/-- The actual free internal module on the represented profinite object G.
Source: paragraph (3), free induction, and the recorded free-module adjunction
(blueprint: lem-sfb-product-action-exact-forgetting). -/
def freeGroup : Modules R :=
  (InternalBar.free R).obj
    (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj (Profinite.of G))

/-- Its canonical local generator, from the unit of the existing free adjunction.
Source: paragraph (3), the symbols [g]
(blueprint: lem-sfb-product-action-exact-forgetting). -/
def generator (S : Profinite.{u}) (g : C(S, G)) : sectionModule R (freeGroup R G) S :=
  (((InternalBar.freeAdjunction R).unit.app
    (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj
      (Profinite.of G))).hom.app (op S)) (ULift.up (CompHausLike.ofHom _ g))

/-- The literal extension-by-zero sheaf j_(G)! R_G.
Source: Stacks Tag 03DI, with module sheafification
(blueprint: lem-sfb-product-action-exact-forgetting). -/
def extendedUnit : SheafOfModules.{u + 1} (ringSheaf R) :=
  (PresheafOfModules.sheafification.{u + 1} (𝟙 (ringSheaf R).obj)).obj
    ((SheafOfModules.extensionByZeroPresheaf.{u + 1, u, u + 1, u + 1}
      (ringSheaf R) (Profinite.of G)).obj
      (SheafOfModules.unit ((ringSheaf R).over (Profinite.of G))))

/-- The canonical [g] section in the extension-by-zero model.
Source: Stacks Tag 03DI, direct-sum injection followed by sheafification
(blueprint: lem-sfb-product-action-exact-forgetting). -/
def extendedGenerator (S : Profinite.{u}) (g : C(S, G)) :
    (extendedUnit R G).val.obj (op S) := by
  classical
  exact ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 (ringSheaf R).obj)).unit.app
      ((SheafOfModules.extensionByZeroPresheaf.{u + 1, u, u + 1, u + 1}
      (ringSheaf R) (Profinite.of G)).obj
        (SheafOfModules.unit ((ringSheaf R).over (Profinite.of G))))).app (op S)
    (DirectSum.of (fun _ : S ⟶ Profinite.of G ↦ (ringSheaf R).obj.obj (op S))
      (CompHausLike.ofHom _ g) 1)

/-- Forget only the first action, by the specified inclusion j ↦ (1,j).
Source: paragraph (3), U_J (blueprint: lem-sfb-product-action-exact-forgetting). -/
def forgetFirst : ActionModule R (G × J) ⥤ ActionModule R J :=
  inflate (ContinuousMonoidHom.inr G J)

/-- The full induction specification. The natural isomorphism fixes the underlying
functor to the actual free-module tensor functor. Local generator formulas fix the
action, the morphisms and both adjunction directions.
Source: paragraph (3), induction formula and its normalized adjunction
(blueprint: lem-sfb-product-action-exact-forgetting). -/
structure Induction where
  /-- The induction functor. -/
  functor : ActionModule R J ⥤ ActionModule R (G × J)
  /-- Underlying induction is R[G] tensor the underlying module. -/
  tensorIso : functor ⋙ forgetAction ≅
    forgetAction ⋙ tensorLeft (freeGroup R G)
  /-- Induction is additive. -/
  additive : functor.Additive
  /-- Left exactness of induction. -/
  finiteLimits : PreservesFiniteLimits functor
  /-- Right exactness of induction. -/
  finiteColimits : PreservesFiniteColimits functor
  /-- The actual action of both factors, on all local pure tensors. -/
  action (M : ActionModule R J) (S : Profinite.{u}) (a g : C(S, G))
      (j : C(S, J)) (m : sectionModule R M.module S) :
    InternalBar.onSections R (tensorIso.hom.app M) S
      ((functor.obj M).act S (a.prodMk j)
        (InternalBar.onSections R (tensorIso.inv.app M) S
          (InternalBar.pureTensor R _ _ S (generator R G S g) m))) =
      InternalBar.pureTensor R _ _ S (generator R G S (a * g)) (M.act S j m)
  /-- The left adjunction is to the specified forgetting functor. -/
  adjunction : functor ⊣ forgetFirst R G J
  /-- Forward transpose evaluates at [1] tensor m. -/
  transpose (M : ActionModule R J) (N : ActionModule R (G × J))
      (f : functor.obj M ⟶ N) (S : Profinite.{u}) (m : sectionModule R M.module S) :
    InternalBar.onSections R (adjunction.homEquiv M N f).val S m =
      InternalBar.onSections R f.val S
        (InternalBar.onSections R (tensorIso.inv.app M) S
          (InternalBar.pureTensor R _ _ S (generator R G S 1) m))
  /-- Inverse transpose sends [g] tensor m to g acting on f(m). -/
  untranspose (M : ActionModule R J) (N : ActionModule R (G × J))
      (f : M ⟶ (forgetFirst R G J).obj N) (S : Profinite.{u})
      (g : C(S, G)) (m : sectionModule R M.module S) :
    InternalBar.onSections R ((adjunction.homEquiv M N).symm f).val S
        (InternalBar.onSections R (tensorIso.inv.app M) S
          (InternalBar.pureTensor R _ _ S (generator R G S g) m)) =
      N.act S ((ContinuousMonoidHom.inl G J).toContinuousMap.comp g)
        (InternalBar.onSections R f.val S m)

/-- The nonequivariant induction, with actual tensor underlying functor and both
normalized transposes; the action translates only the free generators.
Source: paragraph (3), F_(G,1) left adjoint to U_0
(blueprint: lem-sfb-product-action-exact-forgetting). -/
structure PlainInduction where
  /-- The induction functor without a retained action. -/
  functor : Modules R ⥤ ActionModule R G
  /-- Underlying induction is the actual tensor functor. -/
  tensorIso : functor ⋙ forgetAction ≅ tensorLeft (freeGroup R G)
  /-- Additivity of induction. -/
  additive : functor.Additive
  /-- Left exactness of induction. -/
  finiteLimits : PreservesFiniteLimits functor
  /-- Right exactness of induction. -/
  finiteColimits : PreservesFiniteColimits functor
  /-- Translation on generators and no action on the module factor. -/
  action (M : Modules R) (S : Profinite.{u}) (a g : C(S, G))
      (m : sectionModule R M S) :
    InternalBar.onSections R (tensorIso.hom.app M) S
      ((functor.obj M).act S a
        (InternalBar.onSections R (tensorIso.inv.app M) S
          (InternalBar.pureTensor R _ _ S (generator R G S g) m))) =
      InternalBar.pureTensor R _ _ S (generator R G S (a * g)) m
  /-- The nonequivariant adjunction. -/
  adjunction : functor ⊣ forgetAction
  /-- Evaluation at the identity generator. -/
  transpose (M : Modules R) (N : ActionModule R G) (f : functor.obj M ⟶ N)
      (S : Profinite.{u}) (m : sectionModule R M S) :
    InternalBar.onSections R (adjunction.homEquiv M N f) S m =
      InternalBar.onSections R f.val S
        (InternalBar.onSections R (tensorIso.inv.app M) S
          (InternalBar.pureTensor R _ _ S (generator R G S 1) m))
  /-- Extension by the action of the local parameter. -/
  untranspose (M : Modules R) (N : ActionModule R G) (f : M ⟶ N.module)
      (S : Profinite.{u}) (g : C(S, G)) (m : sectionModule R M S) :
    InternalBar.onSections R ((adjunction.homEquiv M N).symm f).val S
        (InternalBar.onSections R (tensorIso.inv.app M) S
          (InternalBar.pureTensor R _ _ S (generator R G S g) m)) =
      N.act S g (InternalBar.onSections R f S m)

/-- Exact conservative forgetting, on modules and on full ordinary unbounded derived
categories. The resolution clause retains the actual termwise map, every lower bound
and injectivity in every degree.
Source: paragraph (3), forgetting and bounded-below resolutions
(blueprint: lem-sfb-product-action-exact-forgetting). -/
structure ExactForgetting {C D : Type (u + 2)} [Category.{u + 1} C]
    [Category.{u + 1} D] [Abelian C] [Abelian D] (U : C ⥤ D) : Prop where
  /-- Additivity on morphisms. -/
  [additive : U.Additive]
  /-- Exactness on kernels. -/
  [finiteLimits : PreservesFiniteLimits U]
  /-- Exactness on cokernels. -/
  [finiteColimits : PreservesFiniteColimits U]
  /-- Conservativity on modules. -/
  conservative : U.ReflectsIsomorphisms
  /-- Preservation of injective objects in the stated direction. -/
  injectives : U.PreservesInjectiveObjects
  /-- Conservativity of the canonical termwise induced unbounded derived functor. -/
  derived : ∀ [HasDerivedCategory.{u + 2} C]
    [HasDerivedCategory.{u + 2} D], U.mapDerivedCategory.ReflectsIsomorphisms
  /-- Every bounded-below injective resolution remains that same termwise resolution. -/
  resolutions : ∀ (K I : CochainComplex C ℤ) (f : K ⟶ I)
    (b : ℤ), QuasiIso f → (∀ n : ℤ, Injective (I.X n)) →
    (∀ n : ℤ, n < b → IsZero (I.X n)) →
    QuasiIso ((U.mapHomologicalComplex (.up ℤ)).map f) ∧
    (∀ n : ℤ, Injective (((U.mapHomologicalComplex (.up ℤ)).obj I).X n)) ∧
    (∀ n : ℤ, n < b → IsZero (((U.mapHomologicalComplex (.up ℤ)).obj I).X n))

/-- Grothendieck abelianness with the existing addition, enough injectives and the
underlying sectionwise kernels and sheafified cokernels.
Source: paragraph (3), abelian infrastructure
(blueprint: lem-sfb-product-action-exact-forgetting). -/
structure ActionProperties [abelian : Abelian (ActionModule R P)] : Prop where
  /-- Its addition is precisely the existing addition. -/
  addition : abelian.toPreadditive = actionPreadditive
  /-- Grothendieck abelianness in the coefficient universe. -/
  grothendieck : IsGrothendieckAbelian.{u + 1} (ActionModule R P)
  /-- Enough injective objects. -/
  enough : EnoughInjectives (ActionModule R P)
  /-- Underlying kernels are kernels of module sheaves. -/
  kernels : PreservesFiniteLimits (forgetAction (R := R) (P := P) ⋙
    InternalAbelianSheafModule.sectionModuleFunctor (coherentTopology Profinite.{u}) R.X)
  /-- Underlying cokernels are cokernels of module sheaves. -/
  cokernels : PreservesFiniteColimits (forgetAction (R := R) (P := P) ⋙
    InternalAbelianSheafModule.sectionModuleFunctor (coherentTopology Profinite.{u}) R.X)
  /-- Evaluation of the module kernel gives the sectionwise kernel. -/
  sectionKernels (M N : ActionModule R P) (f : M ⟶ N) (S : Profinite.{u}) :
    PreservesLimit (parallelPair
      ((InternalAbelianSheafModule.sectionModuleFunctor
        (coherentTopology Profinite.{u}) R.X).map f.val) 0)
      (SheafOfModules.evaluation (ringSheaf R) (op S))
  /-- The module cokernel is the sheafification of the presheaf cokernel. -/
  sheafCokernels (M N : ActionModule R P) (f : M ⟶ N) :
    Nonempty (cokernel ((InternalAbelianSheafModule.sectionModuleFunctor
      (coherentTopology Profinite.{u}) R.X).map f.val) ≅
      (PresheafOfModules.sheafification.{u + 1} (𝟙 (ringSheaf R).obj)).obj
        (cokernel ((SheafOfModules.forget.{u + 1} (ringSheaf R)).map
          ((InternalAbelianSheafModule.sectionModuleFunctor
            (coherentTopology Profinite.{u}) R.X).map f.val))))

/-- All clauses of exact free induction for forgetting a commuting action.
This is a specification of normalized data; the theorem below asserts its existence.
Source: paragraph (3), extracted product-action input
(blueprint: lem-sfb-product-action-exact-forgetting). -/
structure Datum where
  /-- An abelian structure on the first action category. -/
  [groupAbelian : Abelian (ActionModule R G)]
  /-- An abelian structure on the retained action category. -/
  [retainedAbelian : Abelian (ActionModule R J)]
  /-- An abelian structure on the product-action category. -/
  [productAbelian : Abelian (ActionModule R (G × J))]
  /-- The three action categories and their underlying kernel/cokernel formulas. -/
  groupProperties : ActionProperties R G
  /-- The retained action category, including discrete cyclic J. -/
  retainedProperties : ActionProperties R J
  /-- The product-action category. -/
  productProperties : ActionProperties R (G × J)
  /-- The existing normalized fixed-section adjunction, including both transposes. -/
  invariants : ProductInvariants R G J
  /-- Trivial-J inflation is additive. -/
  inflationAdditive : (inflate (R := R) (ContinuousMonoidHom.fst G J)).Additive
  /-- Trivial-J inflation preserves kernels. -/
  inflationLimits : PreservesFiniteLimits (inflate (R := R) (ContinuousMonoidHom.fst G J))
  /-- Trivial-J inflation preserves cokernels. -/
  inflationColimits : PreservesFiniteColimits (inflate (R := R) (ContinuousMonoidHom.fst G J))
  /-- Exact conservative forgetting, derived conservativity and injective resolutions. -/
  forgetting : ExactForgetting (forgetFirst R G J)
  /-- The same assertions after forgetting the only action. -/
  plainForgetting : ExactForgetting (forgetAction (R := R) (P := G))
  /-- Exact free induction with the retained action. -/
  induction : Induction R G J
  /-- Exact free induction without the retained action. -/
  plainInduction : PlainInduction R G
  /-- The free module is the extension by zero, with its canonical generators. -/
  extensionIso :
    (InternalAbelianSheafModule.sectionModuleFunctor
      (coherentTopology Profinite.{u}) R.X).obj (freeGroup R G) ≅ extendedUnit R G
  /-- The identification carries [g] to the direct-sum generator [g]. -/
  extensionGenerator (S : Profinite.{u}) (g : C(S, G)) :
    (extensionIso.hom.val.app (op S)) (generator R G S g) = extendedGenerator R G S g
  /-- Flatness of the free internal module is exactness of its tensor functor. -/
  flat : ObjectProperty.flat (freeGroup R G)

end Profinite.CondensedAction.ProductForgetting
