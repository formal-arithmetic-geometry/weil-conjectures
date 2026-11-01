/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
public import WeilConjectures.CategoryTheory.InternalModule.InternalModule
public import WeilConjectures.CategoryTheory.Finite.FiniteContinuousModule
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import WeilConjectures.CategoryTheory.PoincareDuality.EquivalenceInternalModule
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import WeilConjectures.AlgebraicGeometry.GaloisCategories
import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Algebra.Category.MonCat.FilteredColimits

/-! # Finite module transport and normalized stalk comparison -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme


/-- The internal-module equivalence transported along the finite locally constant
comparison `E`.  It is the selected equivalence supplied by
`equivalence_induces_internalModules`, and is used by the finite-module lift below.
Source: Stacks Project, Tag 0DV5 (3), proof; node `new-e4-galois-finite-module-lift`.
(blueprint: new-c7-galois-finite-module-lift-transport). -/
noncomputable def galoisFiniteModuleLiftInternalEquivalence
    {Y : Scheme.{u}} [ConnectedSpace Y] [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (E : Y.FLC ≌ ContAction FintypeCat.{u} G)
    (R : Type (u + 1)) [Ring R] [Finite R] :
    InternalModule R Y.FLC ≌ InternalModule R (ContAction FintypeCat.{u} G) :=
  Classical.choose ((equivalence_induces_internalModules R E).2.2)

/-- The finite-continuous-module equivalence used by the explicit lift.  This is the
constructive equivalence returned by `internalModules_finiteContAction`.
Source: Stacks Project, Tag 0DV5 (3), proof; node `new-e4-galois-finite-module-lift`.
(blueprint: new-c7-galois-finite-module-lift-transport). -/
noncomputable def galoisFiniteModuleLiftFiniteEquivalence
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (R : Type (u + 1)) [Ring R] [Finite R] :
    InternalModule R (ContAction FintypeCat.{u} G) ≌
      FiniteContinuousModule.{u + 1, u, u} R G :=
  Classical.choose (internalModules_finiteContAction R G)

/-- The underlying action isomorphism `i` selected by the finite-continuous-module
construction.  Its inverse transports a finite representation carrier back to the
internal-module carrier.
Source: Stacks Project, Tag 0DV5 (3), proof; node `new-e4-galois-finite-module-lift`.
(blueprint: new-c7-galois-finite-module-lift-transport). -/
noncomputable def galoisFiniteModuleLiftUnderlyingForgetIso
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (R : Type (u + 1)) [Ring R] [Finite R] :
    InternalModule.forget R (ContAction FintypeCat.{u} G) ⋙ finiteContActionForget G ≅
      (galoisFiniteModuleLiftFiniteEquivalence G R).functor ⋙
        FiniteContinuousModule.forget R G :=
  Classical.choose ((Classical.choose_spec (internalModules_finiteContAction R G)).2.2)

/-- The explicit representation equivalence: the lisse-to-module-object equivalence of
`lisseToModuleObject_isIso_of_categories`, then `L`, the internal-module transport through
`E`, the finite-continuous-module equivalence, and `ε`.
Source: Stacks Project, Tag 0DV5 (3), proof; node `new-e4-galois-finite-module-lift`,
proof steps 1 and 2.
(blueprint: new-c7-galois-finite-module-lift-transport). -/
noncomputable def galoisFiniteModuleLiftEquivalence
    {Y : Scheme.{u}} [ConnectedSpace Y] [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (E : Y.FLC ≌ ContAction FintypeCat.{u} G)
    (L : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      LambdaModuleObject Y R ≌ InternalModule R Y.FLC)
    (ε : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      FiniteContinuousModule.{u + 1, u, u} R G ≌ galoisFiniteRepresentations R G)
    (R : Type (u + 1)) [Ring R] [Finite R] :
    LisseModuleSheafCategory Y R ≌ galoisFiniteRepresentations R G := by
  let A := lisseToModuleObject Y R
  letI : A.IsEquivalence := (lisseToModuleObject_isIso_of_categories (Y := Y) (Λ := R)).1
  let K := galoisFiniteModuleLiftInternalEquivalence G E R
  let M := galoisFiniteModuleLiftFiniteEquivalence G R
  exact A.asEquivalence.trans (L R) |>.trans K |>.trans M |>.trans (ε R)

/-- The underlying action comparison supplied by the explicit finite-module transport.
It first applies the action comparison `εaction`, then the inverse of the
underlying comparison `i` of `internalModules_finiteContAction`, and finally
casts along the underlying functor equality of `galoisFiniteModuleLiftInternalEquivalence`
and the supplied object equality `hL`.
Source: Stacks Project, Tag 0DV5 (3), proof; node `new-e4-galois-finite-module-lift`.
(blueprint: new-c7-galois-finite-module-lift-transport). -/
noncomputable def galoisFiniteModuleLiftUnderlyingComparison
    {Y : Scheme.{u}} [ConnectedSpace Y] [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (E : Y.FLC ≌ ContAction FintypeCat.{u} G)
    (L : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      LambdaModuleObject Y R ≌ InternalModule R Y.FLC)
    (ε : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      FiniteContinuousModule.{u + 1, u, u} R G ≌ galoisFiniteRepresentations R G)
    (εaction : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      Nonempty ((ε R).functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ≅
        ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
          (ModuleCat.uliftFunctor.{u + 1, u} R).mapAction G))
    (R : Type (u + 1)) [Ring R] [Finite R]
    (F : LisseModuleSheafCategory Y R)
    (hF : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F.obj))
    (hL : ((L R).functor.obj ((lisseToModuleObject Y R).obj F)).X =
      galoisUnderlyingFLC R F.obj hF) :
    ((galoisFiniteModuleLiftEquivalence G E L ε R).functor.obj F).obj.V →
      ULift.{u + 1, u} (E.functor.obj (galoisUnderlyingFLC R F.obj hF)).obj.V := by
  let A := lisseToModuleObject Y R
  let K := galoisFiniteModuleLiftInternalEquivalence G E R
  let M := galoisFiniteModuleLiftFiniteEquivalence G R
  let B := K.functor.obj ((L R).functor.obj (A.obj F))
  let C := M.functor.obj B
  let hK := equivalence_induces_internalModules R E
  let hKf := (Classical.choose_spec hK.2.2).1
  let hKB : B.X = E.functor.obj ((L R).functor.obj (A.obj F)).X :=
    congrArg (fun H => H.obj ((L R).functor.obj (A.obj F))) hKf
  let hTarget : B.X = E.functor.obj (galoisUnderlyingFLC R F.obj hF) :=
    hKB.trans (congrArg (fun X : Y.FLC => E.functor.obj X) hL)
  let α := Classical.choice (εaction R)
  intro z
  change (ε R).functor.obj C |>.obj.V at z
  let z' := (α.hom.app C).hom.hom z
  let z'' := (galoisFiniteModuleLiftUnderlyingForgetIso G R).inv.app B |>.hom.hom z'.down
  have hCarrier := congrArg (fun X : ContAction FintypeCat.{u} G => X.obj.V.obj) hTarget
  exact ⟨cast hCarrier z''⟩

/-- The fixed stalk comparison candidate.  It is the inverse of the supplied set
comparison `κ` applied to `τ` after the explicit carrier transport above.
Source: Stacks Project, Tag 0DV5 (3), proof; node `new-e4-galois-finite-module-lift`.
(blueprint: new-c7-galois-finite-module-lift-transport). -/
noncomputable def galoisFiniteModuleLiftUnderlyingStalkComparison
    {Y : Scheme.{u}} [ConnectedSpace Y] [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (E : Y.FLC ≌ ContAction FintypeCat.{u} G)
    (τ : E.functor ⋙ forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙
      CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u} ≅
      ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A := Type (u + 1)))
    (κ : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (F : LisseModuleSheafCategory Y R),
      (((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj F.obj) ≃
        (((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
          (galoisUnderlyingSetSheaf R F.obj)))
    (L : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      LambdaModuleObject Y R ≌ InternalModule R Y.FLC)
    (ε : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      FiniteContinuousModule.{u + 1, u, u} R G ≌ galoisFiniteRepresentations R G)
    (εaction : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      Nonempty ((ε R).functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ≅
        ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
          (ModuleCat.uliftFunctor.{u + 1, u} R).mapAction G))
    (R : Type (u + 1)) [Ring R] [Finite R]
    (F : LisseModuleSheafCategory Y R)
    (hF : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F.obj))
    (hL : ((L R).functor.obj ((lisseToModuleObject Y R).obj F)).X =
      galoisUnderlyingFLC R F.obj hF) :
    ((galoisFiniteModuleLiftEquivalence G E L ε R).functor.obj F).obj.V →
      (((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj F.obj) :=
  fun z ↦ (κ R F).symm (τ.hom.app (galoisUnderlyingFLC R F.obj hF)
    (galoisFiniteModuleLiftUnderlyingComparison G E L ε εaction R F hF hL z))

end AlgebraicGeometry.Scheme
