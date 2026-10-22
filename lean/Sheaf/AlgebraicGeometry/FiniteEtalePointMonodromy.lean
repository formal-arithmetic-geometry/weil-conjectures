/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.SixFunctors.FlatModel
public import Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Point monodromy of a finite etale cover

Source: blueprint `lem-trf-devissage-generation`, proof Step 3.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Monodromy minus identity for the canonical module stalk, with the base point
identified by the given equality. Source: the generic-fibre argument in
`lem-trf-devissage-generation`, Step 3
(blueprint: lem-trf-finite-etale-point-monodromy). -/
@[irreducible]
noncomputable def genericStalkMonodromy (A : Type u) [CommRing A]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (σ : Ω ≃+* Ω)
    (hs : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x = x) :
    finiteCoefficientModuleStalkFunctor x A ⟶ finiteCoefficientModuleStalkFunctor x A :=
  (proEtaleStalkReparam A x σ).hom ≫
    eqToHom (congrArg (fun z ↦ finiteCoefficientModuleStalkFunctor z A) hs) - 𝟙 _

/-- A point-monodromy obstruction, retaining the same fibre functor and endomorphism
in its generator and constant-extension clauses. Source: the generic-fibre argument of
`lem-trf-devissage-generation`, Step 3
(blueprint: lem-trf-finite-etale-point-monodromy). -/
structure SeparatingPointMonodromy (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1, u} A))
    (t : F ⟶ F) (L : proEtaleRingModules X (proEtaleConstantRing X A)) : Prop where
  generator : sfProEtaleClosureGenerators X A
    ((DerivedCategory.singleFunctor _ 0).obj L)
  nonnilpotent : ¬ IsNilpotent (End.of (t.app L))
  constants : ∀ (str : Stratification X) (i : Fin str.n)
          (j : str.domain i ⟶ (str.immersion i).image) [IsOpenImmersion j],
          j ≫ (str.immersion i).imageι = str.immersion i →
          t.app ((sfIntrinsicModuleEquivalence X A).functor.obj
            ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
              (str.immersion i).imageι).obj
              ((ProEtale.openImmersionLowerShriek
                (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
                ((constantSheaf (ProEt.topology (str.domain i))
                  (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
                    (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))))) = 0

/-- A finite etale cover with a two-cycle at a geometric point separates a flat lisse
sheaf from the constant stratum extensions by canonical point monodromy.
Source: blueprint `lem-trf-devissage-generation`, proof Step 3
(blueprint: lem-trf-finite-etale-point-monodromy).

Proof: use the canonical exact module stalk and its germ-normalized reparametrization
by sigma, and subtract the identity. Take L to be the finite etale direct image of the
constant regular module on V, followed by comparison and intrinsic realization.
Finite etale covers split etale locally into finitely many copies of the base; their
direct images of the regular module therefore have finite free local models. Thus L
is lisse and flat, and its degree-zero complex is a generator from the one-stratum
stratification of X.

The finite stalk formula identifies its fibre with A-valued functions on the finite
set of lifts to V, compatibly with precomposition. On the two-cycle through y, the
nonzero vector delta_y-delta_(sigma y) is an eigenvector of monodromy of eigenvalue -1.
In characteristic three monodromy minus identity fixes it, so is not nilpotent.

A closed immersion has at most one lift of a geometric point. Its direct-image stalk
is zero if there is no lift and is the original stalk at the unique lift otherwise.
Extension by zero for an open immersion similarly has zero stalk outside the open
and the original stalk inside. Since lifts are unique, changing the geometric point
by sigma fixes these lifts whenever they exist. The fibre of the constant regular
module is the regular module, with trivial action on its constant germs. Consequently
monodromy minus identity is zero on every constant stratum extension. All comparisons
are normalized on germs, so these identifications commute with sigma and with the
etale/pro-etale and intrinsic fixed-module equivalences. Empty schemes and empty fibres
contribute zero objects and require no separate nonemptiness assumption. -/
theorem finite_etale_point_monodromy
    {X V : Scheme.{u}} (π : V ⟶ X) [IsFinite π] [Etale π]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    (σ : Ω ≃+* Ω)
    (hs : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x = x)
    (y : Spec (.of Ω) ⟶ V) (hy : y ≫ π = x)
    (hmove : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ y ≠ y)
    (htwo : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ y = y)
    (A : Type u) [CommRing A] [Finite A] [CharP A 3] [Nontrivial A] :
    let F := finiteCoefficientModuleStalkFunctor x A
    let t := genericStalkMonodromy A x σ hs
    ∃ L : proEtaleRingModules X (proEtaleConstantRing X A),
      SeparatingPointMonodromy X A F t L := by
  sorry

end AlgebraicGeometry
