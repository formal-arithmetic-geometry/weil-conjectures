/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.SectionsWithSupport
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# Scalar tests detect the rank-one open unit

Source: Stacks 08FI, 0D6F and 0D6J; rank-one part of the scalar-to-lisse argument
in blueprint direct-images paragraph (3).
(blueprint: lem-sfb-scalar-tests-regular-open-unit).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Scalar tests on the full base site detect the open unit on the regular module after
any weakly etale base change. No lisse descent or finite direct sum is asserted here.
The restriction in the hypothesis is written out to avoid importing its consumer.

Source: Stacks, sites-cohomology.tex, lemmas restrict-K-injective-to-open (08FI),
unbounded-cohomology-of-open (0D6F), modules-abelian-unbounded (0D6J); blueprint
six-functor stability, direct-images paragraph (3), agent scalar-to-lisse sublemma,
steps 1--5 and 7--8, specialized to rank one.
(blueprint: lem-sfb-scalar-tests-regular-open-unit).

Proof: Identify internal modules with section-ring module sheaves by the exact
operations equivalence, preserving the ordinary unit. Exact slice restriction preserves
K-injectives because its extension-by-zero left adjoint is exact. For j the pulled-back
open, take a K-injective resolution s of j^*R[0]. The unit is represented by the ordinary
unit followed by j_*s. The exact/K-flat derived-adjunction comparison identifies its
transpose with the identity, so this represents the specified unit. Cover every object
of Y_proet by affine objects weakly contractible on the full X site: regard it as an
X-site object by composition with a and use the contractible basis there, retaining its
map to Y. On such V, the evaluated unit is x mapping to s(x restricted to U times_X V).
K-injective restriction and the ringed/abelian sections comparison identify its target
with abelian derived sections on U times_X V. Exact evaluation on V identifies its source
with derived sections on V; naturality identifies the arrow with the scalar restriction
in the hypothesis. It is therefore an isomorphism. Evaluate the cone: exact evaluation
commutes with cohomology and makes all its cohomology zero on these covering objects.
Sheaf separatedness makes each cohomology sheaf zero on every Y-site object. The cone is
acyclic, so localization inverts the unit. Transport back to internal modules. The empty
site and identity open follow from the same argument without any nonemptiness assumption.
-/
theorem isIso_regular_open_unit_of_scalar_tests
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (U : X.Opens)
    (hscalar : ∀ (V : X.ProEt), IsAffine V.left →
      (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} V →
      IsIso ((Functor.rightDerivedFunctorNatTrans
        ((sheafSections (Scheme.ProEt.topology X) Ab.{u + 1}).map
          (show Scheme.ProEt.mk (pullback.snd U.ι V.hom ≫ V.hom) ⟶ V from
            MorphismProperty.Over.homMk (pullback.snd U.ι V.hom) rfl).op)).app
              ((DerivedCategory.singleFunctor _ 0).obj (condensedRingObj Λ X))))
    (Y : Scheme.{u}) (a : Y ⟶ X) [WeaklyEtale a] :
    IsIso ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ
      (pullback.snd U.ι a)).unit.app
        ((DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ Y)))) := by
  sorry

end AlgebraicGeometry.ProEtale
