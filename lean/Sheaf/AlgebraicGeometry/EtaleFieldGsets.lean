/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.FieldTheory.KrullTopology
import Sheaf.AlgebraicGeometry.EtaleCoproductOfFiniteSeparableFields
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.FieldTheory.EtaleFieldGaloisClassification
import WeilConjectures.Mathlib.RingTheory.Etale.Field

/-!
# Étale schemes over a field and continuous G-sets

Source: Stacks Project, Tags 03QR and 03QS (blueprint: lem-exc-etale-field-gsets).
-/

@[expose] public section

universe u w

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

instance hasForget₂TypeTopCat : HasForget₂ (Type u) TopCat :=
  ⟨TopCat.discrete, rfl⟩

instance hasForget₂DiscreteContActionType (G : Type*) [Monoid G] [TopologicalSpace G] :
    HasForget₂ (DiscreteContAction (Type u) G) (Type u) :=
  HasForget₂.trans (DiscreteContAction (Type u) G) (ContAction (Type u) G) (Type u)

/-- Stacks Project, Tags 03QR and 03QS (blueprint: lem-exc-etale-field-gsets).
The geometric-point functor carries the Galois action by precomposition. An étale scheme
over a field is a coproduct of spectra of finite separable extensions. Their geometric
points are finite transitive Galois sets, with open stabilizers, giving continuity.
The finite Galois correspondence identifies maps between components, proving full
faithfulness. Decomposing any discrete continuous Galois set into orbits and taking
the coproduct of the spectra of their fixed fields proves essential surjectivity.
Finally, every geometric point over a point of an étale scheme lifts through a
surjective étale family, and every point has a geometric point. Thus a family is
a cover exactly when its image under this functor is jointly surjective. -/
theorem etaleFieldGsets
    (K : Type u) [Field K]
    (Ksep : Type u) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] :
    ∃ (E : Scheme.Etale (Spec (CommRingCat.of K)) ≌
        DiscreteContAction (Type u) (Gal(Ksep / K)))
      (points : ∀ X : Scheme.Etale (Spec (CommRingCat.of K)),
        ((forget₂ _ (Type u)).obj (E.functor.obj X)) ≃
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ksep))) ⟶
            (Scheme.Etale.forget _).obj X)),
      (∀ (X Y : Scheme.Etale (Spec (CommRingCat.of K))) (f : X ⟶ Y)
          (x : (forget₂ _ (Type u)).obj (E.functor.obj X)),
        points Y ((forget₂ _ (Type u)).map (E.functor.map f) x) =
          points X x ≫ (Scheme.Etale.forget _).map f) ∧
      (∀ (X : Scheme.Etale (Spec (CommRingCat.of K))) (g : Gal(Ksep / K))
          (x : (forget₂ _ (Type u)).obj (E.functor.obj X)),
        (points X (((E.functor.obj X).obj.obj.ρ g) x)).left =
          Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (points X x).left) ∧
      (∀ {ι : Type w} (X : Scheme.Etale (Spec (CommRingCat.of K)))
          (U : ι → Scheme.Etale (Spec (CommRingCat.of K))) (f : ∀ i, U i ⟶ X),
        Sieve.ofArrows U f ∈ (Spec (CommRingCat.of K)).smallEtaleTopology X ↔
          ∀ x : (forget₂ _ (Type u)).obj (E.functor.obj X),
            ∃ (i : ι) (y : (forget₂ _ (Type u)).obj (E.functor.obj (U i))),
              (forget₂ _ (Type u)).map (E.functor.map (f i)) y = x) := by
  sorry

end AlgebraicGeometry
