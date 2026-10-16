/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Algebra.Homology.DerivedTensor
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Tor amplitude on the small pro-etale site

Source: Stacks Project, Cohomology on Sites, Definition 21.46.1, Tag 08FZ, (1)--(2)
(blueprint: def-weil-proetale-tor-amplitude).

The tensor dependency is given on cochain representatives with a K-flat resolution.
Accordingly the vanishing condition is tested on all such resolutions of representatives
of the given derived object. K-flat resolutions exist and their tensors compute the same
derived tensor product, so this is independent of any representative or resolution choice.
-/

@[expose] public section

universe t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Tor amplitude in the ordered interval `[a,b]` on the small pro-etale site.
For every module sheaf in degree zero, the cohomology of the derived tensor vanishes
outside the interval. We use the recorded `derivedTensor` on every K-flat resolution
of every cochain representative isomorphic to `K`; this imposes no choice of resolution.

Source: Stacks Project, Cohomology on Sites, Definition 21.46.1 (1), Tag 08FZ
(blueprint: def-weil-proetale-tor-amplitude). -/
noncomputable def HasProEtaleTorAmplitude (Y : Scheme.{t}) (A : Type t) [CommRing A]
    (K : proEtaleDerivedCategory Y A) (a b : ℤ) : Prop :=
  let R := (constantSheaf (ProEt.topology Y) CommRingCat.{t + 1}).obj
    (CommRingCat.of (ULift.{t + 1, t} A))
  let S := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
  let C := ringedSiteModules.{t + 1} S
  letI := HasDerivedCategory.standard C
  a ≤ b ∧ ∀ (L P : CochainComplex C ℤ),
    Nonempty (DerivedCategory.Q.obj L ≅ K) →
    ∀ (f : P ⟶ L) (hf : QuasiIso f)
      (hP : CochainComplex.IsAcyclicTensorKFlat.{t + 1, t} (R := R) P)
      (M : C) (i : ℤ),
      (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor C i).obj
        (derivedTensor Y A L
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) P f hf hP))

/-- Finite Tor amplitude means a single ordered integer interval works for every module
sheaf, rather than a separate bound for each test sheaf.

Source: Stacks Project, Cohomology on Sites, Definition 21.46.1 (2), Tag 08FZ
(blueprint: def-weil-proetale-tor-amplitude). -/
noncomputable def HasFiniteProEtaleTorAmplitude (Y : Scheme.{t}) (A : Type t) [CommRing A]
    (K : proEtaleDerivedCategory Y A) : Prop :=
  ∃ a b : ℤ, HasProEtaleTorAmplitude Y A K a b

end AlgebraicGeometry.Scheme
