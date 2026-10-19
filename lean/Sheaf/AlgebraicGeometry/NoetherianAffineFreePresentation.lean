/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre
import WeilConjectures.AlgebraicGeometry.AffineFreeFiniteStalkGeneration
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import Sheaf.AlgebraicGeometry.EtaleStratifiedFinite
import Sheaf.Topology.SpectralConstructibleFiniteIntersection
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.ConstructibleModuleSupportGeneral
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Sheaf.AlgebraicGeometry.FiniteEtalePushforwardFiniteType

/-!
# Affine free presentations for constructible modules

Source: Stacks Project, `etale-cohomology.tex`, Tag 095N, lemma
`category-constructible-modules` (blueprint: lem-per-noetherian-affine-free-presentation).

The theorem below is the finite affine presentation statement.  The displayed
coproducts are finite because their indices are `Fin n` and `Fin m`; the
extension-by-zero summands are `Etale.etaleLowerShriek` applied to the regular
constant module on an affine étale object.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The free module sheaf attached to an étale object, namely the extension by zero
of the constant regular module.

Source: Stacks Project, `etale-cohomology.tex`, Tag 03DI and Tag 095N
(blueprint: lem-per-noetherian-affine-free-presentation). -/
noncomputable def affineFreeEtaleModule
    (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] (W : X.Etale) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  (Etale.etaleLowerShriek (ModuleCat.{u + 1} R) W.hom inferInstance).obj
    ((constantSheaf W.left.smallEtaleTopology
      (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R))

/-- The finite coproduct of the affine free modules indexed by `Fin k`.
Source: Stacks Project, Tag 095N (blueprint: lem-per-noetherian-affine-free-presentation). -/
noncomputable def finiteAffineFreeCoproduct
    (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] (k : ℕ)
    (W : Fin k → X.Etale) : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  letI : HasColimit (Discrete.functor (fun i : Fin k ↦ affineFreeEtaleModule X R (W i))) :=
    (HasFiniteCoproducts.out k).has_colimit
      (Discrete.functor (fun i : Fin k ↦ affineFreeEtaleModule X R (W i)))
  colimit (Discrete.functor (fun i : Fin k ↦ affineFreeEtaleModule X R (W i)))

/-- Every constructible sheaf of modules over a Noetherian ring on a qcqs scheme has
a finite affine étale free presentation.

Source: Stacks Project, `etale-cohomology.tex`, Tag 095N, lemma
`category-constructible-modules`, lines 12412--12466
(blueprint: lem-per-noetherian-affine-free-presentation).

Proof plan, retaining all seven steps of the node:
1. `lem-trf-noetherian-submodule-finitely-presented` gives finite presentation of finite
   values. Restrict a global stratification to affine opens; conversely apply
   `lem-weil-pbc-etale-stratification-local-gluing-core` and pull constant charts back
   along its actual factorization maps (`lemma-constructible-pullback-constant`). Thus
   `lem-sfb-discrete-noetherian-constructible-serre` applies to this global predicate,
   including kernels, cokernels and extensions; split extensions give finite sums.
2. Identify the sheafified free presheaf with the sum-extension of the regular module:
   send a basis lift to 1 in its summand. Coefficient sections are locally constant,
   so the map is locally bijective. Use `lem-weil-pbc-free-yoneda-presheaf-module`,
   `def-weil-presheaf-modules-sheafification`, and
   `lem-weil-pbc-site-sheafification-iso-locally-bijective`; the induced inverse is linear.
3. `lem-weil-pbc-etale-stratified-finite` makes an affine etale object finite etale on
   constructible immersed strata. Apply `lem-weil-pbc-etale-shriek-base-change-modules`,
   pullback of constants, and `lem-weil-pbc-etale-shriek-star-finite-modules`.
   `lem-per-finite-etale-pushforward-finite-type` makes each restriction locally constant
   of finite type, since the regular module is cyclic. Hence each generator is constructible.
4. Index affine free maps to an arbitrary constructible G by pairs (W,f). For a finite
   subfamily S its sum and cokernel are constructible by step 1.
   `new-constructible-module-support-general` makes the cokernel support T_S constructible;
   `prop-weil-pbc-geometric-stalks-exact` identifies its stalk with the cokernel of the
   stalk map. Thus the complement of T_S is precisely the locus of stalkwise surjectivity.
5. Lift a geometric point to a local trivializing cover using
   `lem-weil-pbc-etale-cover-geometric-point-lift`. Use `lemma-openclosed-stalk-upperstar`
   and `lem-weil-pbc-constant-sheaf-geometric-stalk` to identify the stalk with a finite
   module. `lem-weil-pbc-affine-free-finite-stalk-generation` supplies a finite S surjective
   there. Consequently the intersection of the T_S is empty.
6. `lem-weil-pbc-qcqs-scheme-spectral` and
   `lem-weil-pbc-spectral-constructible-finite-intersection` select finitely many T_S with
   empty intersection. Their union of indices gives one surjection at every stalk.
   For an empty selected family X is empty and S is empty. Exactness and
   `lemma-weil-pbc-geometric-stalk-conservative` make the cokernel zero, hence the map epic.
7. Apply steps 4--6 first to F and then to its constructible kernel. Compose the second
   epimorphism with the kernel inclusion. Its image is exactly that kernel, so the first
   map is its cokernel. Reindex the two finite families by `Fin m` and `Fin n`, using step 2
   to express the generators as sum-extensions. Zero F, empty X, the zero ring and either
   empty family are allowed; no finiteness of underlying coefficient or module sets is used.
-/
theorem exists_noetherian_affine_free_presentation
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    [IsConstructibleSheaf F] :
    ∃ (n m : ℕ) (U : Fin n → X.Etale) (V : Fin m → X.Etale),
      (∀ i : Fin n, IsAffine (U i).left) ∧
      (∀ j : Fin m, IsAffine (V j).left) ∧
      ∃ (f : finiteAffineFreeCoproduct X R m V ⟶ finiteAffineFreeCoproduct X R n U)
        (g : finiteAffineFreeCoproduct X R n U ⟶ F)
        (w : f ≫ g = 0),
        Nonempty (IsColimit (CokernelCofork.ofπ g w)) := by
  sorry

end AlgebraicGeometry.Scheme

end
