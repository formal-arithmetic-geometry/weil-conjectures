/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting
import Sheaf.Topology.PresheafModuleStalkFunctor

/-!
# Exactness of stalks of sheaves of modules

Source: Stacks Project, Modules, Section 17.3 (Tag 01AF, `section-kernels`)
and Lemma 01AG (`lemma-abelian`) (blueprint: lem-weil-pbc-module-stalk-exact).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat.Presheaf Opposite
noncomputable section
namespace AlgebraicGeometry.RingedSpace
/--
Source: Stacks Project, Modules, Section 17.3 (Tag 01AF, `section-kernels`),
and Lemma 01AG (`lemma-abelian`) (blueprint: lem-weil-pbc-module-stalk-exact).

Sectionwise injectivity implies stalkwise injectivity. Stalks preserve the canonical
kernel, cokernel and image (the stalk of the image inclusion has the same range
as the stalk map of φ), and detect exactness of a complex at its middle term.
The mono, epi and exactness assertions in `ModuleCat` express injectivity,
surjectivity and equality of the image with the kernel, respectively. In particular,
the cokernel assertion gives the canonical linear quotient isomorphism.

Proof (the node's steps):
0. Use the sectionwise kernel and functoriality of stalk maps. Any other categorical
   kernel or cokernel is uniquely isomorphic compatibly with its structure map, so
   its stalk description is independent of these choices
   (`def-weil-sheaf-of-modules-category`, `def-weil-pbc-module-stalk`).
1. If a germ maps to zero, shrink its representative until its image is zero.
   Sectionwise injectivity makes the representative zero on that neighborhood,
   hence the original germ is zero (`def-weil-pbc-module-stalk`). For a sheaf
   monomorphism the sectionwise kernel inclusion is zero, making every section
   kernel zero; inclusions of submodules are sectionwise injective by definition.
2. The sectionwise kernel inclusion is injective, so its stalk map is injective by
   step 1. A germ annihilated by the stalk map of φ has, after shrinking, a
   representative annihilated by φ; this section belongs to the sectionwise
   kernel. Conversely the composite with φ is zero (`def-weil-pbc-module-stalk`).
3. Form the presheaf Q(U) = G(U)/φ(F(U)) and sheafify it as a module presheaf.
   Every map out of G annihilating φ factors sectionwise through Q and then
   uniquely through its sheafification. This constructs the categorical cokernel
   (`def-weil-presheaf-modules-sheafification`,
   `def-weil-sheaf-of-modules-category`).
4. Every germ of Q lifts to a germ of G by sectionwise quotient surjectivity.
   A germ of G maps to zero in Q precisely when, after shrinking, its
   representative lies in the sectionwise image of φ. Thus the stalk quotient
   map is surjective with kernel the image of the stalk map of φ
   (`def-weil-pbc-module-stalk`).
5. Sheafification does not change stalks
   (`lem-weil-pbc-stalk-sheafification-space`). The resulting bijective additive
   stalk map is linear by the module germ action, hence a module isomorphism
   (`def-weil-presheaf-modules-sheafification`, `def-weil-pbc-module-stalk`).
6. The stalk cokernel map is the composite of the quotient map in step 4 and
   the isomorphism in step 5. It is surjective with kernel the image of φ_x;
   the first isomorphism theorem gives the induced linear quotient isomorphism
   (`def-weil-pbc-module-stalk`).
7. The image is the kernel of the cokernel map. Step 2 applied to that map,
   and step 6, identify its stalk inclusion with the image of φ_x. Since
   φ_x factors through this injective inclusion, its map to the stalk image
   is surjective (`def-weil-sheaf-of-modules-category`, `def-weil-pbc-module-stalk`).
8. Use `lem-weil-pbc-ringed-space-module-exactness-local-lifting` (2): exactness
   is equivalent to locally lifting every section killed by the second map.
   Such local lifts give a preimage of every kernel germ. Conversely, stalkwise
   exactness gives a preimage germ at each point; represent it by a section
   and shrink until the equality of germs holds on sections. These neighborhoods
   cover the given open and provide the required local lifts
   (`def-weil-pbc-module-stalk`, `def-weil-pbc-exact-sequence`).
-/
theorem module_stalk_exact (X : RingedSpace.{u})
    {F G : SheafOfModules.{u} (moduleRings X)} (φ : F ⟶ G) :
    ((∀ (U : Opens X),
        Function.Injective (ConcreteCategory.hom (φ.val.app (Opposite.op U)))) →
      ∀ (x : X), Mono ((moduleStalkFunctor X x).map φ)) ∧
    (∀ (x : X),
      Mono ((moduleStalkFunctor X x).map (kernel.ι φ)) ∧
      ((ShortComplex.mk
          ((moduleStalkFunctor X x).map (kernel.ι φ))
          ((moduleStalkFunctor X x).map φ) (by
            rw [← (moduleStalkFunctor X x).map_comp]
            simp)).Exact)) ∧
    (∀ (x : X),
      Epi ((moduleStalkFunctor X x).map (cokernel.π φ)) ∧
      ((ShortComplex.mk
          ((moduleStalkFunctor X x).map φ)
          ((moduleStalkFunctor X x).map (cokernel.π φ)) (by
            rw [← (moduleStalkFunctor X x).map_comp]
            simp)).Exact)) ∧
    (∀ (x : X),
      Epi ((moduleStalkFunctor X x).map (Abelian.factorThruImage φ)) ∧
      Mono ((moduleStalkFunctor X x).map (Abelian.image.ι φ)) ∧
      LinearMap.range ((moduleStalkFunctor X x).map (Abelian.image.ι φ)).hom =
        LinearMap.range ((moduleStalkFunctor X x).map φ).hom) ∧
    (∀ (H : SheafOfModules.{u} (moduleRings X)) (χ : F ⟶ G) (ψ : G ⟶ H),
      ∀ (h : χ ≫ ψ = 0),
        (ShortComplex.mk χ ψ h).Exact ↔
          ∀ (x : X), ((ShortComplex.mk χ ψ h).map (moduleStalkFunctor X x)).Exact) := by
  sorry

end AlgebraicGeometry.RingedSpace
