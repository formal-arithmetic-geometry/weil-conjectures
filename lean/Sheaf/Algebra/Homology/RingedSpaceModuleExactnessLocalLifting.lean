/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Sheaf.Topology.PresheafModuleStalkFunctor

/-!
# Local lifting for epimorphisms and exact complexes of module sheaves

Source: Stacks Project, Modules, Section 01AF and Lemma 01AG; Sheaves, Definition
007U and Lemma 0H7H (blueprint: lem-weil-pbc-ringed-space-module-exactness-local-lifting).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/--
Source: Stacks Project, Modules, Section 01AF and Lemma 01AG; Sheaves, Definition
007U and Lemma 0H7H (blueprint: lem-weil-pbc-ringed-space-module-exactness-local-lifting).

The category of modules on a ringed space is abelian (Mathlib's
`SheafOfModules.instAbelian`) and its kernels are computed sectionwise.
Epimorphisms are exactly the maps admitting local lifts of sections, and exactness
at the middle term of a complex is exactly local lifting of sections annihilated by
the second map.

Proof (the node's five steps):
1. In the abelian category of module sheaves, an epimorphism is equivalent to zero
   cokernel (`lem-weil-pbc-preadditive-epi-iff-cokernel-zero`).
2. Local lifting implies epimorphism: the difference of two maps agreeing after φ
   vanishes on every local lift. Naturality and the sheaf separation axiom imply that
   it vanishes on all sections (`def-weil-sheaf-of-modules-category`).
3. Conversely, zero cokernel means that the sheafification of the sectionwise quotient
   is zero (`def-weil-presheaf-modules-sheafification`). Its stalks equal those of the
   quotient (`lem-weil-pbc-stalk-sheafification-space`). The class of a section thus has
   zero germ, so it vanishes on a neighborhood (`def-weil-pbc-module-stalk`). There
   the section is in the image of φ. These neighborhoods cover the original open.
4. For a complex, factor χ through the sectionwise kernel of φ. Exactness is equivalent
   to this factor being epi (`lem-weil-pbc-abelian-exact-iff-epi-kernel-lift` and
   `def-weil-pbc-exact-sequence`).
5. Apply the equivalence of steps 1–3 to that factor. Sections of the kernel are exactly
   sections killed by φ, and its restrictions are inherited from G, giving clause (2).
-/
theorem module_exactness_local_lifting (X : RingedSpace.{u}) :
    (∀ (F G : SheafOfModules.{u} (moduleRings X)) (φ : F ⟶ G) (W : Opens X),
        Set.range (ConcreteCategory.hom ((kernel.ι φ).val.app (op W))) =
          {g | φ.val.app (op W) g = 0}) ∧
      (∀ (F G : SheafOfModules.{u} (moduleRings X)) (φ : F ⟶ G),
        (Epi φ ↔ IsZero (cokernel φ)) ∧
        ((∀ (W : Opens X) (t : G.val.obj (op W)),
          (∃ (I : Type u) (V : I → Opens X) (hV : ∀ i, V i ≤ W)
              (g : ∀ i, F.val.obj (op (V i))),
              (⨆ i, V i) = W ∧
                ∀ i, φ.val.app (op (V i)) (g i) =
                  G.val.map (homOfLE (hV i)).op t)) ↔ Epi φ)) ∧
      (∀ (F G H : SheafOfModules.{u} (moduleRings X))
          (χ : F ⟶ G) (φ : G ⟶ H) (h : χ ≫ φ = 0),
        (ShortComplex.mk χ φ h).Exact ↔
          ∀ (W : Opens X) (g : G.val.obj (op W)),
            φ.val.app (op W) g = 0 →
              ∃ (I : Type u) (V : I → Opens X) (hV : ∀ i, V i ≤ W)
                (f : ∀ i, F.val.obj (op (V i))),
                (⨆ i, V i) = W ∧
                  ∀ i, χ.val.app (op (V i)) (f i) =
                    G.val.map (homOfLE (hV i)).op g) := by
  sorry

end AlgebraicGeometry.RingedSpace
