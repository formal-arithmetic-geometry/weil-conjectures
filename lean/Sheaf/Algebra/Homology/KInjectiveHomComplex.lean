/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# K-injectivity of the sheaf Hom complex

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.8 (Tag 0A96),
`sites-cohomology-lemma-RHom-from-K-flat-into-K-injective`
(blueprint: lem-pur-hom-kflat-into-kinjective).
-/

universe u v

open CategoryTheory

namespace CochainComplex

/-- The sheaf Hom complex from a K-flat complex into a K-injective complex is K-injective.
Source: Stacks Project, Cohomology on Sites, Lemma 21.34.8 (Tag 0A96)
(blueprint: lem-pur-hom-kflat-into-kinjective).

Proof: let `K` be any acyclic complex of sheaves of modules. K-flatness of `L`
(`def-pc-kflat-complex`) makes `Tot(K ⊗ L)` acyclic. The tensor-Hom isomorphism
`lem-sc-derived-hom-tensor-total` identifies `Hom(K, Hom(L, I))` with
`Hom(Tot(K ⊗ L), I)` as sheaf complexes. Taking global sections and degree-zero
cohomology identifies these with morphisms in the homotopy category: degree-zero
cocycles are chain maps and coboundaries are null-homotopic maps
(`def-pur-hom-complex`). K-injectivity of `I` (`def-pur-kinjective-complex`)
therefore makes every map from `K` to `Hom(L, I)` null-homotopic. Since `K` was
arbitrary, the Hom complex is K-injective. -/
theorem isKInjective_homComplex_of_isKFlat
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max u v}}
    (L I : CochainComplex
      (SheafOfModules.{max u v} ((sheafCompose J
        (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (hL : L.IsKFlat) [I.IsKInjective] :
    (CategoryTheory.homComplex L I).IsKInjective := by
  sorry

end CochainComplex
