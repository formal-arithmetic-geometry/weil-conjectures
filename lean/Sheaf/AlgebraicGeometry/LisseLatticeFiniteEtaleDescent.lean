/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Topology.NoetherianSpace
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.CategoryTheory.SiteModuleSheafGluing
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Finite étale descent of lisse integral structures

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf,
Lemma 6.8.13, first paragraph; Stacks Project, Tags 04HN and 04TR
(blueprint: lem-weil-pbc-lisse-lattice-finite-etale-descent).
-/

@[expose] public section

set_option autoImplicit false


universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Finite étale descent of the existence of a lisse integral structure.

Source: Bhatt--Scholze, Lemma 6.8.13, first paragraph, and Stacks Project,
Tags 04HN and 04TR (blueprint: lem-weil-pbc-lisse-lattice-finite-etale-descent).
The module presheaf on the right of `hM` is the slice-site presentation of the
actual inverse image: restriction along an etale arrow, with the identity coefficient
identification on continuous functions. Isomorphisms of module sheaves can be stated on
these underlying module presheaves because the forgetful functor is fully faithful.

Proof plan:
1. By `lem-weil-pbc-finite-etale-etale-local-split` (Stacks 04HN), choose an etale
   covering on which p is a finite disjoint union of identity maps. Surjectivity gives
   at least one sheet on each nonempty chart. These are also pro-etale covers by
   `def-weil-pbc-site-comparison-morphism`. The slice presentation agrees with the
   inverse-image colimit in `def-weil-proetale-inverse-image`: a representative on Z
   and a map V to W times_X Z restricts to V; conversely the graph of V to W gives
   the inverse representative. The coefficient identification is identity on C(V, E).
2. Using the given rationalization isomorphism, inject each sheet lattice into L.
   Injectivity is local and is coordinatewise injectivity of A into E. On each split
   chart take their finite sum as submodule sheaves of L. This construction uses
   finite sums of images and ordinary sheaf gluing, not a descent datum on M.
3. Refine by simultaneous pro-etale trivializations of L and these finitely many
   lattices. On a rank-n piece write their inclusions as g_j in GL_n(C(T,E)). Around
   each point t, continuity puts every entry of g_j(t) inverse times g_j(s) minus I
   in the maximal ideal. Its determinant is 1 modulo that ideal, hence it is in
   GL_n(A); the inverse is continuous by the adjugate formula. Open neighborhoods
   are etale by `lem-weil-pbc-open-immersion-etale` and form pro-etale covers. The
   j-th lattice is therefore the constant-coordinate lattice g_j(t) A^n there.
4. Their sum Lambda in E^n is finitely generated, torsion free and spans E^n.
   By `lem-weil-l-adic-extension-integers-dvr` and
   `lem-sc-dvr-fg-torsionfree-free` it is finite free of rank n. Clearing finitely
   many denominators shows that an A-basis is an E-basis. Its matrix h_t identifies
   the sum sheaf with h_t A^n: the inclusions in both directions hold sectionwise.
   Thus the sum is finite locally free and its scalar extension is L.
5. On overlaps, sheet enumerations differ locally by a permutation, on a clopen
   decomposition. Finite sums inside L are unchanged by permutation, and their
   equality induces identity and triple-overlap compatibilities. Apply
   `lem-weil-pbc-site-module-sheaf-gluing` (Stacks 04TR) to obtain M₀ on X.
6. Glue the inclusions and their scalar-extension maps. Restriction of tensor
   products to slices uses the same sectionwise tensors and sheafification, by
   `def-pur-sheaf-tensor-product`. The local inverses glue to the displayed global
   isomorphism. Composite trivializing covers give finite local freeness. For rank
   zero use the zero module; for the empty scheme use the empty covering. No
   equality with the specified lattice after pullback is asserted.
-/
theorem exists_lisse_lattice_finite_etale_descent
    (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (L : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X)))
    (hL : L.IsFiniteLocallyFree)
    {Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (hM : ∃ M : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheaf l E Y)),
      M.IsFiniteLocallyFree ∧
        Nonempty ((SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (lisseIntegerToField l E Y) M).val ≅
          (PresheafOfModules.pushforward.{u + 1, u, u, u + 1, u + 1, u + 1}
            (lisseEtaleCoefficientIdentification l E p)).obj L.val)) :
    ∃ M₀ : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheaf l E X)),
      M₀.IsFiniteLocallyFree ∧
        Nonempty ((SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (lisseIntegerToField l E X) M₀).val ≅ L.val) := by
  sorry

end AlgebraicGeometry.ProEtale
