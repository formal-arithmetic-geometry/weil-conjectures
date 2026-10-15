/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Paper.SiteLocallyConstantFiniteType
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.RingTheory.RingPseudoCoherent

/-! # Derived tensor preserves locally constant finite type cohomology

Source: Stacks Project, Cohomology on Sites, Tag 094H
(blueprint: lem-weil-pbc-locally-constant-tensor).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

set_option synthInstance.maxSize 2048 in
/-- Over a Noetherian coefficient ring, tensoring bounded-above derived objects with
locally constant finite type cohomology again has locally constant finite type cohomology.
`P` and `Q` are arbitrary K-flat representatives of the derived objects; the conclusion
computes derived tensor by their total tensor, exactly as in the node's convention.

Source: Stacks Project, Cohomology on Sites, Tag 094H
(blueprint: lem-weil-pbc-locally-constant-tensor).

Proof plan:
1. Restrict to slices using exact restriction
   (`lem-pur-site-restriction-module-adjunction-exact`). Restriction commutes with tensor
   (`def-pur-sheaf-tensor-product`). Flatness restricts by the extension-tensor formula
   (`lem-weil-pbc-ringed-slice-extension-tensor`); extension by zero detects zero by local
   sections (`def-weil-extension-by-zero-presheaf`,
   `lem-weil-pbc-site-sheafification-sections-local`), hence reflects exactness.
   Bounded-above flat representatives remain K-flat on slices
   (`lem-pc-bounded-above-flat-kflat-site`).
2. In degree i, with upper bounds bK,bL, truncate below i-bL and i-bK respectively.
   Bounded flat replacements (`lem-pc-kflat-bounded-flat-replacement`) and total-degree
   bounds show that the removed kernels have tensor cohomology zero in degrees i and i+1.
   A local cycle/boundary chase using local lifts through quotient sheafification identifies
   degree-i tensor cohomology before and after truncation. K-flatness and cones ensure
   independence of representatives (`def-pc-kflat-complex`).
3. The bounded objects admit local bounded constant finite-module models
   (`lem-weil-pbc-site-bounded-constant-model`). Refine twice to obtain simultaneous models;
   only finitely many refinements are needed for the fixed degree i.
4. Exact constant sheafification (`lem-weil-pbc-site-module-presheaf-sheafification-exact`)
   commutes with cohomology. Noetherianity makes submodules of finite modules finite
   (induct on the rank of a finite free cover). The Noetherian pseudo-coherence criterion
   (`lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion`) supplies bounded-above
   finite free models (`def-pc-ring-pseudo-coherent-complex`). Their constant sheaves are
   flat termwise and K-flat by `lem-pc-bounded-above-flat-kflat-site`.
5. Tensor bases identify constant finite-free sheaf tensors with constant module tensors.
   Upper bounds c,d leave only i-d ≤ p ≤ c in total degree i. Thus the total tensor is
   termwise constant finite free, with differential dP tensor 1 + (-1)^p 1 tensor dQ.
   Its degree-i cohomology is constant with finite value by exact sheafification and
   Noetherianity (`def-pc-tensor-complex-sheaves`).
6. These covering-slice computations for each object and each i are precisely local
   constancy of finite type. No points or simultaneous infinite refinement are used.
-/
theorem locallyConstantFiniteType_derivedTensor
    {C : Type u} [Category.{u} C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B))))]
    (K L : DerivedCategory (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))))
    (hK : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj K))
    (hL : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj L))
    (hKlc : ∀ i : ℤ, IsLocallyConstantFiniteType J.toGrothendieck B
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj K))
    (hLlc : ∀ i : ℤ, IsLocallyConstantFiniteType J.toGrothendieck B
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj L))
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) ℤ)
    (hP : CochainComplex.IsKFlat P) (hQ : CochainComplex.IsKFlat Q)
    (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L) :
    ∀ i : ℤ, IsLocallyConstantFiniteType J.toGrothendieck B
      ((CochainComplex.mapBifunctor P Q
        (@CategoryTheory.MonoidalCategory.curriedTensor _ _
          (SheafOfModules.monoidalCategory
            ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj
              (CommRingCat.of B))))).homology i) := by
  sorry

end SheafOfModules
