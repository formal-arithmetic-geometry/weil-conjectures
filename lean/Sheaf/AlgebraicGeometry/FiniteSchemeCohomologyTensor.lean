/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Topology.RingedSpaceModuleCohomology

/-! # Cohomology and tensor invariance on a finite scheme

Source: Stacks Project, varieties.tex, Tag 0AYT, parts (3)--(5), rank one
(blueprint: lem-pc-finite-scheme-cohomology-tensor).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- On the spectrum of a finite-dimensional algebra, higher module cohomology vanishes,
global sections are finite dimensional, and tensoring with an invertible module preserves
their dimension and the Euler characteristic. Scalar restriction uses the given algebra
map, and the Euler characteristic uses its induced structure morphism.
Source: Stacks Project, varieties.tex, Tag 0AYT, parts (3)--(5), rank one
(blueprint: lem-pc-finite-scheme-cohomology-tensor).

Proof:
1. A finite basis makes A finite over k (`def-weil-finite-dimensional-subspace`). By
   `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`, Spec A is finite discrete.
   Chains of ideals terminate by dimension, so A is Noetherian and Spec A locally
   Noetherian (`pqf-def-locnoeth`).
2. Coherence gives quasi-coherence and finite type (`pqf-lem-coherent-ft-locnoeth`). By
   `lem-weil-pbc-quasi-coherent-finite-type-affine`, global sections are finite over A,
   hence finite over k by `lem-weil-pbc-finite-module-over-finite-algebra`.
3. Trivialize L on each open singleton using `def-sc-invertible-module`. The disjoint
   singleton cover lets the sheaf axiom (`def-weil-sheaf-of-modules-category`) glue the
   trivializations and their inverses, giving L isomorphic to the structure sheaf.
4. Tensor this isomorphism with G and use the tensor unit
   (`def-pur-sheaf-tensor-product`, `def-weil-pbc-module-tensor-product`). Thus G tensor L
   is isomorphic to G, coherent, and has isomorphic global sections and cohomology.
   Global sections of both modules are finite dimensional with equal dimension.
5. Affine quasi-coherent vanishing (`lem-pc-affine-vanishing`) gives the positive-degree
   vanishing for G, and step 4 transfers it to G tensor L.
6. The structure morphism is finite (`def-weil-finite-integral-morphism`), hence proper
   (`lem-weil-pbc-finite-proper`). The Euler characteristics are therefore defined
   (`lem-pc-euler-characteristic-well-defined`, `def-pc-euler-characteristic`). Only
   degree zero contributes by step 5; degree zero is global sections
   (`pqf-def-cohomology`). Step 4 gives equality of the two Euler characteristics. The
   comparison of module-derived and underlying abelian-sheaf cohomology identifies
   this with the recorded `eulerChar` encoding. -/
theorem finiteSchemeCohomologyTensor
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] [FiniteDimensional k A]
    (G L : (Spec (.of A)).Modules)
    (hG : RingedSpace.IsCoherent (Spec (.of A)).toRingedSpace G)
    (hL : L.IsInvertible) :
    (∀ q : ℕ, 0 < q →
      IsZero ((RingedSpace.moduleCohomology (Spec (.of A)).toRingedSpace q).obj G)) ∧
    (∀ q : ℕ, 0 < q →
      IsZero ((RingedSpace.moduleCohomology (Spec (.of A)).toRingedSpace q).obj (G ⊗ₘ L))) ∧
    @FiniteDimensional k Γ(G, ⊤) _ _
      (Module.compHom Γ(G, ⊤)
        ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap k A))) ∧
    @FiniteDimensional k Γ(G ⊗ₘ L, ⊤) _ _
      (Module.compHom Γ(G ⊗ₘ L, ⊤)
        ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap k A))) ∧
    @Module.finrank k Γ(G ⊗ₘ L, ⊤) _ _
      (Module.compHom Γ(G ⊗ₘ L, ⊤)
        ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap k A))) =
      @Module.finrank k Γ(G, ⊤) _ _
        (Module.compHom Γ(G, ⊤)
          ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap k A))) ∧
    @eulerChar k _ (Spec (.of A)) ⟨Spec.map (CommRingCat.ofHom (algebraMap k A))⟩ G =
      (@Module.finrank k Γ(G, ⊤) _ _
        (Module.compHom Γ(G, ⊤)
          ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap k A))) : ℤ) ∧
    @eulerChar k _ (Spec (.of A)) ⟨Spec.map (CommRingCat.ofHom (algebraMap k A))⟩ (G ⊗ₘ L) =
      @eulerChar k _ (Spec (.of A)) ⟨Spec.map (CommRingCat.ofHom (algebraMap k A))⟩ G := by
  sorry

end AlgebraicGeometry.Scheme.Modules
