/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.Algebra.Homology.ModuleHomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomologySequence
import Sheaf.Algebra.Homology.BoundedAboveCoherentRHom

/-! # Coherent derived Hom into a finite-injective-dimension complex

Source: Stacks Project, dualizing.tex, Tag 0G4H, lemma-finite-ext-into-bounded-injective;
more-algebra.tex, Tag 0A5S, definition-injective-dimension
(blueprint: lem-trf-coherent-rhom-finite-injective-dimension).

The shared one-object ringed site presents ordinary A-modules. Evaluation at its unique
object reads their underlying A-modules. The derived Hom is the recorded ringed-site functor.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedCategory

/-- Derived Hom into a coherent complex of finite injective dimension has finite
cohomology for every coherent input, including inputs unbounded in both directions.
Source: Stacks Project, dualizing.tex, Tag 0G4H, and more-algebra.tex, Tag 0A5S
(blueprint: lem-trf-coherent-rhom-finite-injective-dimension).

Proof:
1. Choose a bounded injective representative I of L, supported in [a,b], and a representative
P of K. Bounded-below injective complexes are K-injective
(lem-weil-pbc-bounded-below-injectives-kinjective). Thus the recorded derived internal Hom
(def-pur-derived-internal-hom) is computed by the total Hom into I. Its A-module-valued
presentation is def-sc-module-total-hom-complex.
2. Fix i and set n = b-i+1. The good truncation T = truncLE n P has finite cohomology:
lem-weil-pbc-truncation-cohomology identifies it with that of K up to n and makes it zero
above n. The quotient C = P/T has zero terms below n, and 0 to T to P to C to 0 is degreewise
short exact.
3. In Hom^r(C,I), a coordinate with source degree p vanishes if p<n since C^p=0; otherwise
it vanishes if r>b-n since p+r>b. Hence Hom^r(C,I)=0 for r>b-n=i-1, so its cohomology in
degrees i and i+1 vanishes.
4. Restriction Hom(P^p,I^(p+r)) to Hom(T^p,I^(p+r)) is surjective by injectivity, and its
kernel is Hom(C^p,I^(p+r)). Only a-r <= p <= b-r contribute in degree r. Taking this finite
product gives a short exact sequence of total Hom complexes; precomposition commutes with
the signed differential of def-sc-module-total-hom-complex.
5. The long exact sequence (lem-weil-pbc-complex-ses-homology-long-exact) and the two
vanishings identify H^i RHom(K,L) with H^i RHom(QT,L).
6. Apply lem-trf-bounded-above-coherent-rhom with upper bound n on QT and lower bound a on
L. Both have finite cohomology by the hypotheses and step 2. It gives finite generation
of H^i RHom(QT,L), and step 5 transfers this to H^i RHom(K,L). No bound on K was used. -/
theorem coherent_rhom_finite_injective_dimension
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (RingSiteModules A)]
    (K L : DerivedCategory (RingSiteModules A))
    (hK : ∀ i : ℤ, Module.Finite A
      (((homologyFunctor (RingSiteModules A) i).obj K).val.obj (op ⟨PUnit.unit⟩)))
    (hL : ∀ i : ℤ, Module.Finite A
      (((homologyFunctor (RingSiteModules A) i).obj L).val.obj (op ⟨PUnit.unit⟩)))
    (hI : ∃ I : CochainComplex (RingSiteModules A) ℤ,
      (∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero (I.X q)) ∧
      (∀ q : ℤ, Injective (I.X q)) ∧ Nonempty (DerivedCategory.Q.obj I ≅ L)) :
    ∀ i : ℤ, Module.Finite A
      (((homologyFunctor (RingSiteModules A) i).obj
        ((derivedInternalHomOfUniverses.{u, u, u, w} ⊥
          (CochainComplex.onePointRingSheaf A)).obj (op K, L))).val.obj
            (op ⟨PUnit.unit⟩)) := by
  sorry

end DerivedCategory
