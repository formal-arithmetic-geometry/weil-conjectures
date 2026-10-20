/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Algebra.Homology.DerivedEvaluationCanonicalMap
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.ModuleHomComplex
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Pseudo-coherent derived evaluation

Source: Stacks Project, More on Algebra, Tag 0A68,
lemma-internal-hom-evaluate-isomorphism, case (2)
(blueprint: lem-trf-derived-evaluation-pseudocoherent).

The one-object bottom-topology ringed site is the recorded presentation of ordinary
R-modules. Pseudo-coherence is the existing ordinary-module predicate, applied after
evaluation at the unique object. Boundedness of L is cohomological; the finite
injective dimension of M is expressed by a bounded injective representative.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedCategory

/-- Pseudo-coherence, a lower cohomological bound on L and finite injective
dimension of M make the specified canonical evaluation map invertible.
Source: Stacks Project, More on Algebra, Tag 0A68, case (2)
(blueprint: lem-trf-derived-evaluation-pseudocoherent).

Proof:
1. Choose a bounded-above finite-free representative P of K, zero above u, using
def-pc-ring-pseudo-coherent-complex. Choose a bounded injective representative I
of M, zero outside [a,b]. By lem-weil-pbc-ring-modules-enough-injectives and
lem-weil-pbc-dplus-injective-representative, choose a bounded-below injective
representative J of L, zero below l. Both I and J are K-injective.
2. Finite free modules are flat, since tensor with them is a finite sum of the
identity. Thus P is K-flat by lem-pc-module-bounded-flat-kflat, in the categorical
convention of def-pc-module-kflat-complex. By lem-pc-source-kflat-module-tensor-model
and symmetry, the source is represented by T = Tot(Hom(J,I) tensor P).
3. By def-pur-derived-internal-hom, the target is represented by
B = Hom(Hom(P,J),I). These are the product total Hom complexes of
def-sc-module-total-hom-complex, with differential d(f)=d_target f-(-1)^|f| f d_source.
4. In degree n only triples p+r+s=n with a≤p≤b, r≤-l and s≤u contribute.
Consequently n-b+l≤s≤u and n-b-u≤r≤-l. Also Hom(P,J)^k has only l-k≤s≤u
nonzero factors. Thus all products become finite sums after removing zeros.
Finite distributivity identifies T^n and B^n with the sums of, respectively,
Hom(J^(-r),I^p) tensor P^s and Hom(Hom(P^s,J^(-r)),I^p).
5. Define E on each triple by g tensor x ↦ (f ↦ (-1)^(s(r+1)) g(f(x))).
The three differential terms require epsilon(p,r,s)=epsilon(p+1,r,s),
epsilon(p,r,s)=(-1)^s epsilon(p,r-1,s), and
epsilon(p,r,s+1)=(-1)^(r+1) epsilon(p,r,s), all immediate from the exponent.
6. This is the canonical map of lem-trf-derived-evaluation-canonical-map.
Writing h=p+r and k=-r-s, the adjunction transpose contributes the sign
(-1)^(kh+kn)=(-1)^(ks)=(-1)^(s(r+1)). The same computation after a K-flat
replacement of the inner Hom (lem-pc-kflat-resolution) identifies the derived
transpose, using the tensor and Hom models above.
7. For a finite basis e_i of P^s, let iota_i(v) send e_j to delta_ij v.
The inverse to the unsigned component sends beta to sum_i (beta ∘ iota_i) tensor e_i.
One composite is f ↦ sum_i beta(iota_i(f(e_i)))=beta(f); the other follows by
expanding x in its basis. Multiplication by the sign preserves invertibility,
so every E^n is invertible.
8. The chain-map equation for E implies the chain-map equation for its component
inverses. Hence E is a complex isomorphism, and localization preserves its inverse
(def-weil-abstract-derived-category). The models and step 6 identify its image
with precisely the specified canonical derived evaluation. -/
theorem isIso_evaluation_of_isPseudoCoherent
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (RingSiteModules R)]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (K L M : evaluationDerivedCategory R)
    (hK : ∃ P : CochainComplex (RingSiteModules R) ℤ,
      Nonempty (Q.obj P ≅ K) ∧
      IsPseudoCoherent (A := R) (Q.obj
        (((SheafOfModules.forget
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf R)) ⋙
          PresheafOfModules.evaluation
            ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (CochainComplex.onePointRingSheaf R)).obj
            (op ⟨PUnit.unit⟩)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
    (hL : ∃ n : ℤ, L.IsGE n)
    (hM : ∃ I : CochainComplex (RingSiteModules R) ℤ,
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (I.X i)) ∧
      (∀ i : ℤ, Injective (I.X i)) ∧ Nonempty (Q.obj I ≅ M)) :
    IsIso ((derived_evaluation_canonical_map R).choose K L M) := by
  sorry

end DerivedCategory
