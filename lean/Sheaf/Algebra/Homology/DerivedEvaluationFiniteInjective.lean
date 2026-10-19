/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.Algebra.Homology.TorAmplitudeFlatModel
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-! # Derived evaluation with finite injective dimension

Source: Stacks Project, More on Algebra, Tags 0A67 and 0A69
(blueprint: lem-trf-derived-evaluation-finite-injective).

The canonical map is transposed using the recorded evaluation-normalized adjunction.
The theorem asserts its invertibility and its naturality in all three arguments.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace DerivedCategory

/-- The transpose of evaluation and composition, using the normalized derived adjunction.
Source: Stacks 0A67 (blueprint: lem-trf-derived-evaluation-finite-injective). -/
def finiteInjectiveEvaluation (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (RingSiteModules R)]
    (K L M : DerivedCategory (RingSiteModules R)) :
    (SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) L).obj M ⊗ K ⟶
      (SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R)
        ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) K).obj L)).obj M :=
  (SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf R)
    ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) K).obj L)).homEquiv _ M
      ((α_ _ _ _).hom ≫
        _ ◁ ((β_ K _).hom ≫
          (SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf R) K).counit.app L) ≫
        (SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf R) L).counit.app M)

/-- Derived evaluation is invertible under the three finiteness hypotheses.
Source: Stacks Project, Tag 0A69 (blueprint: lem-trf-derived-evaluation-finite-injective).

Proof:
1. The canonical evaluation map of lem-trf-derived-evaluation-canonical-map gives an exact
natural comparison from F(A) = RHom(L,M) tensor A to G(A) = RHom(RHom(A,L),M).
2. Choose bounded injective representatives J,I of L,M, with J zero above u and I zero
below v. They are K-injective by lem-weil-pbc-dplus-injective-representative. Use the
standard truncation triangle A_n to K to E_n, where A_n = truncLE n K and E_n has a
representative B_n zero below n+1, by def-sbc-standard-tstructure-derived-category and
lem-weil-heart-short-exact-triangles.
3. Every A_n is pseudo-coherent. The bounded-below property of L and finite injective
dimension of M allow lem-trf-derived-evaluation-pseudocoherent to make e(A_n) invertible.
4. By lem-pc-module-tor-amplitude-flat-model the fixed Tor interval [a,b] supplies a flat
representative P of RHom(L,M) supported there. It is K-flat by
lem-pc-module-bounded-flat-kflat. The total tensor of P and B_n is zero below n+1+a.
5. The Hom-complex formula of def-pur-derived-internal-hom bounds Hom(B_n,J) above by
u-n-1 and Hom(Hom(B_n,J),I) below by n+1+v-u. Thus both tails have zero cohomology in
degrees at most n-c for c = max(-a,u-v), independent of n.
6. Fix d and choose n at least d+c. The long exact sequences of
lem-sf-derived-homology-long-exact identify degree d of F(A_n),F(K) and G(A_n),G(K).
Naturality (lem-weil-pbc-derived-cohomology-ladder) makes H^d(e(K)) conjugate to H^d(e(A_n)).
It is invertible for every d, hence e(K) is invertible by
lem-weil-pbc-unbounded-derived-iso-cohomology. Naturality in all three variables follows
from the evaluation and composition construction, before the finiteness assumptions. -/
theorem isIso_finiteInjectiveEvaluation
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (RingSiteModules R)]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (K L M : DerivedCategory (RingSiteModules R))
    (hL : ∃ J : CochainComplex (RingSiteModules R) ℤ,
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (J.X i)) ∧
      (∀ i : ℤ, Injective (J.X i)) ∧ Nonempty (Q.obj J ≅ L))
    (hM : ∃ I : CochainComplex (RingSiteModules R) ℤ,
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (I.X i)) ∧
      (∀ i : ℤ, Injective (I.X i)) ∧ Nonempty (Q.obj I ≅ M))
    (hTor : ∃ a b : ℤ, a ≤ b ∧ ∀ (N : RingSiteModules R) (j : ℤ),
      j < a ∨ b < j → IsZero ((homologyFunctor (RingSiteModules R) j).obj
        ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) L).obj M ⊗
          (singleFunctor (RingSiteModules R) 0).obj N)))
    (hK : ∀ (P : CochainComplex (RingSiteModules R) ℤ), Nonempty (Q.obj P ≅ K) →
      ∀ n : ℤ, IsPseudoCoherent (A := R) (Q.obj
        (((SheafOfModules.forget
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf R)) ⋙
          PresheafOfModules.evaluation
            ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (CochainComplex.onePointRingSheaf R)).obj
            (op ⟨PUnit.unit⟩)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (P.truncLE n)))) :
    IsIso (finiteInjectiveEvaluation R K L M) ∧
      (∀ (K' L' M' : DerivedCategory (RingSiteModules R))
        (f : K ⟶ K') (l : L' ⟶ L) (m : M ⟶ M'),
        ((SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
          (l.op, m) ⊗ₘ f) ≫ finiteInjectiveEvaluation R K' L' M' =
        finiteInjectiveEvaluation R K L M ≫
          (SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
            (X := (op ((SignedRingedHom.hom ⊥
              (CochainComplex.onePointRingSheaf R) K).obj L), M))
            (Y := (op ((SignedRingedHom.hom ⊥
              (CochainComplex.onePointRingSheaf R) K').obj L'), M'))
            (((SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
              (f.op, l)).op, m)) := by
  sorry

end DerivedCategory
