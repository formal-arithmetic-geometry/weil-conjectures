/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.AdicCompletion.Exactness

/-!
# Supported pseudo-coherent Ext and completion of coefficients

Source: Stacks Project, Tags 0DYJ, 0A6A(3), 00MA and 00MB
(blueprint: lem-sfb-supported-complex-ext-completion).

The quotient tower starts with `N / I N`, at index zero. Naturality of the first
comparison is expressed after every limit projection, which jointly detect equality.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedCategory

/-- The coefficient functor `M ↦ Hom(K, M[i])`, with its canonical A-module structure.
Source: Stacks Project, Tag 0DYJ
(blueprint: lem-sfb-supported-complex-ext-completion). -/
noncomputable def supportedExtFunctor {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    ModuleCat.{max u v} A ⥤ ModuleCat.{w} A :=
  singleFunctor (ModuleCat.{max u v} A) 0 ⋙
    shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i ⋙
      (linearCoyoneda A (DerivedCategory (ModuleCat.{max u v} A))).obj (op K)

/-- The module quotient tower; index n denotes the power n+1.
Source: Stacks Project, Tag 0DYJ
(blueprint: lem-sfb-supported-complex-ext-completion). -/
noncomputable abbrev supportedExtCoefficientTower {A : Type u} [CommRing A]
    (I : Ideal A) (N : ModuleCat.{max u v} A) : ℕᵒᵖ ⥤ ModuleCat.{max u v} A :=
  Functor.ofOpSequence (X := fun n : ℕ ↦
    ModuleCat.of A (N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N)))
      (fun n ↦ ModuleCat.ofHom (AdicCompletion.transitionMap I N (Nat.le_succ (n + 1))))

/-- The quotient coefficient tower after applying `Hom(K, -[i])`.
Source: Stacks Project, Tag 0DYJ
(blueprint: lem-sfb-supported-complex-ext-completion). -/
noncomputable abbrev supportedExtQuotientTower {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (N : ModuleCat.{max u v} A) : ℕᵒᵖ ⥤ ModuleCat.{w} A :=
  supportedExtCoefficientTower I N ⋙ supportedExtFunctor K i

/-- The cone of all quotient-induced maps from `Hom(K, N[i])`.
Source: Stacks Project, Tag 0DYJ
(blueprint: lem-sfb-supported-complex-ext-completion). -/
noncomputable def supportedExtQuotientCone {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (N : ModuleCat.{max u v} A) : Cone (supportedExtQuotientTower I K i N) :=
  (supportedExtFunctor K i).mapCone
    { pt := N
      π := NatTrans.ofOpSequence
        (fun n ↦ ModuleCat.ofHom (Submodule.mkQ (I ^ (n + 1) • ⊤ : Submodule A N)))
        (fun n ↦ by
          simp only [supportedExtCoefficientTower, Functor.const_obj_map,
            Functor.ofOpSequence_map_homOfLE_succ]
          rfl) }


/-- The ordinary completion unit, regarded as a morphism of A-modules.
Source: Stacks Project, Tags 0DYJ and 00MA
(blueprint: lem-sfb-supported-complex-ext-completion). -/
noncomputable def supportedExtCompletionUnit {A : Type u} [CommRing A]
    (I : Ideal A) (N : ModuleCat.{max u v} A) :
    N ⟶ ModuleCat.of A (AdicCompletion I N) :=
  ModuleCat.ofHom (AdicCompletion.of I N)

/-- The coefficient morphism on completions, with scalars restricted to A.
Source: Stacks Project, Tag 00MA
(blueprint: lem-sfb-supported-complex-ext-completion). -/
noncomputable def supportedExtCompletionMap {A : Type u} [CommRing A]
    (I : Ideal A) {N N' : ModuleCat.{max u v} A} (f : N ⟶ N') :
    ModuleCat.of A (AdicCompletion I N) ⟶ ModuleCat.of A (AdicCompletion I N') :=
  ModuleCat.ofHom ((AdicCompletion.map I f.hom).restrictScalars A)

/-- The coefficient morphism on quotients, with scalars restricted to A.
Source: Stacks Project, Tag 0DYJ
(blueprint: lem-sfb-supported-complex-ext-completion). -/
noncomputable def supportedExtQuotientMap {A : Type u} [CommRing A]
    (I : Ideal A) {N N' : ModuleCat.{max u v} A} (f : N ⟶ N') (n : ℕ) :
    (supportedExtCoefficientTower I N).obj (op n) ⟶
      (supportedExtCoefficientTower I N').obj (op n) :=
  ModuleCat.ofHom ((f.hom.reduceModIdeal (I ^ (n + 1))).restrictScalars A)

/-- The canonical A-linear map to the inverse limit of quotient-coefficient Ext groups.
Its coordinate at `n` is induced by `N → N/I^(n+1)N`.
Source: Stacks Project, Tag 0DYJ
(blueprint: lem-sfb-supported-complex-ext-completion). -/
noncomputable def supportedExtQuotientComparison {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (N : ModuleCat.{max u v} A) :
    (supportedExtFunctor K i).obj N ⟶ limit (supportedExtQuotientTower I K i N) :=
  limit.lift _ (supportedExtQuotientCone I K i N)

set_option maxHeartbeats 600000 in
-- The four clauses elaborate several derived Hom and inverse-limit functors.
/-- Supported pseudo-coherent Ext is unchanged by completing finite coefficients.
The first two clauses assert invertibility of the two canonical A-linear maps.
The last two clauses give naturality, for the quotient limit in every coordinate.
Source: Stacks Project, Tags 0DYJ, 0A6A(3), 00MA and 00MB
(blueprint: lem-sfb-supported-complex-ext-completion).

Proof:
1. Represent K by a bounded-above finite free complex P, using
   def-pc-ring-pseudo-coherent-complex. Its terms are projective. By
   lem-sc-bounded-above-projective-kprojective and
   lem-coef-kprojective-derived-hom-bijection, E^i(K,M) is the degree-i cohomology
   of Hom(P,M[0]), naturally in M. In degree j this complex is Hom(P^(-j),M).
2. For finite M these terms, their cycles, and their cohomology H are finite, by
   lem-weil-pbc-noetherian-submodule-finite. The support hypothesis and
   lem-weil-pbc-finite-module-support-annihilator put I in the radical of Ann(H),
   using lem-weil-pbc-zero-locus-eq-iff-radical-eq. Then
   lem-weil-pbc-fg-ideal-radical-power gives I^t H = 0, so H equals its completion.
3. Apply lem-sfb-finite-short-complex-adic-cohomology-limit to the three Hom terms
   in degrees i-1, i and i+1. Finite bases identify their quotients with the Hom
   complex for N/I^n N, compatibly with differentials. This gives exactly the
   quotient comparison, since each coordinate is reduction of a cycle.
4. Apply lem-weil-pbc-completion-exact-finite-modules to the four short exact
   sequences defining cycles, boundaries, their quotient, and the image of the
   outgoing differential. More explicitly, with C = Hom(P,N[0]), Z = ker(d^i),
   B = im(d^(i-1)), and D = im(d^i), these are 0 → Z → C^i → D → 0,
   0 → D → C^(i+1) → C^(i+1)/D → 0, 0 → B → Z → H → 0, and
   0 → ker(d^(i-1)) → C^(i-1) → B → 0. All their terms are finite.
   Thus the completed cycles are Z-hat and the boundaries are B-hat, so the
   completed complex has cohomology H-hat. Finite bases identify its terms
   and differentials with Hom(P,N-hat[0]). The coefficient map induces
   H → H-hat, invertible by step 2.
5. Postcomposition by N → N' commutes with reduction and completion on every
   coordinate. These identities pass to cohomology and give both naturality squares.
-/
theorem supportedComplex_ext_completion {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{max u v} A))
    (hK : IsPseudoCoherent K) (a : ℤ)
    (hSupport : ∀ (M : ModuleCat.{max u v} A), Module.Finite A M →
      ∀ (i : ℤ), a ≤ i → ∀ (p : Ideal A) [p.IsPrime], ¬ I ≤ p →
        Subsingleton (LocalizedModule p.primeCompl ((supportedExtFunctor K i).obj M))) :
    (∀ (N : ModuleCat.{max u v} A), Module.Finite A N → ∀ (i : ℤ), a ≤ i →
      IsIso (supportedExtQuotientComparison I K i N)) ∧
    (∀ (N : ModuleCat.{max u v} A), Module.Finite A N → ∀ (i : ℤ), a ≤ i →
      IsIso ((supportedExtFunctor K i).map
        (supportedExtCompletionUnit I N))) ∧
    (∀ (N N' : ModuleCat.{max u v} A), Module.Finite A N → Module.Finite A N' →
      ∀ (f : N ⟶ N') (i : ℤ), a ≤ i → ∀ (n : ℕ),
        supportedExtQuotientComparison I K i N ≫
            limit.π (supportedExtQuotientTower I K i N) (op n) ≫
            (supportedExtFunctor K i).map
              (supportedExtQuotientMap I f n) =
          (supportedExtFunctor K i).map f ≫ supportedExtQuotientComparison I K i N' ≫
            limit.π (supportedExtQuotientTower I K i N') (op n)) ∧
    (∀ (N N' : ModuleCat.{max u v} A), Module.Finite A N → Module.Finite A N' →
      ∀ (f : N ⟶ N') (i : ℤ), a ≤ i →
        (supportedExtFunctor K i).map (supportedExtCompletionUnit I N) ≫
            (supportedExtFunctor K i).map
              (supportedExtCompletionMap I f) =
          (supportedExtFunctor K i).map f ≫
            (supportedExtFunctor K i).map (supportedExtCompletionUnit I N')) := by
  sorry

end DerivedCategory
