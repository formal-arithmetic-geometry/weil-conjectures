module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.OpenFlatLocus
import WeilConjectures.AlgebraicGeometry.AffineFlatModuleDescent

/-! # Flatness modulo a directed union of ideals descends to a quotient

Source: Stacks Project, Flatness, Tags 05MK and 05MN (2), specialized to quotient local
bases; More on Algebra, Tag 05LT, essentially finitely presented case
(blueprint: lem-sfb-fp-quotient-flatness-directed-limit).
-/

@[expose] public section

set_option autoImplicit false

universe u v w p l

open scoped TensorProduct

namespace Module

/-- Flatness of `P / JP` descends to `P / (J i)P` for one member of a nonempty directed
family of ideals of the local base. The algebra `B` is exhibited as a localization of the
finitely presented `A`-algebra `C`; `P` is finitely presented over `B`, not over `A`.

The union ideal is `⨆ i, J i`: for a nonempty directed family its underlying set is the
union, by `Submodule.coe_iSup_of_directed`. For every ideal `K`, the quotient `P / KP` is
encoded by `(A ⧸ K) ⊗[A] P`. The canonical equivalence
`TensorProduct.quotTensorEquivQuotSMul P K` sends `(a + K) ⊗ x` to the class of `a • x`
in `P ⧸ (K • (⊤ : Submodule A P))`; thus `KP` consists of finite sums of these products.
The tensor's left scalar action is the canonical `A / K`-action on that quotient.

Source: Stacks Project, Flatness, Situation 05MK and Lemma 05MN (2); More on Algebra,
Lemma 05LT (blueprint: lem-sfb-fp-quotient-flatness-directed-limit).

Proof:
1. Choose a finite presentation matrix for `P` over `B`. Clear its finitely many
   denominators in `S` to a matrix over `C`; its cokernel `N` is finitely presented over
   `C`, and exact localization identifies `S⁻¹N` with `P`. Multiplying the presentation
   matrix by the common unit denominator does not change its image. This is the matrix
   construction of Tag 05N5, using lem-weil-pbc-localization-module-exact (Tag 00CS).
2. Let `q` be the inverse image in `C` of the maximal ideal of `B`. Every element of
   `C` outside `q` becomes a unit in the local ring `B`, so `B` identifies with `C_q`.
   Locality gives `JC ⊆ q`. The fraction maps identify `(C/JC)_(q/JC)` with `B/JB`
   and the corresponding localization of `N/JN` with `P/JP`, using
   lem-weil-pbc-localization-at-prime-of-quotient and the module localization definition.
3. By lem-weil-pbc-openness-of-flatness (Tag 00RC), the flat locus of `N/JN` over `A/J`
   is open in `Spec(C/JC)` and contains `q/JC`. Choose a principal neighborhood defined
   by an element `h` outside `q` inside this locus. Prime contraction under localization
   (lem-weil-pbc-localization-quotient-by-prime) and
   lem-sfb-base-flatness-maximal-localizations show that `(N/JN)[1/h]` is `A/J`-flat.
4. Put `D = C[1/h]` and `E = N[1/h]`. Adjoining an inverse of `h` adds one generator
   and one relation, so `D` is finitely presented over `A`; the localized matrix presents
   `E` over `D`. The quotient tensor maps `(a+K) ⊗ x ↦ ax+KE` identify reduction
   modulo each ideal `K` with base change to `A/K`. The fraction maps identify the
   limit reduction with `(N/JN)[1/h]`, which is flat by step 3.
5. Order the indices by inclusion of their ideals. Their quotient rings have colimit
   `A/J`: a map from `A` kills every `J i` exactly when it kills their union. Fix an
   index and pass to its cofinal tail. Apply lem-pc-affine-flat-module-descent (Tag
   02JO (3)) to the finite presentations of `D` and `E` reduced at this index, with
   first coefficient algebra the base ring itself. It gives an index `i` where
   `E/(J i)E` is flat over `A/(J i)`.
6. Since `h` becomes a unit in `B`, further localization identifies this module with
   `P/(J i)P`. Localization preserves injections by
   lem-weil-pbc-localization-module-exact; commuting localization with tensor products
   shows that tensoring with `P/(J i)P` preserves injections over `A/(J i)`, hence is
   flat by def-weil-pbc-flat-ring-map. No henselian or Noetherian assumption is used.
-/
theorem exists_flat_quotient_of_directed_iSup
    {A : Type u} {B : Type v} {C : Type w} {P : Type p} {L : Type l}
    [CommRing A] [CommRing B] [CommRing C] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [Algebra.FinitePresentation A C] (S : Submonoid C) [IsLocalization S B]
    [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]
    [Module.FinitePresentation B P] [Nonempty L]
    (J : L → Ideal A) (hJ : Directed (· ≤ ·) J)
    (hJmax : ∀ i : L, J i ≤ IsLocalRing.maximalIdeal A)
    (hflat : Module.Flat (A ⧸ (⨆ i : L, J i))
      ((A ⧸ (⨆ i : L, J i)) ⊗[A] P)) :
    ∃ i : L, Module.Flat (A ⧸ J i) ((A ⧸ J i) ⊗[A] P) := by
  sorry

end Module
