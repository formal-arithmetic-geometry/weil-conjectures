/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Algebra.Category.ModuleCat.Free

/-!
# Cotangent and graded rigidity for complete local rings

Source: Stacks Project, Formal Deformation Theory, Tag 06GZ
(`lemma-surjective-cotangent-space`), and Artin's Axioms, Tag 07XH
(`lemma-approximate-versal`), proof after the dotted-arrow construction.
(blueprint: lem-sfb-complete-local-cotangent-graded-rigidity)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace IsLocalRing

/-- A local map of complete Noetherian local rings with fixed residue field is surjective
if its cotangent map is surjective, and is an isomorphism if all graded dimensions agree.
The quotient displayed in degree `j` is `m^j / m*m^j = m^j / m^(j+1)`. Its natural
`C/m`-module structure is transported along `eC.symm` (and similarly for `D`). Thus the
explicit `Module.compHom` arguments compute dimensions over the specified common field `k`.
The cotangent map is the canonical `Ideal.mapCotangent`, regarded as a map of abelian
groups via its integer-linear presentation; its underlying function is the same as that
of the induced `k`-linear map. No coefficient-field embedding in either ring is assumed.

Source: Stacks Project, Tag 06GZ, conditions (1)-(2), and Tag 07XH, proof after the
dotted-arrow construction.
(blueprint: lem-sfb-complete-local-cotangent-graded-rigidity)

Proof:
1. Put `J = (maximalIdeal C).map f`. Cotangent surjectivity says each element of `n`
   differs from the image of an element of `m` by an element of `n^2`, hence `n = J + n^2`.
2. Noetherianity (def-weil-pbc-noetherian-ring) makes `n/J` a finite `D`-module. The
   preceding equality gives `n*(n/J) = n/J`. Since the Jacobson radical of the local ring
   `D` is `n`, Nakayama (lem-weil-pbc-nakayama-jacobson) gives `n/J = 0`, so `J = n`.
3. Completeness (def-weil-pbc-adic-completion) gives precompleteness of `C` and
   `J`-adic Hausdorffness of `D`. The residue-field identity gives surjectivity of
   `C → D/J`. Apply lem-weil-pbc-complete-source-surjective-mod-ideal to get surjectivity
   of `f`.
4. Surjectivity and locality give `f(m) = n`. Lifting factors in each product shows
   `f(m^j) = n^j` for every positive `j`; degree zero is surjectivity of `f`. The induced
   maps `g_j : m^j/m^(j+1) → n^j/n^(j+1)` are surjective and are `k`-linear by the
   residue-field identity.
5. Each graded piece is finite-dimensional by Noetherianity. The kernels of `g_j`
   are finite-dimensional by lem-trf-vector-space-quotient-dimension. Apply
   lem-trf-finite-dimensional-short-exact-dimension to `0 → ker(g_j) → gr_j(C) → gr_j(D)
   → 0`. Equality of graded dimensions forces every kernel to have dimension zero,
   hence to vanish; thus each `g_j` is injective.
6. For `x ∈ ker(f)`, induction starting at `m^0 = C` and using injectivity of `g_j`
   gives `x ∈ m^j` for every `j`. Hausdorffness from completeness of `C` implies `x = 0`.
   Thus `f` is bijective and its inverse defines a ring equivalence whose ring map is `f`.
-/
theorem surjective_and_isomorphism_of_cotangent_surjective_of_complete
    (C : Type u) (D : Type v) (k : Type w)
    [CommRing C] [CommRing D] [Field k]
    [IsNoetherianRing C] [IsNoetherianRing D] [IsLocalRing C] [IsLocalRing D]
    [IsAdicComplete (maximalIdeal C) C] [IsAdicComplete (maximalIdeal D) D]
    (eC : ResidueField C ≃+* k) (eD : ResidueField D ≃+* k)
    (f : C →+* D) [IsLocalHom f]
    (hres : eD.toRingHom.comp (ResidueField.map f) = eC.toRingHom)
    (hcot : Function.Surjective
      (Ideal.mapCotangent (maximalIdeal C) (maximalIdeal D) f.toIntAlgHom
        (maximalIdeal_comap f).symm.le)) :
    Function.Surjective f ∧
      ((∀ j : ℕ,
        @Module.finrank k
          ((maximalIdeal C ^ j : Ideal C) ⧸
            (maximalIdeal C • ⊤ : Submodule C (maximalIdeal C ^ j : Ideal C))) _ _
          (@Module.compHom (C ⧸ maximalIdeal C) k _ _ _ inferInstance _ eC.symm.toRingHom) =
        @Module.finrank k
          ((maximalIdeal D ^ j : Ideal D) ⧸
            (maximalIdeal D • ⊤ : Submodule D (maximalIdeal D ^ j : Ideal D))) _ _
          (@Module.compHom (D ⧸ maximalIdeal D) k _ _ _ inferInstance _ eD.symm.toRingHom)) →
        ∃ e : C ≃+* D, e.toRingHom = f) := by
  sorry

end IsLocalRing
