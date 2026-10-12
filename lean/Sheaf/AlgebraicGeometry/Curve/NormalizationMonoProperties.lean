/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Cokernels of monomorphisms in the normalization comparison

Source: the normalization exact-sequence blueprint, unit `sk-thm-p1`.
This module isolates the constructibility and support calculation, after the comparison
monomorphism has been constructed from the adjunction unit and finite/open comparison.
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The cokernel of any monomorphism between the two normalization comparison sheaves
is constructible and vanishes on the dense isomorphism locus.

Source: `sec-proper-base-change/sk-thm-p1/lemma-weil-pbc-normalization-exact-sequence.md`,
construction of the cokernel and its finite support.
(blueprint: lem-weil-pbc-normalization-mono-cokernel)

Proof: Write R = Λ/ℓΛ. The curve X is Noetherian since it is of finite type over k;
X' is Noetherian since ν is finite. The constant R-sheaves are finite locally constant:
R is cyclic as a Λ-module. Extension by zero along j and j' preserves constructibility,
using the two strata U and its closed complement, respectively U' and its complement.
Finite direct image preserves constructibility on a Noetherian scheme, as follows from
finite base change and the finite geometric-fibre stalk formula. For the passage from
finite set sheaves to module sheaves, all operations factor through the finite ring R:
extension by zero and finite direct image preserve ℓ-annihilation, and a finite set
trivialization can be refined to trivialize the finitely many R-operations. Thus both
source and target of α are constructible. Refine their finite stratifications to a common one;
the cokernel of a morphism of finite locally constant module sheaves on each stratum
is finite locally constant (trivialise the morphism étale-locally and take its module
cokernel). Exact inverse image identifies this with the restriction of cokernel α.
This proves constructibility without imposing Noetherianity on Λ.

Over V, finite base change and ν|V being an isomorphism identify the two sheaves with
the same extension-by-zero constant R-sheaf on U ∩ V. At a geometric point in U ∩ V,
the restricted map α is an injection between two copies of the finite set R, hence
is a bijection. At a point outside U both stalks vanish. Pullback preserves monos,
and geometric stalks detect isomorphisms, so V^*α is an isomorphism. Pullback also
preserves cokernels; consequently V^*(cokernel α) is zero. This argument applies to
any mono α, not just the canonical diagonal. Finiteness of R is essential for this
last argument; no such general claim is made for infinite coefficient sets. -/
theorem normalization_mono_properties {k : Type u} [Field k] [IsAlgClosed k]
    {X X' U U' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (ν : X' ⟶ X) [IsFinite ν] [Surjective ν] (V : X.Opens) (hV : Dense (V : Set X))
    [IsIso (ν ∣_ V)] (j : U ⟶ X) [IsOpenImmersion j] {j' : U' ⟶ X'}
    [IsOpenImmersion j'] {ν' : U' ⟶ U} (hj : IsPullback j' ν' ν j) (ℓ : ℕ)
    [Fact ℓ.Prime] [Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})]
    (α : (j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ) ⟶
        (ν)_*[ModuleCat.{u + 1} Λ].obj
          ((j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ)))
    (hα : Mono α) : Scheme.IsConstructibleSheaf (cokernel α) ∧
      IsZero ((V.ι)^*[ModuleCat.{u + 1} Λ].obj (cokernel α)) := by
  sorry
end AlgebraicGeometry
