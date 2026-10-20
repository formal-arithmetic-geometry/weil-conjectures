/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.Paper.EtaleHomFiniteTorAmplitude
import Sheaf.Paper.ConstructibleHomComparison

/-!
# Finite-Tor constructible pro-etale internal Hom without separatedness

Source: Weil conjectures blueprint, `thm-sf-hom-ctf` and
`thm-sf-hom-comparison-constructible`, main-20261015, sec-smooth-purity/sk-lem-sp-tower;
the domain argument for trace-class exceptional internal-Hom exchange
(blueprint: lem-trf-proetale-internal-hom-ctf).

The statement uses the intrinsic constant-ring module presentation of the recorded
finite-Tor predicate and the ambient Hom-complex localization on the small pro-etale site.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Ambient derived internal Hom preserves finite-Tor bounded constructibility on a
finite-type scheme over the fixed algebraic closure of a finite field.
Source: blueprint `thm-sf-hom-ctf` and `thm-sf-hom-comparison-constructible`,
main-20261015, sec-smooth-purity/sk-lem-sp-tower
(blueprint: lem-trf-proetale-internal-hom-ctf).

Proof:
1. Since l differs from the characteristic prime, it is invertible on T. By
lem-sf-proetale-constructible-origin(ii), descend K,L to bounded constructible etale
objects K',L'. Choose ordered Tor intervals [a,b] and [c,d] for K,L. They descend to
K',L' by lem-sf-comparison-tor-amplitude(ii); boundedness implies boundedness below.
2. Apply lem-fin-finite-type-fibre-dimension-bound to the structure morphism to Spec k.
The base is quasi-compact and its unique fibre is T, giving a nonnegative bound m
on the dimension of T. Empty T is allowed.
3. Apply the general clause of thm-sf-hom-ctf to K',L'. Their etale derived Hom H'
is bounded constructible with Tor amplitude [c-b-2m,d-a+2m]. This clause requires
neither separatedness nor site-perfectness.
4. By thm-sf-hom-comparison-constructible the pullback of H' is the ambient pro-etale
Hom of the pullbacks. Apply the bifunctor def-pur-derived-internal-hom to the chosen
input isomorphisms to identify this with the displayed Hom of K,L.
5. By lem-sf-comparison-tor-amplitude(i), the pullback of H' is bounded constructible
with the same Tor interval. Cohomology and derived tensor preserve isomorphisms, so
transport these properties along step 4. This proves membership in D^b_ctf. -/
theorem finiteCoefficient_derivedInternalHom_ctf_proEtale
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    (K L : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n))
    (_hK : finiteTorConstructible l E n hn T K)
    (_hL : finiteTorConstructible l E n hn T L) :
    finiteTorConstructible l E n hn T
      ((derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology T)
        (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))).obj (op K, L)) := by
  sorry

end WeilConjectures
