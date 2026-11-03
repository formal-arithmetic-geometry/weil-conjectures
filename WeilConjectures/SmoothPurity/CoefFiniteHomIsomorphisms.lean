/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Trace
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionConstructible
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes

/-! # A proper subargument of finite coefficient internal-Hom comparison

Source: the latest blueprint `thm-coef-finite-hom` and its proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Invertibility of the two specified native scalar-Hom comparisons.

Source: the latest blueprint `thm-coef-finite-hom.proof.md`, the constructible
stratum argument and its final finite-site transport
(blueprint: lem-coef-native-hom-isomorphisms).

Proof: normalize the native derived scalar tensorator against the ordinary
scalar adjunction on flat-term K-flat resolutions. The cochain counit formula
identifies this tensorator with the normalized adjoint-chosen one, and the
unique evaluation transpose identifies the actual Hom maps. Work first etale.
Finite type over the field makes X Noetherian. Choose a finite constructible
stratum filtration of the first input. Its restrictions are locally bounded
finite-projective complexes, by finite-Tor truncation. Localization triangles
reduce to a stratum extension s_!P. Factor s as an open immersion j followed by
a closed immersion g and use the closure-factorization isomorphism. Put
N = j^* Rg^! M and Q = RHom(P,N). The pre-duality closed exceptional scalar
comparison makes N ctf and identifies N_B with s_B^! M_B, with its specified
counit equation; Hom preservation makes Q ctf. On finite-projective summands
P = e A^r, scalar extension and duality give the same transposed idempotent
e^t on B^r. Evaluation matrices, signed differentials and finite sums agree,
so the evaluation-defined scalar-Hom map is invertible for perfect P.
Internal adjunction expresses RHom(s_!P,M) as Rs_*Q. Apply the ctf direct-image
scalar comparison, the perfect Hom calculation and the exceptional scalar
comparison, then internal adjunction over B. The support scalar comparison
identifies its first input with (s_!P)_B. The pairing-change theorem, using the
specified exceptional counit equation, identifies this invertible composite
with etaleHom. Its isomorphism locus in the first variable is thick, so the
finite filtration proves etale invertibility. For pro-etale inputs, take
bounded constructible etale origins and reflect their Tor intervals. The
canonical finite-ring Hom site comparisons are invertible. Normalize the
scalar/site tensor square on the same flat resolutions. Its evaluation
transpose square identifies proHom with the conjugate of etaleHom. Transport
invertibility through the origins. This proves invertibility of the fixed
maps, without replacing them by unrelated isomorphisms. -/
theorem finiteCoefficientHomIsomorphisms
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (hell : (ell : k) ≠ 0)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    (hA : ∃ n : ℕ, (ell ^ n : A) = 0)
    (hB : ∃ n : ℕ, (ell ^ n : B) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    finiteHomLaw_vEtale_iso X φ ∧ finiteHomLaw_vPro_iso X φ := by
  sorry

end WeilConjectures
