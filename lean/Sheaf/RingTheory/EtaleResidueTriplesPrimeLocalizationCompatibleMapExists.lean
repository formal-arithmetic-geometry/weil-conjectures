module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Compatible maps to prime-localized pointed etale triples

Source: Stacks Project, Tags 04GW, 00CP and 00U2 (3).
(blueprint: new-lem-sbc-etale-triples-prime-localization-compatible-map-exists)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Every pointed étale `R`-triple admits a compatible map into a pointed étale
`R_p`-triple. This is the localization construction used in the uniqueness
argument for compatible cocone legs.
Source: Stacks Project, Tags 04GW (pointed triples), 00CP (localization
universal property), and 00U2 (3) (etale base change). The construction below
is an agent-written consequence, valid for any field K, without separable closure.
(blueprint: new-lem-sbc-etale-triples-prime-localization-compatible-map-exists)

Proof: Put A = R_p and let f : B_s -> K be evaluation at s.q followed by s.phi.
Set M to be the image under s.alpha of the multiplicative subset R minus p,
and construct C = M^{-1}B_s, with canonical map beta : B_s -> C. The map
R -> C inverts R minus p, so it extends uniquely to a : A -> C. The standard
localization base-change identification C = A tensor_R B_s identifies a with
the base change of s.alpha; hence Spec(a) is etale by Tag 00U2 (3).

For r outside p, compatibility of s identifies f(s.alpha(r)) with evaluation
of r at p followed by chi. The evaluation has kernel p and the field map chi
is injective, so this value is nonzero, hence a unit of K. By Tag 00CP, f
extends to g : C -> K with g beta = f. The two maps g a and the specified
A-algebra map to K agree on R by hK and compatibility of s; uniqueness for
R -> A gives their equality.

Let Q = ker(g), a prime because K is a field. The injection C/Q -> K extends
to its fraction field by sending c/d to g(c)/g(d); this gives a residue-field
embedding phi_Q whose composite with C -> kappa(Q) is g. Transfer Q and this
embedding to Spec(C) using the canonical affine residue-field identification.
The contraction of Q under a is the kernel of the specified A -> K. By hpsi,
this map is evaluation at q followed by psi. Evaluation has kernel q, and psi
is injective, so the contraction is q. Thus (C, a, Q, phi_Q) is a pointed
etale A-triple t: its compatibility equation is g a = evaluation_q followed
by psi. Finally a composed with R -> A equals beta composed with s.alpha
by construction, and g beta = f is precisely the required pointing equation.
All objects here are explicit localizations, kernels and fraction maps. -/
theorem etaleResidueTriples_primeLocalization_compatible_map_exists
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (s : EtaleResidueTriples R p K χ) :
    ∃ (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ)
      (β : s.B ⟶ t.B),
      s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α ∧
      β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ := by
  sorry

end AlgebraicGeometry.Scheme
