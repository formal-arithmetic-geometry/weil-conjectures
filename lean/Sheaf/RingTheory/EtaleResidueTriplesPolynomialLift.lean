module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsSepClosed

/-! Polynomial lifting step for surjectivity of the pointed étale colimit.
(blueprint: lem-weil-pbc-etale-triples-colimit-polynomial-lift). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every element of `K` admits a monic polynomial over the colimit whose image has
that element as a simple root. Source: the coefficient-lifting and separability step
of Stacks Project, Tags 04GW and 00UH.

Proof: Put `C = c.pt` and let `F` be the image of `ψ` in `K`. If `ψ(x)` is nonzero,
`hunit` represents `x` by a unit of `C`; mapping its inverse gives the inverse of
`ψ(x)`. Thus `F` is a subfield, including inverse closure at zero. The identity
triple `(R, p, algebraMap κ(p) K)` exists because the identity morphism is étale.
Applying `hψ` to this triple shows that `F` contains the canonical image of `R`.
The isomorphism `Spec.residueFieldIso` identifies `κ(p)` with the residue field of
`R_p` and commutes with the canonical maps from `R`. Every residue class lifts to
an element of `R_p`, represented by `r/s` with `s` outside `p`. The class of `s`
is a unit, hence nonzero; its image in `K` is nonzero since field homomorphisms are
injective. Inverse closure therefore puts the image of every such fraction in `F`.
Consequently every element of `κ(p)` has its image in `K` lifted by `ψ`.

For `a₀ : K`, let `g = minpoly κ(p) a₀`. The separable-closure hypothesis gives
algebraicity and separability, so `g` is monic and separable and evaluates to zero
at `a₀`. Choose preimages in `C` of the images of its finitely many coefficients
below `n = g.natDegree`. The polynomial `X^n + ∑ i < n, C(b_i) * X^i` is monic and
maps under `ψ` to `g.map (algebraMap κ(p) K)`. This is also the construction in
`Polynomial.lifts_and_natDegree_eq_and_monic`. Its evaluation at `a₀` is zero.
Separability supplies `U*g + V*g.derivative = 1`; evaluating at `a₀` shows that
`g.derivative` evaluates to a nonzero element. Derivative and evaluation commute
with coefficient mapping, giving the same nonzero value for the lifted polynomial.
This proves both required evaluation conditions without an injective map `R → C`.
(blueprint: lem-weil-pbc-etale-triples-colimit-polynomial-lift) -/
theorem etaleResidueTriples_polynomial_lift
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c)
    (ψ : c.pt →+* K)
    (hψ : ∀ t, ψ.comp (c.ι.app t).hom =
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom)
    (hunit : ∀ x : c.pt, ψ x ≠ 0 → IsUnit x) :
    ∀ a₀ : K, ∃ f : Polynomial c.pt, f.Monic ∧
      f.eval₂ ψ a₀ = 0 ∧ f.derivative.eval₂ ψ a₀ ≠ 0 := by
  sorry

end AlgebraicGeometry.Scheme
