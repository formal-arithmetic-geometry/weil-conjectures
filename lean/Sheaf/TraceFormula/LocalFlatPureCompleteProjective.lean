module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
import Sheaf.RingTheory.CompletionFlatMittagLeffler
import Sheaf.RingTheory.FlatCompletionUniversallyInjective
import Sheaf.RingTheory.IsMittagLeffler
import Sheaf.SecTraceFormula.CountableFlatMittagLefflerProjective

/-!
# Projectivity over a complete Noetherian base from a projective reduction

Source: Stacks Project, Commutative Algebra, Tag 05DP, `lemma-flat-pure-over-complete-projective`.
(blueprint: lem-trf-local-flat-pure-complete-projective)

The fibre is the canonical tensor product `M ⊗[A] κ(p)`, equipped with its induced
`B`-module structure. The reduction modulo `I` is represented by the canonical
base-change module `(A/I) ⊗[A] M`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

/-- Projectivity over a complete Noetherian base from a projective reduction.
(blueprint: lem-trf-local-flat-pure-complete-projective)


Source: Stacks Project, Commutative Algebra, Tag 05DP, `lemma-flat-pure-over-complete-projective`.
The hypotheses are: `A` is Noetherian and `I`-adically complete; `A → B` is of finite type;
`M` is finite over `B` and flat over `A`; the canonical reduction
`(A/I) ⊗[A] M` is projective over `A/I`; and for every prime `p` of `A`, every
prime `q` of `B` over `p` which is an element-annihilator associated prime of the
canonical fibre `M ⊗[A] κ(p)`, the ideal `I B + q` is proper. The conclusion is that
`M` is projective over `A`.

The tensor products are Mathlib's universal tensor products. The `B`-action on the
fibre is the canonical action induced from the `B`-action on `M` and the scalar
extension along `A → B`.
-/
theorem local_flat_pure_complete_projective
    (A : Type u) (B : Type v) (M : Type w) [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] (I : Ideal A) [IsNoetherianRing A]
    [IsAdicComplete I A] [Algebra.FiniteType A B] [Module.Finite B M]
    [Module.Flat A M]
    (hproj : Module.Projective (A ⧸ I)
      (TensorProduct A (A ⧸ I) M))
    (hassoc : ∀ (p : Ideal A) (hp : p.IsPrime),
      letI := hp
      ∀ (q : Ideal B) (hq : q.IsPrime),
        letI := hq
        q.comap (algebraMap A B) = p →
        q ∈ RingTheory.annihilatorAssociatedPrimes B
          (TensorProduct A M p.ResidueField) →
        Ideal.map (algebraMap A B) I ⊔ q ≠ ⊤) :
    Module.Projective A M := by
  sorry

end
