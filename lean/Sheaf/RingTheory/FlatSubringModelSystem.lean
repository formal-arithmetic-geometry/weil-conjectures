module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FiniteType
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import WeilConjectures.RingTheory.ColimitFlatRingMap

/-! # Compatible eventually flat models over finitely generated integer subalgebras

Source: Stacks Project, Tags 05FE, 05FD, 05N9 (1), and 02JO (3).
(blueprint: lem-trf-flat-subring-model-system)

The base change is written with the base ring first, using Mathlib's convention.
The stage helpers supply the canonical algebra structure from an inclusion of subalgebras.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Algebra

/-- The canonical tensor model at a larger integer subalgebra, in base-first order.
Source: Stacks Project, Tag 05N9 (1). (blueprint: lem-trf-flat-subring-model-system) -/
def flatSubringModelStage {R : Type u} [CommRing R]
    (i j : Subalgebra ℤ R) (hij : i ≤ j) (B : Type u) [CommRing B] [Algebra i B] :
    CommRingCat.{u} :=
  letI := (Subalgebra.inclusion hij).toRingHom.toAlgebra
  CommRingCat.of (j ⊗[i] B)

/-- The structure map of the canonical tensor model, sending `r` to `r ⊗ 1`.
Source: Stacks Project, Tag 05N9 (1). (blueprint: lem-trf-flat-subring-model-system) -/
def flatSubringModelStructure {R : Type u} [CommRing R]
    (i j : Subalgebra ℤ R) (hij : i ≤ j) (B : Type u) [CommRing B] [Algebra i B] :
    j →+* flatSubringModelStage i j hij B :=
  letI := (Subalgebra.inclusion hij).toRingHom.toAlgebra
  Algebra.TensorProduct.includeLeftRingHom

/-- The canonical algebra structure on the tensor model over its stage ring.
Source: Stacks Project, Tag 05N9 (1). (blueprint: lem-trf-flat-subring-model-system) -/
instance flatSubringModelAlgebra {R : Type u} [CommRing R]
    (i j : Subalgebra ℤ R) (hij : i ≤ j) (B : Type u) [CommRing B] [Algebra i B] :
    Algebra j (flatSubringModelStage i j hij B) :=
  (flatSubringModelStructure i j hij B).toAlgebra

/-- Pure tensors in the canonical model, with the stage-ring factor first.
Source: Stacks Project, Tag 05N9 (1). (blueprint: lem-trf-flat-subring-model-system) -/
def flatSubringModelTensor {R : Type u} [CommRing R]
    (i j : Subalgebra ℤ R) (hij : i ≤ j) (B : Type u) [CommRing B] [Algebra i B]
    (r : j) (b : B) : flatSubringModelStage i j hij B :=
  letI := (Subalgebra.inclusion hij).toRingHom.toAlgebra
  r ⊗ₜ[i] b

/-- A finitely presented flat algebra admits a compatible eventually flat tensor-model system.
Source: Stacks Project, Tag 05FE, via Tag 05FD, with Tags 05N9 (1) and 02JO (3).
(blueprint: lem-trf-flat-subring-model-system)

Proof plan:
1. The finitely generated integer subalgebras above any fixed one form a small nonempty
   directed set: adjoining the union of two finite generating sets gives an upper bound.
   Every element of `R` belongs to such a stage. Compatible ring maps therefore extend
   uniquely to `R`, proving that the inclusion cocone on each tail is colimiting.
2. Apply `lem-kun-fp-algebra-descent` to obtain the finitely presented model `B` over `i`
   and the base-change isomorphism `theta`. At any later stage use the tensor product.
   At `i` itself use the canonical identification `i ⊗[i] B ≃ B`.
3. The tensor pushout universal property gives the comparison isomorphisms: multiply the
   two base-ring factors, with inverse inserting `1`. Composing the comparison to `R`
   with `theta` gives `thetaStage`. Its displayed pure-tensor formula proves compatibility
   with every transition. Tensor inclusions and the universal property give the stated
   unique factorization for arbitrary compatible ring homomorphisms into any ring `T`.
4. `lem-weil-pbc-finite-presentation-base-change-composition` (1) gives finite presentation
   at every stage. Tensor symmetry identifies this order with the source's `B ⊗[i] j`.
5. Apply `lem-weil-pbc-colimit-flat-ring-map` to the tail above `i`, with distinguished
   map `i → B`. The limit map is flat by `theta` and the hypothesis. It supplies `jf`
   such that all later models are flat. Step 1 also supplies the colimit of this tail.

For `j ≤ k`, the transition is `comparison ∘ (z ↦ 1 ⊗ z)`. Its pure-tensor formula,
its compatibility with the maps to `S`, and the canonical comparison formula are included
below. The formulas uniquely determine the transition maps, so also their identity and
composition laws.
-/
theorem exists_flat_subring_model_system
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hfp : Algebra.FinitePresentation R S) (hflat : (algebraMap R S).Flat) :
    ∃ (i : {A : Subalgebra ℤ R // A.FG}) (B : Type u) (_ : CommRing B)
      (_ : Algebra i.1 B) (_ : Algebra.FinitePresentation i.1 B)
      (theta : R ⊗[i.1] B ≃ₐ[R] S)
      (jf : {A : Subalgebra ℤ R // A.FG}),
      i ≤ jf ∧
      (∀ a ∈ ({i, jf} : Set {A : Subalgebra ℤ R // A.FG}),
        Small.{u} {A : Subalgebra ℤ R // A.FG ∧ a.1 ≤ A} ∧
        Nonempty {A : Subalgebra ℤ R // A.FG ∧ a.1 ≤ A} ∧
        IsDirectedOrder {A : Subalgebra ℤ R // A.FG ∧ a.1 ≤ A} ∧
        Nonempty (IsColimit (CommRingCat.subalgebraCocone R
          (fun A ↦ A.FG ∧ a.1 ≤ A)))) ∧
      ∃ thetaStage : ∀ (j : {A : Subalgebra ℤ R // A.FG}) (hij : i ≤ j),
          R ⊗[j.1] flatSubringModelStage i.1 j.1 hij B ≃ₐ[R] S,
        (∀ (j : {A : Subalgebra ℤ R // A.FG}) (hij : i ≤ j),
          (flatSubringModelStructure i.1 j.1 hij B).FinitePresentation ∧
          (jf ≤ j → (flatSubringModelStructure i.1 j.1 hij B).Flat) ∧
          (∀ (r : R) (t : j.1) (b : B),
            thetaStage j hij (r ⊗ₜ[j.1] flatSubringModelTensor i.1 j.1 hij B t b) =
              theta ((j.1.val t * r) ⊗ₜ[i.1] b)) ∧
          (∀ (T : Type (max u v w)) [CommRing T]
            (f : flatSubringModelStage i.1 j.1 hij B →+* T) (g : R →+* T),
            f.comp (flatSubringModelStructure i.1 j.1 hij B) = g.comp j.1.val.toRingHom →
            ∃! h : S →+* T,
              h.comp ((thetaStage j hij).toRingHom.comp
                Algebra.TensorProduct.includeRight.toRingHom) = f ∧
              h.comp (algebraMap R S) = g)) ∧
        (∀ (j k : {A : Subalgebra ℤ R // A.FG}) (hij : i ≤ j) (hjk : j ≤ k),
          ∃ comparison :
              flatSubringModelStage j.1 k.1 hjk (flatSubringModelStage i.1 j.1 hij B) ≃+*
                flatSubringModelStage i.1 k.1 (hij.trans hjk) B,
            (∀ (s : k.1) (t : j.1) (b : B),
              comparison (flatSubringModelTensor j.1 k.1 hjk
                (flatSubringModelStage i.1 j.1 hij B) s
                (flatSubringModelTensor i.1 j.1 hij B t b)) =
                flatSubringModelTensor i.1 k.1 (hij.trans hjk) B
                  (Subalgebra.inclusion hjk t * s) b) ∧
            (∀ z : flatSubringModelStage i.1 j.1 hij B,
              thetaStage k (hij.trans hjk) (1 ⊗ₜ[k.1]
                comparison (flatSubringModelTensor j.1 k.1 hjk
                  (flatSubringModelStage i.1 j.1 hij B) 1 z)) =
                thetaStage j hij (1 ⊗ₜ[j.1] z))) := by
  sorry

end Algebra
