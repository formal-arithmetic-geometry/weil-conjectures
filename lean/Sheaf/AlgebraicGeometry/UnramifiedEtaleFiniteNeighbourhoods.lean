module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.AlgebraicGeometry.EtaleLocalFiniteMultiplePoints
import Sheaf.AlgebraicGeometry.UnramifiedFibrePointIsolated
import Sheaf.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen

/-!
# Finite unramified neighbourhoods after étale localization

The first construction in Stacks Project, Tag 04HI, using Tags 02LM, 02G6 and 02GA.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 04HH, used by Tag 04HI; Tag 02LM and Tags 02G6, 02GA.
(blueprint: lem-weil-pbc-unramified-etale-finite-neighbourhoods)

Proof: take the union of the given unramified open neighbourhoods. Local finite type and
unramifiedness are local on the source, so its restriction is unramified. Remove duplicate
listed points, keeping one representative index for each. The isolated-fibre-point theorem
applies to this restriction. Apply `exists_etale_local_finite_multiple_points` to the distinct
representatives. Its finite pieces remain unramified by base change and open restriction.
The open immersion from the restricted source induces an open immersion of pullbacks;
regard the pieces as opens of the original pullback. Open immersions identify their residue
fields, so uniqueness and pure inseparability persist. Index each representative's pieces
by its original index and assign zero pieces to duplicate indices. The injectivity of the
marked points is unchanged. Every lift of a listed point lies in this source open and is
one of the enumerated points, including for repeated entries of the original list.
For the empty list take the identity neighbourhood and the empty family. -/
theorem exists_etale_finite_unramified_neighbourhoods
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (n : ℕ) (x : Fin n → X) (hx : ∀ i, f.base (x i) = s)
    (hunramified : ∀ i, ∃ O : X.Opens, x i ∈ O ∧
      LocallyOfFiniteType (O.ι ≫ f) ∧ IsOpenImmersion (pullback.diagonal (O.ι ≫ f))) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U), Etale g ∧ g.base u = s ∧
      ∃ (m : Fin n → ℕ) (V : (Σ i : Fin n, Fin (m i)) → (pullback f g).Opens)
        (v : (a : Σ i : Fin n, Fin (m i)) → (V a).toScheme),
        (∀ a, IsFinite ((V a).ι ≫ pullback.snd f g) ∧
          (LocallyOfFiniteType ((V a).ι ≫ pullback.snd f g) ∧
            IsOpenImmersion (pullback.diagonal ((V a).ι ≫ pullback.snd f g))) ∧
          ((V a).ι ≫ pullback.snd f g) (v a) = u ∧
          (∀ w : (V a).toScheme,
            ((V a).ι ≫ pullback.snd f g) w = u → w = v a) ∧
          (letI : Algebra (U.residueField (((V a).ι ≫ pullback.snd f g) (v a)))
              ((V a).toScheme.residueField (v a)) :=
            (((V a).ι ≫ pullback.snd f g).residueFieldMap (v a)).hom.toAlgebra
           IsPurelyInseparable
             (U.residueField (((V a).ι ≫ pullback.snd f g) (v a)))
             ((V a).toScheme.residueField (v a)))) ∧
        Function.Injective (fun a ↦ (V a).ι (v a)) ∧
        (∀ (i : Fin n) (p : ↥(pullback f g)),
          (pullback.snd f g).base p = u → (pullback.fst f g).base p = x i →
            ∃ a, p = (V a).ι (v a)) := by
  sorry

end AlgebraicGeometry
