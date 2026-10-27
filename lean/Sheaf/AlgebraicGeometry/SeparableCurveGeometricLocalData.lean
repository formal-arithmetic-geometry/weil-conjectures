/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.ZetaSeries
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.TensorProduct.Quotient
import Sheaf.FieldTheory.SeparableTensorAlgebraicClosure
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.ClosedPointDimensionLocalRing

/-! # Affine geometric stalks at a separable closed point

Source: Stacks Project, curves.tex, Tag 0C4D, arbitrary-field paragraph;
varieties.tex, Tags 0C4Y, 0C50 and 0A21, closed-point dimension.
(blueprint: lem-sfb-separable-curve-geometric-local-data)

The cartesian square names the base change together with its two projections.
An affine neighbourhood is represented by an open immersion from `Spec S` and
its point `p`. All stalk and completion isomorphisms are characterized by the
canonical maps, including their action on each completion quotient.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The affine and geometric local data at a closed point with finite separable
residue field, for every affine open neighbourhood of that point.

Source: Stacks Project, curves.tex, Tag 0C4D, arbitrary-field paragraph;
varieties.tex, Tags 0C4Y, 0C50 and 0A21; algebra.tex, Tag 00M9.
(blueprint: lem-sfb-separable-curve-geometric-local-data)

Proof:
1. For the given affine open immersion `i`, use lem-weil-pbc-lft-affine-pairs
   to make S finite type over k. Closedness of x makes p maximal. The germ
   identification is lem-weil-pbc-affine-open-stalk-localization, and
   lem-weil-pbc-prime-residue-field-algebra identifies S/p with the given F.
2. lem-weil-pbc-open-fibre-product identifies the base-changed open with the
   inverse image of this open. lem-weil-pbc-fibre-product-affine-spectra gives
   its tensor-product chart and both projection formulas. Lift y to q in this
   chart; the affine-open stalk theorem identifies its localization with B.
3. lem-weil-pbc-tensor-quotient-base-change and
   lem-weil-pbc-algebra-tensor-pushout-universal-property identify T/pT with
   F tensor_k K. By lem-pc-separable-tensor-algebraic-closure this is a finite
   product of copies of K. In a prime quotient exactly one of the orthogonal
   coordinate idempotents is one, so q is maximal with structural residue K.
   Restrict its evaluation to F to obtain the embedding iota determined by y;
   tensor balancing gives the displayed formula and identifies its kernel.
4. Apply lem-trf-separable-evaluation-local-base-change with this embedding.
   The actual stalk map agrees on S with the localized inclusion, hence on
   S_p by localization uniqueness. The lemma gives Noetherian local A and B,
   faithful flatness, equality of extended maximal ideals and residue field K,
   with residue map iota. A is essentially finite type by its localization
   presentation, as in def-weil-pbc-essentially-finite-type-algebra.
5. def-weil-pure-dimension and lem-sbc-equidimensional-open-local-dimension
   give local topological dimension d. Use
   lem-weil-pbc-dimension-at-point-open-subspace and
   lem-weil-pbc-closed-point-dimension-local-ring to obtain dim A = d.
6. The germ ring isomorphisms preserve units and hence maximal ideals and
   all their powers. Apply their mutually inverse quotient maps coordinatewise
   to compatible sequences in def-weil-pbc-adic-completion. This constructs
   the completion isomorphisms with the stated action on every quotient,
   using def-weil-pbc-algebra-hom-quotient. -/
theorem separable_curve_geometric_local_data
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (d : ℕ) (hdim : C.IsPureDimension d)
    (x : C) (hx : IsClosed ({x} : Set C))
    (hfin : (f.residueFieldAlgebraMap x).Finite)
    (hsep : @Algebra.IsSeparable k (C.residueField x) _ _
      (f.residueFieldAlgebraMap x).toAlgebra)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]
    (Y : Scheme.{u}) (π : Y ⟶ C) (g : Y ⟶ Spec (.of K))
    (hcart : IsPullback π g f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (y : Y) (hy : π y = x)
    (S : Type u) [CommRing S] [Algebra k S]
    (i : Spec (.of S) ⟶ C) [IsOpenImmersion i]
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k S)))
    (p : PrimeSpectrum S) (hp : i p = x) :
    (algebraMap k S).FiniteType ∧ p.asIdeal.IsMaximal ∧
    IsNoetherianRing (C.presheaf.stalk x) ∧ IsNoetherianRing (Y.presheaf.stalk y) ∧
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ C.presheaf.Γgerm x).hom).EssFiniteType ∧
    ringKrullDim (C.presheaf.stalk x) = (d : WithBot ℕ∞) ∧
    ∃ (eA : C.presheaf.stalk x ≃+* Localization.AtPrime p.asIdeal)
      (eF : (S ⧸ p.asIdeal) ≃+* C.residueField x)
      (j : Spec (.of (S ⊗[k] K)) ⟶ Y) (hj : IsOpenImmersion j),
      eA = (C.presheaf.stalkCongr (Inseparable.of_eq hp.symm) ≪≫
        asIso (i.stalkMap p) ≪≫ Spec.stalkIso (.of S) p).commRingCatIsoToRingEquiv ∧
      (∀ s : S, eF (Ideal.Quotient.mk p.asIdeal s) =
        IsLocalRing.residue (C.presheaf.stalk x)
          (eA.symm (algebraMap S (Localization.AtPrime p.asIdeal) s))) ∧
      eF.toRingHom.comp ((Ideal.Quotient.mk p.asIdeal).comp (algebraMap k S)) =
        f.residueFieldAlgebraMap x ∧
      Set.range j = π ⁻¹' Set.range i ∧
      j ≫ π = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : S →ₐ[k] S ⊗[k] K).toRingHom) ≫ i ∧
      j ≫ g = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : K →ₐ[k] S ⊗[k] K).toRingHom) ∧
      ∃ (q : PrimeSpectrum (S ⊗[k] K)) (hq : j q = y)
        (eB : Y.presheaf.stalk y ≃+* Localization.AtPrime q.asIdeal)
        (ι : C.residueField x →+* K) (ε : S ⊗[k] K →+* K)
        (eK : Y.residueField y ≃+* K),
        q.asIdeal.IsMaximal ∧
        eB = (Y.presheaf.stalkCongr (Inseparable.of_eq hq.symm) ≪≫
          asIso (j.stalkMap q) ≪≫
          Spec.stalkIso (.of (S ⊗[k] K)) q).commRingCatIsoToRingEquiv ∧
        ι.comp (f.residueFieldAlgebraMap x) = algebraMap k K ∧
        (∀ (s : S) (l : K), ε (s ⊗ₜ[k] l) = ι (eF (Ideal.Quotient.mk p.asIdeal s)) * l) ∧
        q.asIdeal = RingHom.ker ε ∧
        eK.toRingHom.comp (g.residueFieldAlgebraMap y) = RingHom.id K ∧
        (∀ t : S ⊗[k] K,
          eK (IsLocalRing.residue (Y.presheaf.stalk y)
            (eB.symm (algebraMap (S ⊗[k] K) (Localization.AtPrime q.asIdeal) t))) = ε t) ∧
        (∀ s : S,
          eB (((C.presheaf.stalkCongr (Inseparable.of_eq hy.symm)).hom ≫
            π.stalkMap y).hom (eA.symm (algebraMap S (Localization.AtPrime p.asIdeal) s))) =
          algebraMap (S ⊗[k] K) (Localization.AtPrime q.asIdeal) (s ⊗ₜ[k] (1 : K))) ∧
        (∀ a : C.presheaf.stalk x,
          eK (IsLocalRing.residue (Y.presheaf.stalk y)
            (((C.presheaf.stalkCongr (Inseparable.of_eq hy.symm)).hom ≫ π.stalkMap y).hom a)) =
          ι (IsLocalRing.residue (C.presheaf.stalk x) a)) ∧
        @Module.FaithfullyFlat (C.presheaf.stalk x) (Y.presheaf.stalk y) _ _
          (((C.presheaf.stalkCongr (Inseparable.of_eq hy.symm)).hom ≫
            π.stalkMap y).hom.toAlgebra.toModule) ∧
        Ideal.map (((C.presheaf.stalkCongr (Inseparable.of_eq hy.symm)).hom ≫
          π.stalkMap y).hom) (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) =
          IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ∧
        ∃ (EA : AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
              (C.presheaf.stalk x) ≃+*
            AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
              (Localization.AtPrime p.asIdeal))
          (EB : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
              (Y.presheaf.stalk y) ≃+*
            AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
              (Localization.AtPrime q.asIdeal)),
          (∀ (n : ℕ)
            (z : AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
              (C.presheaf.stalk x)) (a : C.presheaf.stalk x),
            AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) n z =
                Ideal.Quotient.mk (IsLocalRing.maximalIdeal (C.presheaf.stalk x) ^ n) a →
            AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
                n (EA z) =
              Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ n)
                (eA a)) ∧
          (∀ (n : ℕ)
            (z : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
              (Y.presheaf.stalk y)) (b : Y.presheaf.stalk y),
            AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) n z =
                Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ n) b →
            AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
                n (EB z) =
              Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ n)
                (eB b)) := by
  sorry

end AlgebraicGeometry
