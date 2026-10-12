/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.RingTheory.KoszulConormalComparison
public import Sheaf.RingTheory.KoszulRegularSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.RingTheory.Localization.Defs
import Sheaf.Paper.KoszulComplex

/-!
# Duality for a Koszul-regular quotient

Source: Stacks Project, duality.tex, Tag 0BQZ, lemma-regular-immersion-ext, local
Koszul computation (blueprint: lem-sc-koszul-regular-sequence-dual-complex).

The comparison is normalized by the determinant pairing on the conormal module,
with the sign `(-1)^(r*(r-1)/2)` from the ordered contraction composition in Stacks.
A complex supported in degree `r` represents `⋀^r N[-r]`. The Ext comparison is
specified on roofs from the Koszul resolution, so it is independent of generators.

## Main statements

* `exists_unique_koszul_conormal_comparison`: the canonical quasi-isomorphism.
* `koszul_conormal_comparison_cohomology`: the derived and cohomological conclusions.
* `exists_koszul_quotient_augmentation`: the Koszul resolution of the quotient.
* `exists_intrinsic_koszul_ext_determinant`: the generator-independent Ext identification.
* `koszul_conormal_comparison_change_generators`: change-of-resolution compatibility.
* `koszul_conormal_comparison_localization`: compatibility with arbitrary localization.
-/

@[expose] public section

universe uT

open CategoryTheory CategoryTheory.Limits

namespace ExteriorAlgebra

/-- The uniquely normalized comparison is a quasi-isomorphism.
Source: Stacks Project, Tag 0BQZ
(blueprint: lem-sc-koszul-regular-sequence-dual-complex).

Proof: (1) Koszul-regularity makes the finite free Koszul complex a resolution of
`A/I`, using `def-weil-pbc-koszul-complex` and `def-weil-pbc-koszul-regular-sequence`.
(2) The determinant pairing of `lem-sc-exterior-power-dual-pairing` identifies the
complementary exterior-power duals. (3) Evaluation on the top wedge identifies the
signed dual complex with the shifted Koszul complex; correct an anticommuting map
by a degreewise sign when the length is even. Thus only degree `r` survives.
(4) Reduction modulo `I` identifies the surviving classes with the determinant of
the dual conormal module. Ordered contractions on the top wedge contribute
`(-1)^(r*(r-1)/2)`; this evaluation formula fixes the comparison uniquely.
The formulas commute with localization and determinant changes of generators. -/
theorem exists_unique_koszul_conormal_comparison
    (A : Type uT) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I) :
    ∃! φ : koszulDualComplex A r f ⟶
        (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
          (koszulNormalDeterminant A I r),
      IsKoszulConormalComparison A I r f hf φ ∧ QuasiIso φ := by
  sorry

/-- The canonical comparison `φ`, extended by zero to integer degrees, becomes an
isomorphism in `D(A)` onto the determinant placed in degree `r`; all cohomology
vanishing outside degree `r`, and the degree-`r` identification as a `B`-module.
The restricted module `M` realizes the induced `B = A/I` action on cohomology;
the last equality ties its isomorphism to the actual canonical comparison.
Source: Stacks Project, Tag 0BQZ
(blueprint: lem-sc-koszul-regular-sequence-dual-complex).

Proof: Steps 1--3 of the node identify the dual with the shifted Koszul resolution,
so the only cohomology is in degree `r`. Step 4 identifies that cohomology with the
dual conormal determinant by reduction modulo `I` and the determinant pairing.
The normalized comparison is an `A`-linear quasi-isomorphism to the restriction
of this `B`-module; its localization in `D(A)` is the asserted isomorphism. -/
theorem koszul_conormal_comparison_cohomology
    (A : Type uT) [CommRing A] [HasDerivedCategory.{uT + 1} (ModuleCat.{uT} A)]
    (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I)
    (φ : koszulDualComplex A r f ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r))
    (hφ : IsKoszulConormalComparison A I r f hf φ) :
    IsIso (DerivedCategory.Q.map
      (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)) ∧
    (∀ i : ℤ, i ≠ (r : ℤ) → IsZero ((koszulDualCochainComplex A r f).homology i)) ∧
    ∃ (M : ModuleCat.{uT} (A ⧸ I))
      (ι : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M ≅
        (koszulDualComplex A r f).homology r)
      (e : M ≅ ModuleCat.of (A ⧸ I)
        (⋀[A ⧸ I]^r (Module.Dual (A ⧸ I) I.Cotangent))),
      ∀ z : (koszulDualComplex A r f).cycles r,
        e.hom (ι.inv ((koszulDualComplex A r f).homologyπ r z)) =
          koszulComparisonValue A I r f φ ((koszulDualComplex A r f).iCycles r z) := by
  sorry

/-- The Koszul augmentation is a quasi-isomorphism to the quotient in degree zero.
Source: Stacks Project, Tag 0BQZ
(blueprint: lem-sc-koszul-regular-sequence-dual-complex).

Proof: Step 1 uses Koszul-regularity to kill positive homology. Degree zero is the
cokernel of `d₁`, whose image is the ideal generated by `f`; the augmentation is
therefore the quotient map. Extension along `embeddingDownNat` puts degree `n`
in cohomological degree `-n`, with zero terms outside the image. -/
theorem exists_koszul_quotient_augmentation
    (A : Type uT) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I) :
    ∃ ε : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
        (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)),
      QuasiIso ε ∧
      ∀ x : ⋀[A]^0 (Fin r →₀ A),
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of A (A ⧸ I))).hom
          (ε.f 0 (((koszulComplex A r f).extendXIso
            ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
        Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x) := by
  sorry

/-- The intrinsic Ext determinant isomorphism, normalized on every Koszul roof.
One isomorphism is chosen for the ideal `I`, before quantifying over its generating
sequences. The equality on roofs identifies it with the canonical comparison on
cohomology. Precomposition with multiplication on `B` specifies its `B`-linearity.
Source: Stacks Project, Tag 0BQZ
(blueprint: lem-sc-koszul-regular-sequence-dual-complex).

Proof: Step 1 supplies the finite free resolution and computes Ext by its total
Hom complex. Steps 2--3 identify its top classes through the determinant pairing.
Step 4 shows that reduction modulo `I` and the determinant formula are intrinsic:
changing the free generators changes both determinant evaluations by the same
factor. Thus the normalized isomorphism on Ext is independent of the resolution
and commutes with the quotient action by precomposition. The ordered contraction
composition contributes the sign `(-1)^(r*(r-1)/2)` on the top wedge. -/
theorem exists_intrinsic_koszul_ext_determinant
    (A : Type uT) [CommRing A] [HasDerivedCategory.{uT + 1} (ModuleCat.{uT} A)]
    (I : Ideal A) (r : ℕ)
    (hex : ∃ f : Fin r → A,
      RingTheory.Sequence.IsKoszulRegular f ∧ Ideal.span (Set.range f) = I) :
    ∃ e : Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) r ≃ₗ[A]
        koszulNormalDeterminant A I r,
      (∀ (b : A ⧸ I) (x : Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) r),
        e ((Abelian.Ext.mk₀ (ModuleCat.ofHom
          (b • (LinearMap.id : (A ⧸ I) →ₗ[A] (A ⧸ I))))).comp x (zero_add r)) =
          @SMul.smul (A ⧸ I) (⋀[A ⧸ I]^r (Module.Dual (A ⧸ I) I.Cotangent))
            inferInstance b (e x)) ∧
      ∀ (f : Fin r → A) (_hreg : RingTheory.Sequence.IsKoszulRegular f)
        (hf : Ideal.span (Set.range f) = I)
        (ε : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
          (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
        [QuasiIso ε],
        (∀ x : ⋀[A]^0 (Fin r →₀ A),
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (ModuleCat.of A (A ⧸ I))).hom
            (ε.f 0 (((koszulComplex A r f).extendXIso
              ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
          Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x)) →
        ∀ (z : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
            (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A))
          (v : Fin r → (Fin r →₀ A)),
          exteriorPower.pairingDual (A ⧸ I) I.Cotangent r
            (e ((Abelian.Ext.homLinearEquiv (R := A)).symm
              (inv (DerivedCategory.Q.map ε) ≫ DerivedCategory.Q.map z ≫
                ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
                  (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app
                    (ModuleCat.of A A))))
            (exteriorPower.ιMulti (A ⧸ I) r
              (fun i ↦ koszulConormalVector A I r f hf (v i))) =
            (-1 : A ⧸ I) ^ (r * (r - 1) / 2) *
              Ideal.Quotient.mk I
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
                (ModuleCat.of A A)).hom
                (z.f (-(r : ℤ)) (((koszulComplex A r f).extendXIso
                  ComplexShape.embeddingDownNat (i := r) rfl).inv
                    (exteriorPower.ιMulti A r v)))) := by
  sorry

/-- The normalized comparisons commute with a change of Koszul generators.
Source: Stacks Project, Tag 0BQZ
(blueprint: lem-sc-koszul-regular-sequence-dual-complex).

Proof: Step 4 uses the determinant change-of-generators identity. A map `t` lifting
identity on the quotient induces the identity on conormal classes. Evaluating the
two composites on wedges gives the same determinant pairing, hence the same value.
This is the comparison of resolutions used in the intrinsic Ext isomorphism. -/
theorem koszul_conormal_comparison_change_generators
    (A : Type uT) [CommRing A] (I : Ideal A) (r : ℕ) (f g : Fin r → A)
    (hregf : RingTheory.Sequence.IsKoszulRegular f)
    (hregg : RingTheory.Sequence.IsKoszulRegular g)
    (hf : Ideal.span (Set.range f) = I) (hg : Ideal.span (Set.range g) = I)
    (φ : koszulDualComplex A r f ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r))
    (ψ : koszulDualComplex A r g ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r))
    (hφ : IsKoszulConormalComparison A I r f hf φ)
    (hψ : IsKoszulConormalComparison A I r g hg ψ)
    (t : (Fin r →₀ A) →ₗ[A] (Fin r →₀ A))
    (ht : (Finsupp.linearCombination A g).comp t = Finsupp.linearCombination A f) :
    ∀ x : (koszulComplex A r g).X r ⟶ ModuleCat.of A A,
      koszulComparisonValue A I r f φ
          (ModuleCat.ofHom (x.hom.comp (exteriorPower.map r t))) =
        koszulComparisonValue A I r g ψ x := by
  sorry

/-- Localization preserves regularity and the determinant-normalized comparison.
The maps `χ` and `ν` are the coefficient-extension maps on the degree-`r` dual
and normal determinant. Their evaluation equations specify the canonical maps,
and the last equation is the commutative comparison square. Since the comparison
target has only degree `r`, this is the complete complex-level compatibility.
Source: Stacks Project, Tag 0BQZ
(blueprint: lem-sc-koszul-regular-sequence-dual-complex).

Proof: Steps 1--3 use exact localization on the Koszul resolution, giving regularity
of the localized sequence. Step 4 localizes the conormal determinant pairing.
Its evaluation matrix is obtained by applying the localization ring map entrywise,
so the determinant and top dual evaluations commute with that map. The two
normalized comparison maps therefore give the asserted commutative square. -/
theorem koszul_conormal_comparison_localization
    (A : Type uT) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I)
    (T : Submonoid A) (S : Type uT) [CommRing S] [Algebra A S]
    [IsLocalization T S] :
    RingTheory.Sequence.IsKoszulRegular (algebraMap A S ∘ f) ∧
    ∃ hs : Ideal.span (Set.range (algebraMap A S ∘ f)) = I.map (algebraMap A S),
      ∃ q : (A ⧸ I) →+* (S ⧸ I.map (algebraMap A S)),
        (∀ b : A, q (Ideal.Quotient.mk I b) =
          Ideal.Quotient.mk (I.map (algebraMap A S)) (algebraMap A S b)) ∧
        ∀ (φ : koszulDualComplex A r f ⟶
            (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
              (koszulNormalDeterminant A I r))
          (ψ : koszulDualComplex S r (algebraMap A S ∘ f) ⟶
            (HomologicalComplex.single (ModuleCat S) (ComplexShape.up ℕ) r).obj
              (koszulNormalDeterminant S (I.map (algebraMap A S)) r)),
          IsKoszulConormalComparison A I r f hf φ →
          IsKoszulConormalComparison S (I.map (algebraMap A S)) r
            (algebraMap A S ∘ f) hs ψ →
          ∃ (χ : koszulDualComplex A r f ⟶
              ((ModuleCat.restrictScalars (algebraMap A S)).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (koszulDualComplex S r (algebraMap A S ∘ f)))
            (ν : koszulNormalDeterminant A I r →ₗ[A]
              (ModuleCat.restrictScalars (algebraMap A S)).obj
                (koszulNormalDeterminant S (I.map (algebraMap A S)) r)),
            (∀ (n : ℕ) (x : (koszulComplex A r f).X n ⟶ ModuleCat.of A A)
              (v : Fin n → (Fin r →₀ A)),
              (χ.f n x).hom (exteriorPower.ιMulti S n
                (fun i ↦ (v i).mapRange (algebraMap A S) (map_zero _))) =
              algebraMap A S (x.hom (exteriorPower.ιMulti A n v))) ∧
            (∀ (w : koszulNormalDeterminant A I r) (v : Fin r → (Fin r →₀ A)),
              exteriorPower.pairingDual (S ⧸ I.map (algebraMap A S))
                (I.map (algebraMap A S)).Cotangent r (ν w)
                (exteriorPower.ιMulti (S ⧸ I.map (algebraMap A S)) r
                  (fun i ↦ koszulConormalVector S (I.map (algebraMap A S)) r
                    (algebraMap A S ∘ f) hs
                    ((v i).mapRange (algebraMap A S) (map_zero _)))) =
              q (exteriorPower.pairingDual (A ⧸ I) I.Cotangent r w
                (exteriorPower.ιMulti (A ⧸ I) r
                  (fun i ↦ koszulConormalVector A I r f hf (v i))))) ∧
            (∀ x : (koszulComplex A r f).X r ⟶ ModuleCat.of A A,
              koszulComparisonValue S (I.map (algebraMap A S)) r
                (algebraMap A S ∘ f) ψ (χ.f r x) =
              ν (koszulComparisonValue A I r f φ x)) := by
  sorry

end ExteriorAlgebra
