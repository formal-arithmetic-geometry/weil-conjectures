module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal
import Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction
import Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees
import Sheaf.AlgebraicGeometry.ProperFibrewiseAmpleProjective
import Sheaf.AlgebraicGeometry.ProperFiniteFibreFiniteNeighbourhood
import Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import WeilConjectures.RingTheory.FiniteTypeZDomainNormalizationFinite
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.TraceFormula.MarkedCurveFiniteTypeModel
import Sheaf.TraceFormula.StableModificationSpreading
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension

/-!
# Temkin stable modification of a multipointed relative curve

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé X, §3.2.2 and
proof of Theorem 3.4, Step 3, printed pp. 158--160; Temkin, Stable
Modification, Theorems 1.5 and 1.1 (blueprint: lem-trf-temkin-stable-modification).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/--
Source: ILO, Exposé X, §3.2.2 and proof of Theorem 3.4, Step 3, pp. 158--160;
Temkin, Stable Modification, Theorems 1.5 and 1.1 (blueprint: lem-trf-temkin-stable-modification).

Proof (Temkin, proof of Theorem 1.5, pp. 35--36, and of Theorem 1.1, p. 3):
1. By `lem-trf-marked-curve-finite-type-model` the pair `(C, H)` is pulled back
   along a dominant map `S → T` from a multipointed pair `(X, D)` over an integral
   finite-type `ℤ`-scheme `T`, with smooth generic curve and etale generic marking.
2. Fix a separable closure `L` of `k(T)`.  Every point of `RZ_L(T)` is a centred
   valuation ring `V` of finite height (`lem-trf-riemann-zariski-finite-refinement`);
   over `Spec V` choose a stable modification (`lem-trf-valuation-stable-reduction`,
   hypotheses by `lem-trf-semistable-marked-base-change`) and spread it to an
   `L`-quasi-model `U_x` (`lem-trf-stable-modification-spreading`).  No global
   existence theorem is invoked.
3. By quasi-compactness finitely many `U_i` suffice; the common refinement gives a
   proper dominant generically finite `T' → T` covered by opens `W_i` over `U_i`.
   The stable models pull back to `W_i`, stay proper
   (`lem-weil-pbc-proper-fp-permanence`) and semistable, and are isomorphisms over a
   dense open containing the generic fibre; flatness over an integral base makes
   these opens schematically dense.
4. Normalize `T'` to `N` (`lem-weil-pbc-normalization-in-residue-field-extension`);
   `N → T'` is finite (`lem-weil-pbc-finite-type-z-domain-normalization-finite`),
   hence proper, and the models pull back to the cover `V_i` of `N`.
5. On `V_i ∩ V_j` the two models are uniquely isomorphic over `(X, D)`
   (`lem-trf-stable-modification-uniqueness-normal`); the cocycle condition holds by
   uniqueness and `lem-weil-pbc-glue-schemes` glues a pair `(Y, E)` over `N` with a
   pair map to `(X, D) ×_T N`.
6. Flatness, finite presentation, relative dimensions, nodal fibres, the etale
   marking in the smooth locus, properness and the dense isomorphism opens are local
   on the cover, so the glued pair is a stable generic-fibre modification over `N`.
7. In `Q = S ×_T N` take the closure `S'` of a point of the generic fibre `Q_η`.
   It is integral, proper, dominant and finite over a dense open of `S`
   (`thm-sc-proper-finite-fibre-finite-neighbourhood`), Noetherian and excellent
   (`lem-exc-finite-type-localization-excellent`).  Pulling back `(Y, E)` gives
   `(C', H')`, `b` and `d`, with generic isomorphisms.
8. `lem-trf-marked-nodal-dualizing-degrees` gives `ω_{C'/S'}(H')` of positive degree
   on every contracted component, and `lem-trf-proper-fibrewise-ample-projective`
   gives the closed immersion of `C'` into a projective bundle over `C ×_S S'`.
9. The compatibility `j' ≫ b = d ≫ (H ×_S S' → C ×_S S')` and the generic
   isomorphism of `d` were kept at every step; `lem-trf-semistable-marked-base-change`
   gives the semistable multipointed form after every base change `S₁ → S'`.
-/
theorem exists_temkin_stable_modification
    {S : Scheme.{u}} [IsIntegral S] [IsNoetherian S]
    (hS : ∀ U : S.Opens, IsAffineOpen U → IsExcellent Γ(S, U))
    (η : S) (hη : IsGenericPoint η Set.univ)
    {C H : Scheme.{u}} (c : C ⟶ S) (h : H ⟶ S)
    [Flat c] [LocallyOfFinitePresentation c]
    [Flat h] [LocallyOfFinitePresentation h]
    (hCdim : ∀ s : S, ∀ Z : Set (c.fiber s),
      Z ∈ irreducibleComponents (c.fiber s) →
        topologicalKrullDim Z = (1 : WithBot ℕ∞))
    (hHdim : ∀ s : S, ∀ Z : Set (h.fiber s),
      Z ∈ irreducibleComponents (h.fiber s) →
        topologicalKrullDim Z = (0 : WithBot ℕ∞))
    (i : H ⟶ C) (hi : i ≫ c = h) [IsClosedImmersion i]
    [Smooth (c.fiberToSpecResidueField η)]
    [Etale (h.fiberToSpecResidueField η)] :
    ∃ (S' : Scheme.{u}) (a : S' ⟶ S) (η' : S')
      (_ : IsGenericPoint η' Set.univ),
      IsIntegral S' ∧ IsNoetherian S' ∧
      (∀ U : S'.Opens, IsAffineOpen U → IsExcellent Γ(S', U)) ∧
      IsProper a ∧ IsDominant a ∧
      (∃ U : S.Opens, Dense (U : Set S) ∧ IsFinite (a ∣_ U)) ∧
      ∃ (C' H' : Scheme.{u}) (b : C' ⟶ pullback (C := Scheme.{u}) c a)
        (j' : H' ⟶ C') (d : H' ⟶ pullback (C := Scheme.{u}) h a)
        (c' : C' ⟶ S') (h' : H' ⟶ S')
        (hb : b ≫ pullback.snd c a = c') (hd : d ≫ pullback.snd h a = h')
        (hj' : j' ≫ c' = h'),
        IsProjectiveBundle b ∧ IsProper b ∧
        (∃ U : (pullback (C := Scheme.{u}) c a).Opens,
          Dense (U : Set (pullback (C := Scheme.{u}) c a)) ∧
          IsIso (pullback.snd b U.ι)) ∧
        IsClosedImmersion j' ∧
        j' ≫ b = d ≫
          pullback.map h a c a i (𝟙 S') (𝟙 S) hi.symm (by simp) ∧
        IsIso
          (show (c'.fiber η') ⟶
              (pullback.snd c a).fiber η' from
            pullback.lift
              (c'.fiberι η' ≫ b)
              (c'.fiberToSpecResidueField η')
              (by simpa [hb] using Scheme.Hom.fiber_fac c' η')) ∧
        IsIso
          (show (h'.fiber η') ⟶
              (pullback.snd h a).fiber η' from
            pullback.lift
              (h'.fiberι η' ≫ d)
              (h'.fiberToSpecResidueField η')
              (by simpa [hd] using Scheme.Hom.fiber_fac h' η')) ∧
        Flat c' ∧ LocallyOfFinitePresentation c' ∧
        (∀ s : S', ∀ Z : Set (c'.fiber s),
          Z ∈ irreducibleComponents (c'.fiber s) →
            topologicalKrullDim Z = (1 : WithBot ℕ∞)) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (g : Spec (.of Ω) ⟶ S'),
          ∀ x : pullback (C := Scheme.{u}) c' g,
            (¬ ∃ U : (pullback (C := Scheme.{u}) c' g).Opens, x ∈ U ∧
              Smooth (U.ι ≫ pullback.snd c' g)) →
            Nonempty
              (AdicCompletion
                (IsLocalRing.maximalIdeal ((pullback (C := Scheme.{u}) c' g).presheaf.stalk x))
                ((pullback (C := Scheme.{u}) c' g).presheaf.stalk x) ≃+*
                (MvPowerSeries (Fin 2) Ω ⧸
                  Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                    (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)})) ) ∧
        Flat h' ∧ LocallyOfFinitePresentation h' ∧
        (∀ s : S', ∀ Z : Set (h'.fiber s),
          Z ∈ irreducibleComponents (h'.fiber s) →
            topologicalKrullDim Z = (0 : WithBot ℕ∞)) ∧
        Etale h' ∧
        (∀ x : H', ∃ U : C'.Opens, j' x ∈ U ∧ Smooth (U.ι ≫ c')) ∧
        (∀ (S₁ : Scheme.{u}) (q : S₁ ⟶ S'),
          let j₁ := pullback.map h' q c' q j' (𝟙 S₁) (𝟙 S')
            hj'.symm
            (by simp)
          Flat (pullback.snd c' q) ∧ LocallyOfFinitePresentation (pullback.snd c' q) ∧
          IsClosedImmersion j₁ ∧
          (∀ s : S₁, ∀ Z : Set ((pullback.snd c' q).fiber s),
            Z ∈ irreducibleComponents ((pullback.snd c' q).fiber s) →
              topologicalKrullDim Z = (1 : WithBot ℕ∞)) ∧
          (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
              (g : Spec (.of Ω) ⟶ S₁),
            ∀ x : pullback (C := Scheme.{u}) (pullback.snd c' q) g,
              (¬ ∃ U : (pullback (C := Scheme.{u}) (pullback.snd c' q) g).Opens,
                x ∈ U ∧ Smooth (U.ι ≫ pullback.snd (pullback.snd c' q) g)) →
              Nonempty
                (AdicCompletion
                  (IsLocalRing.maximalIdeal
                    ((pullback (C := Scheme.{u}) (pullback.snd c' q) g).presheaf.stalk x))
                  ((pullback (C := Scheme.{u}) (pullback.snd c' q) g).presheaf.stalk x) ≃+*
                  (MvPowerSeries (Fin 2) Ω ⧸
                    Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                      MvPowerSeries.X 1}))) ∧
          Flat (pullback.snd h' q) ∧
          LocallyOfFinitePresentation (pullback.snd h' q) ∧
          (∀ s : S₁, ∀ Z : Set ((pullback.snd h' q).fiber s),
            Z ∈ irreducibleComponents ((pullback.snd h' q).fiber s) →
              topologicalKrullDim Z = (0 : WithBot ℕ∞)) ∧
          Etale (pullback.snd h' q) ∧
          (∀ x : pullback (C := Scheme.{u}) h' q,
            ∃ U : (pullback (C := Scheme.{u}) c' q).Opens, j₁ x ∈ U ∧
              Smooth (U.ι ≫ pullback.snd c' q))) := by
  sorry

end AlgebraicGeometry
