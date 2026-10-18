/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Compactification.StrictTransformChartModel
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# The affine deformation chart as a strict-transform complement

Source: Stacks Project, divisors.tex, Tags 0804 and 080D, specialized to the centre
`(I,t)` in `Spec R[t]` (blueprint: lem-pur-dnc-affine-blowup-complement).

The auxiliary definitions specialize the existing ideal and strict-transform constructions;
the charts are the recorded `AffineBlowup.chartRingιOfEq`. No new model for any of these
constructions is introduced.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.DncAffineBlowup

variable {R : Type u} [CommRing R]

/-- The centre ideal `(I,t)` in `R[t]`. Source: Stacks, Tag 0804, affine specialization
(blueprint: lem-pur-dnc-affine-blowup-complement). -/
noncomputable def centerIdeal (I : Ideal R) : Ideal (Polynomial R) :=
  I.map Polynomial.C ⊔ Ideal.span {Polynomial.X}

/-- The distinguished generator `t` of the centre. Source: Stacks, Tag 0804
(blueprint: lem-pur-dnc-affine-blowup-complement). -/
noncomputable def parameter (I : Ideal R) : centerIdeal I :=
  ⟨Polynomial.X, Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))⟩

/-- A constant generator of the centre. Source: Stacks, Tag 0804
(blueprint: lem-pur-dnc-affine-blowup-complement). -/
noncomputable def constant (I : Ideal R) (a : I) : centerIdeal I :=
  ⟨Polynomial.C (a : R), Ideal.mem_sup_left (Ideal.mem_map_of_mem Polynomial.C a.2)⟩

/-- The ideal sheaf of the centre on the affine spectrum. Source: Stacks, Tag 0804
(blueprint: lem-pur-dnc-affine-blowup-complement). -/
noncomputable def center (I : Ideal R) : (Spec (.of (Polynomial R))).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    ((centerIdeal I).map (Scheme.ΓSpecIso (.of (Polynomial R))).inv.hom)

/-- The closed immersion `V(t) → Spec R[t]`. Source: Stacks, Tag 080D
(blueprint: lem-pur-dnc-affine-blowup-complement). -/
noncomputable def hyperplane (R : Type u) [CommRing R] :
    Spec (.of (Polynomial R ⧸ (Ideal.span {Polynomial.X} : Ideal (Polynomial R)))) ⟶
      Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.span {Polynomial.X} : Ideal (Polynomial R))))

/-- The ideal sheaf of the scheme-theoretic strict transform, viewed inside the blow-up.
Source: Stacks, Tag 080D (blueprint: lem-pur-dnc-affine-blowup-complement). -/
noncomputable def transformIdeal (I : Ideal R) : (center I).blowup.IdealSheafData :=
  (strictTransformMap (hyperplane R) (center I).blowupMap (center I).support.compl).ker

/-- The strict-transform complement is exactly the parameter chart, including the
scheme-theoretic calculation on every generator chart. Source: Stacks, Tags 0804 and 080D
(blueprint: lem-pur-dnc-affine-blowup-complement).

Proof plan:
1. The global blow-up over this affine base is the affine Rees blow-up, by
`def-nagata-global-blowup`, its gluing datum and local model. The standard charts cover it
by `prop-nagata-affine-blowup-chart` and `prop-nagata-affine-blowup-chart-cover`.
The map `def-nagata-homogeneous-away-to-chart` sends the homogeneous fraction to `x/a`.
2. On an `f`-chart put `C = R[I/f]`. Substitution `v ↦ t/f` gives `C[v] ≃ A[J/f]`.
It is onto because `t = fv`; it is one-to-one by comparison of polynomial coefficients
inside `R_f[t]`, since `f` is a unit in `R_f`. This includes the zero localization.
3. The strict transform is the schematic closure of the hyperplane away from the centre.
The open immersion used for the closure is quasi-compact since the ideal has finitely many
generators. By `lemma-nagata-scheme-image-restrict-open`, compute its ideal on each chart
as the restriction kernel, using `def-nagata-scheme-theoretic-closure` and
`def-nagata-scheme-theoretic-image`.
4. On the parameter chart the centre ideal is `(t)`, and `V(t) ∩ D(t)` is empty.
Its closure ideal is the unit ideal.
5. On the `f`-chart the centre is `(f)` and the hyperplane is `V(fv)`. Off the centre
its ring is `R_f[v]/(v) = R_f`. The map from `C[v]` has kernel `(v)` because `C` embeds
in `R_f`. Thus the strict transform is scheme-theoretically `V(v)`.
6. By `prop-nagata-proj-standard-open` and `def-nagata-affine-proj`, the overlap with
the parameter chart is `D(v)`: the actual homogeneous ratio is `(tz)/(fz) = t/f`.
7. The charts cover, so their complements glue to precisely the parameter chart, over
`Spec R[t]`. Finally `J/t` generates the same subalgebra as the fractions `f/t` for `f ∈ I`,
since `(f+tg)/t = f/t+g`.
-/
theorem affine_blowup_complement (I : Ideal R) (m : ℕ) (f : Fin m → I)
    (hf : Ideal.span (Set.range fun i ↦ (f i : R)) = I) :
    ∃ e : AffineBlowup (centerIdeal I) ≅ (center I).blowup,
      e.hom ≫ (center I).blowupMap = AffineBlowup.toSpec (centerIdeal I) ∧
      ∃ jt : Spec (.of (AffineBlowup.chartRing (centerIdeal I) Polynomial.X)) ⟶
          (center I).blowup,
        jt = AffineBlowup.chartRingιOfEq (centerIdeal I) (parameter I).2 rfl
            (reesX_mem _ _ (parameter I).2) ≫ e.hom ∧
        (transformIdeal I).comap jt = ⊤ ∧
        (∀ i : Fin m,
          ∃ θ : Polynomial (AffineBlowup.chartRing I (f i : R)) ≃+*
              AffineBlowup.chartRing (centerIdeal I) (Polynomial.C (f i : R)),
            (∀ c : AffineBlowup.chartRing I (f i : R),
              (θ (Polynomial.C c) : Localization.Away (Polynomial.C (f i : R))) =
                Localization.awayMap Polynomial.C (f i : R) c.val) ∧
            (θ Polynomial.X : Localization.Away (Polynomial.C (f i : R))) =
              AffineBlowup.chartFraction (Polynomial.C (f i : R)) 1 Polynomial.X ∧
            ∃ ji : Spec (.of (Polynomial (AffineBlowup.chartRing I (f i : R)))) ⟶
                (center I).blowup,
              ji = Spec.map (CommRingCat.ofHom θ.symm.toRingHom) ≫
                AffineBlowup.chartRingιOfEq (centerIdeal I) (constant I (f i)).2 rfl
                  (reesX_mem _ _ (constant I (f i)).2) ≫ e.hom ∧
              (transformIdeal I).comap ji =
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
                  (Ideal.span {Polynomial.X} :
                    Ideal (Polynomial (AffineBlowup.chartRing I (f i : R))))))).ker ∧
              ji ⁻¹' Set.range jt =
                {p | Polynomial.X ∉ p.asIdeal} ∧
              ji ⁻¹' ((transformIdeal I).support : Set (center I).blowup)ᶜ =
                ji ⁻¹' Set.range jt) ∧
        Set.range jt = ((transformIdeal I).support : Set (center I).blowup)ᶜ ∧
        (∃ c : Spec (.of (AffineBlowup.chartRing (centerIdeal I) Polynomial.X)) ≅
            Scheme.Opens.toScheme ((transformIdeal I).support.compl),
          c.hom ≫ Scheme.Opens.ι ((transformIdeal I).support.compl) = jt ∧
          c.hom ≫ Scheme.Opens.ι ((transformIdeal I).support.compl) ≫ (center I).blowupMap =
            Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R)
              (AffineBlowup.chartRing (centerIdeal I) Polynomial.X)))) ∧
        AffineBlowup.chartRing (centerIdeal I) Polynomial.X =
          Algebra.adjoin (Polynomial R)
            (Set.range fun a : I ↦
              AffineBlowup.chartFraction (Polynomial.X : Polynomial R) 1
                (Polynomial.C (a : R))) := by
  sorry

end AlgebraicGeometry.DncAffineBlowup
