/-
Copyright (c) 2026 SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.ProjectiveFibreHilbertPolynomial
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.RingTheory.FlatModuleAtPrime
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality

/-! # The flat closure of a generic projective closed subscheme over a DVR

Source: Grothendieck, Bourbaki Expose 221, Lemma 3.7, printed pp.264--265,
and Theorem 3.2 (blueprint: lem-sfb-projective-dvr-flat-closure).

Closed subschemes are Mathlib ideal-sheaf data, so generic restriction and uniqueness
are equalities of ideals, retaining the embeddings. Kernels of restriction maps express
contraction without assuming the ambient coordinate rings are torsion-free.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.ProjectiveDvrFlatClosure

/-- Restriction from an ambient affine chart to the prescribed generic closed subscheme.
On `U = Spec C` the codomain is `(C tensor_R K)/J_K`; its kernel is precisely the
contraction of `J_K`. This definition uses the actual structural maps.
Source: Bourbaki Expose 221, Lemma 3.7, kernel construction
(blueprint: lem-sfb-projective-dvr-flat-closure). -/
def genericChartMap {E S T : Scheme.{u}} (f : E ⟶ S) (h : T ⟶ S)
    (I : (pullback f h).IdealSheafData) (U : E.affineOpens) :
    Γ(E, U) →+* Γ(I.subscheme, (I.subschemeι ≫ pullback.fst f h) ⁻¹ᵁ U) :=
  ((I.subschemeι ≫ pullback.fst f h).app U).hom

/-- The scalar map on the affine quotient chart, formed from the specified map to Spec R,
the canonical global sections of Spec R, restriction to U, and the quotient map.
Source: Bourbaki Expose 221, Lemma 3.7, affine quotient construction
(blueprint: lem-sfb-projective-dvr-flat-closure). -/
def quotientScalarMap {R : Type u} [CommRing R] {E : Scheme.{u}}
    (f : E ⟶ Spec (.of R)) (I : E.IdealSheafData) (U : E.affineOpens) :
    R →+* Γ(E, U) ⧸ I.ideal U :=
  (Ideal.Quotient.mk (I.ideal U)).comp
    (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫
      E.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom)

/-- The prescribed generic closed subscheme has exactly one flat finitely presented
closed extension. The affine contraction, its compatibility with every localization and
with restriction on overlaps, torsion-freeness of each quotient, quotient flatness, and the
common geometric Hilbert polynomial are included. No flatness of E, excellence of R,
reducedness or nonemptiness is assumed.

Source: Bourbaki Expose 221, Lemma 3.7 and its proof, printed pp.264--265;
Theorem 3.2 and Stacks Tag 0B9T for the Hilbert polynomial
(blueprint: lem-sfb-projective-dvr-flat-closure).

Proof for stage 3:
1. Compose the generic closed immersion with the generic-fibre projection. Its inverse
   images of affine opens are Spec((C tensor_R K)/J_K), so it is affine, hence qcqs
   (lem-weil-pbc-affine-scheme-qcqs, lem-pc-separated-quasi-separated). Pushforward of its
   structure module is quasi-coherent (pqf-lem-pushforward-qcoh). Its kernel is a
   quasi-coherent ideal (lem-weil-pbc-quasi-coherent-module-kernel), with the stated ideals.
2. A localized fraction c/t vanishes exactly when some u in the multiplicative subset
   kills the image of c. This proves the localized-kernel formula. On overlaps the kernel
   maps are the restrictions of one sheaf, hence agree and satisfy the cocycle condition.
   Lem-weil-pbc-quasi-coherent-ideal-closed-subscheme constructs I.subscheme. Inverting
   nonzero R-scalars recovers J_K: a numerator of an element c/r in J_K lies in J_K.
3. Each C/I injects into (C tensor_R K)/J_K. Nonzero R-scalars act invertibly on that
   K-vector space, hence injectively on C/I. A DVR is a PID, so
   lem-weil-pbc-pid-torsion-free-module-flat gives quotient flatness. The affine criterion
   lem-weil-pbc-flat-morphism-affine-criterion and lem-pc-affine-flat-module-local-criterion
   give flatness of the scheme.
4. The embedding of E is projective (def-kun-projective), hence proper by
   lem-kun-projective-implies-proper. Its closed subscheme is proper by
   lem-weil-pbc-closed-immersion-proper, hence separated, quasi-compact, quasi-separated,
   and finite type (def-weil-proper-morphism, def-weil-finite-type-morphism and
   lem-pc-separated-quasi-separated). The composite closed embedding gives its polarization.
5. A DVR is Noetherian (def-weil-pbc-noetherian-ring). The quotient charts are finite
   type, hence finitely presented by lem-weil-pbc-finite-type-noetherian-finite-presentation.
   Together with qcqs this gives finite presentation (def-sbc-locally-finite-presentation).
6. For another flat closed extension J, its affine quotient is torsion-free by
   lem-trf-flat-module-torsionfree-domain. It injects into its generic localization, so
   its kernel is the same contraction. The ideals agree on every affine open, giving
   equality as ideal sheaves (def-sbc-closed-immersion-ideal-sheaf).
7. Lem-sfb-flat-projective-hilbert-polynomial-locality gives locally constant fibre
   polynomials, invariant under field extension. Spec R is irreducible, so this function
   equals its generic value everywhere. Interpret it by
   def-sfb-projective-fibre-hilbert-polynomial. For the empty generic subscheme all
   contracted ideals are the unit ideal, giving the empty extension and zero polynomial.
-/
theorem exists_unique_projective_dvr_flat_closure
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (n : ℕ) {E : Scheme.{u}}
    (i : E ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R))) [IsClosedImmersion i]
    (I_K : (pullback (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).IdealSheafData) :
    ∃ I : E.IdealSheafData,
      Flat (I.subschemeι ≫ i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R))) ∧
      LocallyOfFinitePresentation
        (I.subschemeι ≫ i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R))) ∧
      QuasiCompact
        (I.subschemeι ≫ i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R))) ∧
      QuasiSeparated
        (I.subschemeι ≫ i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R))) ∧
      I.comap (pullback.fst (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R)))
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))) = I_K ∧
      (∀ J : E.IdealSheafData,
        Flat (J.subschemeι ≫ i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R))) →
        LocallyOfFinitePresentation
          (J.subschemeι ≫ i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R))) →
        QuasiCompact
          (J.subschemeι ≫ i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R))) →
        QuasiSeparated
          (J.subschemeι ≫ i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R))) →
        J.comap (pullback.fst (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R)))
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))) = I_K → J = I) ∧
      (∀ U : E.affineOpens,
        I.ideal U = RingHom.ker
          (genericChartMap (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R)))
            (Spec.map (CommRingCat.ofHom (algebraMap R K))) I_K U)) ∧
      (∀ U : E.affineOpens, ∀ T : Submonoid Γ(E, U),
        (I.ideal U).map (algebraMap Γ(E, U) (Localization T)) =
          RingHom.ker (IsLocalization.map
            (Localization (T.map
              (genericChartMap (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R)))
                (Spec.map (CommRingCat.ofHom (algebraMap R K))) I_K U)))
            (genericChartMap (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R)))
              (Spec.map (CommRingCat.ofHom (algebraMap R K))) I_K U)
            T.le_comap_map)) ∧
      (∀ (U V : E.affineOpens) (h : U ≤ V),
        (I.ideal V).map (E.presheaf.map (homOfLE h).op).hom = I.ideal U) ∧
      (∀ U : E.affineOpens,
        (∀ r : R, r ≠ 0 → Function.Injective
          (fun x : Γ(E, U) ⧸ I.ideal U ↦
            quotientScalarMap
              (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R))) I U r * x)) ∧
        (quotientScalarMap
          (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R))) I U).Flat) ∧
      (∃ P : NumericalHilbertPolynomial,
        HasProjectiveFibreHilbertPolynomial
          (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R))) i
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)))) I_K P.val ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of R)),
          HasProjectiveFibreHilbertPolynomial
            (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R))) i (Over.mk s)
            (I.comap (pullback.fst
              (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R))) s)) P.val) := by
  sorry

end AlgebraicGeometry.ProjectiveDvrFlatClosure
