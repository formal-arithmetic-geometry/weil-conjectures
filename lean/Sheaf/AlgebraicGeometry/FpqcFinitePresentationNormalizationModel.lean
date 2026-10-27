module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.GoingUp
import WeilConjectures.AlgebraicGeometry.FpqcSingletonAffineRefinement
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import WeilConjectures.AlgebraicGeometry.FlatOfFpqcCover
import WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent
import WeilConjectures.AlgebraicGeometry.FpqcDescendQuasiCompact
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange

/-!
# Finitely presented fpqc forms over a normalized semi-trait

Source: Anantharaman, Schémas en groupes, espaces homogènes et espaces algébriques
sur une base de dimension 1, Lemma 4.2.1, printed pp. 55–56; Stacks Tags 09IG,
0AUW, 02KU, 02KY, 02L0 and 02L2.
(blueprint: lem-sfb-fpqc-finite-presentation-normalization-model)
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- An fpqc sheaf over a semi-trait, represented by a flat separated finitely presented
scheme on an fpqc cover, has such a model after normalization in a finite field extension.
The normalized base is again a semi-trait, and its canonical map is integral, surjective,
flat and quasi-compact, an fpqc cover with finite underlying fibres.

Source: Anantharaman, Lemma 4.2.1, printed pp. 55–56, flat separated specialization;
Stacks Tags 09IG, 0AUW, 022B, 02KU, 02KY, 02L0 and 02L2.
(blueprint: lem-sfb-fpqc-finite-presentation-normalization-model)

Proof plan:
1. Refine the original singleton fpqc cover by a finite affine-open coproduct, using
   `lem-galois-fpqc-singleton-affine-refinement`. Base change the given model and use
   `lem-weil-pbc-qcqs-morphism-permanence`. Then
   `lem-sfb-dedekind-fpqc-model-finite-type-stage` produces a flat surjective finitely
   presented affine cover T and a finitely presented model of the restricted sheaf.
2. Apply `lem-sfb-flat-cover-normalization-local-sections` to T. This gives a finite
   extension L/K and a finite open covering of the integral closure's spectrum with
   actual maps to T; pull the model back along these maps.
3. The subfunctor of sections whose structure morphism factors through each such open
   is represented by that local model. Its pullback by a section is the corresponding
   open subscheme, and these cover. The fpqc sheaf is a Zariski sheaf by
   `def-weil-pbc-fpqc-covering`; `lem-pc-schemes-criterion` glues the models to Y.
4. `lem-sc-integral-closure-dedekind-surjective-fibres` gives Noetherianity, normality,
   dimension one, surjectivity and finite fibres. By
   `lem-weil-pbc-integral-maximal-contracts-maximal`, maximal ideals lie above the
   finitely many maximal ideals of R; finite fibres give semilocality. The integral
   closure lies in L and is torsion-free over R, so
   `lem-sfb-dedekind-torsionfree-module-flat` gives flatness. Integrality follows from
   `def-weil-finite-integral-morphism`; affine spectra give quasi-compactness by
   `lem-weil-pbc-qcqs-morphism-permanence`, hence the fpqc condition.
5. Base change the affine refinement, using `lem-galois-fpqc-covering-base-change`.
   This is an affine flat surjective quasi-compact cover of the normalized base.
   Both models represent the same restricted functor, so Yoneda identifies them.
   Use `lem-weil-pbc-flat-morphism-base-change`, `lem-weil-pbc-separated-base-change`
   and `lem-weil-pbc-qcqs-morphism-permanence` on the original model. Descend flatness,
   separatedness, local finite presentation and quasi-compactness via
   `lem-weil-pbc-fpqc-descend-flat`, `lem-weil-pbc-fpqc-descend-separated`,
   `lem-weil-pbc-fpqc-descend-locally-finite-presentation` and
   `lem-weil-pbc-fpqc-descend-quasi-compact`. Finally
   `lem-pc-separated-quasi-separated` supplies quasi-separatedness, completing finite
   presentation. No finiteness of the integral closure as an R-module is required.
-/
theorem exists_fpqc_finite_presentation_normalization_model
    (R K : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Finite (MaximalSpectrum R)]
    [Field K] [Algebra R K] [IsFractionRing R K] (hdim : ringKrullDim R = 1)
    (F : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type v)
    (hF : Presheaf.IsSheaf (Scheme.fpqcTopology.over (Spec (CommRingCat.of R))) F)
    (S' : Scheme.{u}) (p : S' ⟶ Spec (CommRingCat.of R))
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage (Spec (CommRingCat.of R)))
    (P : Over S') (hP : Nonempty (((Over.map p).op ⋙ F).RepresentableBy P))
    [Flat P.hom] [IsSeparated P.hom] [LocallyOfFinitePresentation P.hom]
    [QuasiCompact P.hom] [QuasiSeparated P.hom] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra R L)
      (_ : IsScalarTower R K L) (_ : FiniteDimensional K L),
      IsNoetherianRing (integralClosure R L) ∧
      IsDomain (integralClosure R L) ∧ IsIntegrallyClosed (integralClosure R L) ∧
      ringKrullDim (integralClosure R L) = 1 ∧ Finite (MaximalSpectrum (integralClosure R L)) ∧
      IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L)))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L)))) ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L)))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L)))) ∧
      Presieve.singleton (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L)))) ∈
        Scheme.fpqcPrecoverage (Spec (CommRingCat.of R)) ∧
      (∀ s : Spec (CommRingCat.of R),
        Finite ((Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L)))) ⁻¹' {s})) ∧
      ∃ Y : Over (Spec (CommRingCat.of (integralClosure R L))),
        Flat Y.hom ∧ IsSeparated Y.hom ∧ LocallyOfFinitePresentation Y.hom ∧
        QuasiCompact Y.hom ∧ QuasiSeparated Y.hom ∧
        Nonempty (Functor.RepresentableBy
          ((Over.map (Spec.map
            (CommRingCat.ofHom (algebraMap R (integralClosure R L))))).op ⋙ F) Y) := by
  sorry

end AlgebraicGeometry
