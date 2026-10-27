/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import WeilConjectures.Mathlib.RingTheory.Henselian

import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.TraceFormula.FiniteBaseSplitsEtale
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import Mathlib.RingTheory.Flat.TorsionFree
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence

/-!
# Finite-presentation invariant opens of a flat group sheaf over a strict trait

Source: Anantharaman, Schémas en groupes, §4.2, Lemma 4.2.4 and the action argument,
printed pp.59–61, with the node's normalization construction for generic-only pieces
(blueprint: lem-sfb-flat-trait-group-finite-component-opens).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Restriction of a subfunctor to schemes over a new base, by composition of structure maps.
Source: Anantharaman, §4.2, change of base of the open pieces
(blueprint: lem-sfb-flat-trait-group-finite-component-opens). -/
def traitPieceRestriction {S T : Scheme.{u}} (p : T ⟶ S)
    {F : (Over S)ᵒᵖ ⥤ Type u} (H : Subfunctor F) :
    Subfunctor ((Over.map p).op ⋙ F) where
  obj W := H.obj ((Over.map p).op.obj W)
  map i := H.map ((Over.map p).op.map i)

/-- The canonical morphism from the spectrum of the integral closure in an extension field.
Source: Anantharaman, §4.2.1, normalization of the trait
(blueprint: lem-sfb-flat-trait-group-finite-component-opens). -/
noncomputable def traitPieceNormalizationMap (R L : Type u) [CommRing R] [Field L] [Algebra R L] :
    Spec (.of (integralClosure R L)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L)))

/-- Finite-presentation subgroup and invariant open pieces, homogeneous fppf-locally after
normalization in finite, possibly ramified extensions of the fraction field.
Source: Anantharaman, Lemma 4.2.4 and its action argument, printed pp.59–61;
the generic-only pieces use the normalization construction recorded in the node
(blueprint: lem-sfb-flat-trait-group-finite-component-opens).

Proof plan:
1. Apply lem-sfb-trait-component-minimal-envelope to the neutral special-fibre component.
   Inversion preserves its envelope H. Over the strictly henselian DVR the neutral-product
   clause identifies the product envelope with H × H. Multiplication is a flat locally
   finitely presented projection up to (x,y) ↦ (xy,y), using flat base-change and
   lem-weil-pbc-qcqs-morphism-permanence. Envelope compatibility makes H a subgroup;
   its representing pullback is separated, flat and finitely presented.
2. Use lem-sfb-fpqc-open-subgroup-coset-space and pull its covering opens Q_a back to F.
   The inverse images U_a cover on every scheme test and are invariant. The quotient map
   over T and each Q_a over the base are finitely presented, so composition gives finite
   presentation, by lem-sfb-space-separated-fp-composition. Restriction of P gives flatness
   and separatedness; locality uses lem-sfb-space-flat-proper-fp-locality.
3. Apply lem-trf-finite-base-splits-etale to the finite affine separated etale atlas of Q_a,
   obtaining a finite surjection C_a over S on which the atlas splits into open schemes.
4. Choose a generic point of C_a and take the fraction field L of its integral component.
   This is finite over Frac(R). The finite algebra maps to integralClosure R L because
   its elements are integral, by the characteristic-polynomial argument.
5. Apply lem-sc-integral-closure-dedekind-surjective-fibres. Its dimension-one normal
   Noetherian domain is semilocal since all maximal ideals lie over the closed point and
   that fibre is finite. Torsion freeness over the DVR gives flatness by
   lem-weil-pbc-pid-torsion-free-module-flat. The affine integral map is quasi-compact
   and surjective, hence fpqc; no module-finiteness of the normalization is used.
6. Pull the split atlas back to this normalization. Its sections are open immersions by
   lem-trf-space-chartwise-etale-permanence and lem-sfb-space-etale-monomorphism-open.
   Their inverse images in F give finitely many invariant opens covering U_a. The quotient
   torsor identity identifies (h,x) ↦ (hx,x) with an isomorphism on each such piece, hence
   gives fppf-local lifts.
7. Pulling back the inverse and its identities preserves that isomorphism. Inverse images
   preserve the invariant opens and their cover. The universal scheme-test quantifiers in
   the conclusion express these local lifts over every further base change. -/
theorem flatTraitGroup_finite_component_opens
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsStrictlyHenselianLocalRing R]
    (F : (Over (Spec (.of R)))ᵒᵖ ⥤ GrpCat.{u})
    (hF : Presieve.IsSheaf (Scheme.fpqcTopology.over (Spec (.of R)))
      (F ⋙ forget GrpCat))
    (T : Scheme.{u}) (p : T ⟶ Spec (.of R))
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage (Spec (.of R)))
    (P : Over T) [IsSeparated P.hom] [Flat P.hom]
    [LocallyOfFinitePresentation P.hom]
    (e : (Over.map p).op ⋙ (F ⋙ forget GrpCat) ≅ yoneda.obj P) :
    ∃ (H : Subfunctor (F ⋙ forget GrpCat))
      (A : Type (u + 1)) (U : A → Subfunctor (F ⋙ forget GrpCat)),
      (∀ W, ∃ G : Subgroup (F.obj W), (G : Set (F.obj W)) = H.obj W) ∧
      AlgebraicSpace.IsRepresentableWith (fun _ _ i ↦ IsOpenImmersion i.left) H.ι ∧
      (∀ a, AlgebraicSpace.IsRepresentableWith
        (fun _ _ i ↦ IsOpenImmersion i.left) (U a).ι) ∧
      (⨆ a, U a).sheafify (Scheme.zariskiTopology.over (Spec (.of R))) = ⊤ ∧
      (∀ a W (h x : F.obj W), h ∈ H.obj W → x ∈ (U a).obj W →
        h * x ∈ (U a).obj W) ∧
      (∃ X : Over T, Nonempty ((Over.map p).op ⋙ H.toFunctor ≅ yoneda.obj X) ∧
        IsSeparated X.hom ∧ Flat X.hom ∧ LocallyOfFinitePresentation X.hom ∧
        QuasiCompact X.hom ∧ QuasiSeparated X.hom) ∧
      (∀ a, ∃ X : Over T,
        Nonempty ((Over.map p).op ⋙ (U a).toFunctor ≅ yoneda.obj X) ∧
        IsSeparated X.hom ∧ Flat X.hom ∧ LocallyOfFinitePresentation X.hom ∧
        QuasiCompact X.hom ∧ QuasiSeparated X.hom) ∧
      ∀ a, ∃ (L : Type u) (_ : Field L) (_ : Algebra (FractionRing R) L)
        (_ : Algebra R L) (_ : IsScalarTower R (FractionRing R) L),
        FiniteDimensional (FractionRing R) L ∧
        IsIntegralHom (traitPieceNormalizationMap R L) ∧
        Surjective (traitPieceNormalizationMap R L) ∧
        Flat (traitPieceNormalizationMap R L) ∧
        QuasiCompact (traitPieceNormalizationMap R L) ∧
        (∀ s, Set.Finite ((traitPieceNormalizationMap R L) ⁻¹' {s})) ∧
        IsDomain (integralClosure R L) ∧ IsNoetherianRing (integralClosure R L) ∧
        IsIntegrallyClosed (integralClosure R L) ∧
        ringKrullDim (integralClosure R L) = 1 ∧
        Finite (MaximalSpectrum (integralClosure R L)) ∧
        ∃ (n : ℕ) (V : Fin n →
          Subfunctor ((Over.map (traitPieceNormalizationMap R L)).op ⋙
            (F ⋙ forget GrpCat))),
          (∀ j, V j ≤ traitPieceRestriction (traitPieceNormalizationMap R L) (U a)) ∧
          (∀ j, AlgebraicSpace.IsRepresentableWith
            (fun _ _ i ↦ IsOpenImmersion i.left) (V j).ι) ∧
          (⨆ j, V j).sheafify
            (Scheme.zariskiTopology.over (Spec (.of (integralClosure R L)))) =
              traitPieceRestriction (traitPieceNormalizationMap R L) (U a) ∧
          (∀ j W (h x : F.obj ((Over.map (traitPieceNormalizationMap R L)).op.obj W)),
            h ∈ (traitPieceRestriction (traitPieceNormalizationMap R L) H).obj W →
            x ∈ (V j).obj W → h * x ∈ (V j).obj W) ∧
          ∀ j (W : Over (Spec (.of (integralClosure R L))))
            (x y : F.obj (op ((Over.map (traitPieceNormalizationMap R L)).obj W))),
            x ∈ (V j).obj (op W) → y ∈ (V j).obj (op W) →
            ∃ (I : Type u) (Wᵢ : I → Over (Spec (.of (integralClosure R L))))
              (f : ∀ i, Wᵢ i ⟶ W),
              Presieve.ofArrows (fun i ↦ (Wᵢ i).left) (fun i ↦ (f i).left) ∈
                Scheme.fppfPrecoverage W.left ∧
              ∀ i, ∃ h : F.obj (op ((Over.map (traitPieceNormalizationMap R L)).obj (Wᵢ i))),
                h ∈ (traitPieceRestriction (traitPieceNormalizationMap R L) H).obj
                  (op (Wᵢ i)) ∧
                h * (F.map ((Over.map (traitPieceNormalizationMap R L)).map (f i)).op y) =
                  F.map ((Over.map (traitPieceNormalizationMap R L)).map (f i)).op x := by
  sorry

end AlgebraicGeometry
