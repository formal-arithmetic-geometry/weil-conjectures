/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.Galois.Basic
public import Sheaf.FieldTheory.FieldTower
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import WeilConjectures.AlgebraicGeometry.GenericComponentsSplit
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorDecomposition
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Galois component presentation

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, 2.3 Step 2,
printed p.150; Stacks Project, Tags 054R, 033C and 02OO.
(blueprint: lem-sfb-galois-component-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A normal geometrically reduced proper integral variety has a geometrically integral
clopen component over a finite Galois extension. The Galois action is specified by its
projections, with inverse on scalars because `Spec` is contravariant. Its component
stabilizer acts by restriction. Faithfulness on the field is inherent in its being a
subgroup of the field automorphism group. The geometric-fibre orbit assertion uses
field-valued lifts, retaining their residue-field embeddings, rather than underlying
points in the original scheme. For a finite etale map these lifts are exactly the points
of the geometric fibre. Cartier stability is equality of pulled-back ideals.

Source: ILO, Travaux de Gabber, Expose X, 2.3 Step 2, printed p.150;
Stacks Project, Tags 054R, 033C and 02OO.
(blueprint: lem-sfb-galois-component-presentation)

Proof (the ten steps of the DAG):
1. Every field base change is finite type over a field, hence Noetherian, by
   lem-sfb-finite-type-composition-base-change and lem-weil-pbc-finite-type-over-noetherian.
2. Split the geometric components by lem-sbc-generic-components-split. The splitting
   extension is separable by lem-weil-pbc-etale-residue-field-extension-separable;
   embed it in a finite Galois extension using
   lem-weil-pbc-finite-galois-receiving-separable-extensions.
3. The projection after either extension is finite etale surjective, by
   lem-weil-pbc-spec-finite-ring-map-finite, lem-weil-pbc-finite-separable-extension-etale,
   lem-pc-field-extension-surjective, lem-trf-finite-radicial-basechange, and
   lem-weil-pbc-etale-covering-base-change. Apply lem-fin-etale-normal-components:
   the base change is a finite disjoint union of clopen normal integral components.
4. Each split component remains irreducible after further field extension; it is reduced
   as an open of a geometrically reduced base change. It is therefore geometrically
   integral. It is proper by lem-weil-pbc-proper-base-change and
   lem-weil-pbc-closed-immersion-proper. Choose one component U.
5. The fibre-product universal property defines the action id times Spec of the inverse
   automorphism. Restrict to the stabilizer of U to get its semilinear action.
6. Each component map to B is etale by lem-weil-pbc-open-immersion-etale and
   lem-weil-pbc-etale-covering-composition. It is finite by
   lem-weil-pbc-closed-immersion-finite and lem-weil-pbc-finite-composition, thus proper
   by lem-weil-pbc-finite-proper. Its image is nonempty, closed and open (use
   lem-weil-pbc-etale-morphism-open-map), hence all of the integral scheme B.
7. At a geometric point with field Omega, embed L in Omega using
   lem-weil-pbc-algebraic-extension-embeds-algebraically-closed. By
   lem-exc-finite-galois-tensor-decomposition and lem-weil-pbc-fibre-product-affine-spectra,
   Omega tensor L is the product of Omega indexed by Aut_e(L). The action is simply
   transitive on its coordinate points, including their residue-field embeddings.
8. Every component meets every geometric fibre by lem-weil-pbc-surjective-base-change.
   Transitivity on that fibre implies transitivity on components. An element sending
   two lifts in U to each other stabilizes U since distinct components are disjoint.
9. The stabilizer acts faithfully on L by inclusion. If it acts identically on U,
   semilinearity at any point of the nonempty U and injectivity of the structural
   field homomorphism into its residue field show that its scalar automorphism is 1.
10. Etale implies flat. By lem-pc-flat-pullback-effective-cartier-ideal the pullback
    Cartier ideal is Cartier and has the inverse-image support. Invariance of the
    component map makes this ideal stable under every stabilizer element. This also
    applies to the empty divisor.
-/
theorem exists_galois_component_presentation
    (e : Type u) [Field e] (B : Scheme.{u}) (b : B ⟶ Spec (.of e))
    [IsIntegral B] [IsProper b]
    [GeometricallyReduced b]
    (hBnormal : ∀ x : B, IsDomain (B.presheaf.stalk x) ∧
      IsIntegrallyClosed (B.presheaf.stalk x)) :
    IsNoetherian B ∧
    ∃ (L : Type u) (_ : Field L) (_ : Algebra e L),
      Module.Finite e L ∧ IsGalois e L ∧
      ∃ (U : (pullback b (Spec.map (CommRingCat.ofHom (algebraMap e L)))).Opens)
        (a : (L ≃ₐ[e] L) →*
          Aut (pullback b (Spec.map (CommRingCat.ofHom (algebraMap e L)))))
        (H : Subgroup (L ≃ₐ[e] L)) (r : H →* Aut U.toScheme),
        IsClosed (U : Set ↥(pullback b (Spec.map (CommRingCat.ofHom (algebraMap e L))))) ∧
        (U : Set ↥(pullback b (Spec.map (CommRingCat.ofHom (algebraMap e L))))) ∈
          irreducibleComponents ↥(pullback b (Spec.map (CommRingCat.ofHom (algebraMap e L)))) ∧
        IsIntegral U.toScheme ∧
        (∀ x : U.toScheme, IsDomain (U.toScheme.presheaf.stalk x) ∧
          IsIntegrallyClosed (U.toScheme.presheaf.stalk x)) ∧
        IsProper (U.ι ≫ pullback.snd b (Spec.map (CommRingCat.ofHom (algebraMap e L)))) ∧
        GeometricallyIntegral
          (U.ι ≫ pullback.snd b (Spec.map (CommRingCat.ofHom (algebraMap e L)))) ∧
        (∀ g : L ≃ₐ[e] L,
          (a g).hom ≫ pullback.fst b (Spec.map (CommRingCat.ofHom (algebraMap e L))) =
            pullback.fst b (Spec.map (CommRingCat.ofHom (algebraMap e L))) ∧
          (a g).hom ≫ pullback.snd b (Spec.map (CommRingCat.ofHom (algebraMap e L))) =
            pullback.snd b (Spec.map (CommRingCat.ofHom (algebraMap e L))) ≫
              Spec.map (CommRingCat.ofHom g.symm.toRingHom)) ∧
        (∀ Z ∈ irreducibleComponents
            ↥(pullback b (Spec.map (CommRingCat.ofHom (algebraMap e L)))),
          ∃ g : L ≃ₐ[e] L, (a g).hom '' (U : Set _) = Z) ∧
        (∀ g : L ≃ₐ[e] L, g ∈ H ↔ (a g).hom '' (U : Set _) = (U : Set _)) ∧
        (∀ h : H, (r h).hom ≫ U.ι = U.ι ≫ (a h.val).hom) ∧
        Function.Injective r ∧
        IsFinite (U.ι ≫ pullback.fst b (Spec.map (CommRingCat.ofHom (algebraMap e L)))) ∧
        Etale (U.ι ≫ pullback.fst b (Spec.map (CommRingCat.ofHom (algebraMap e L)))) ∧
        Surjective (U.ι ≫ pullback.fst b (Spec.map (CommRingCat.ofHom (algebraMap e L)))) ∧
        (∀ h : H, (r h).hom ≫ U.ι ≫
            pullback.fst b (Spec.map (CommRingCat.ofHom (algebraMap e L))) =
          U.ι ≫ pullback.fst b (Spec.map (CommRingCat.ofHom (algebraMap e L)))) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x y : Spec (.of Ω) ⟶ U.toScheme),
          x ≫ U.ι ≫ pullback.fst b (Spec.map (CommRingCat.ofHom (algebraMap e L))) =
            y ≫ U.ι ≫ pullback.fst b (Spec.map (CommRingCat.ofHom (algebraMap e L))) →
          ∃ h : H, x ≫ (r h).hom = y) ∧
        (∀ (I : B.IdealSheafData), I.IsInvertible →
          ∃ J : U.toScheme.IdealSheafData,
            J.IsInvertible ∧
            (J.support : Set U.toScheme) =
              (U.ι ≫ pullback.fst b (Spec.map (CommRingCat.ofHom (algebraMap e L)))) ⁻¹'
                (I.support : Set B) ∧
            ∀ h : H, J.comap (r h).hom = J) := by
  sorry

end AlgebraicGeometry
