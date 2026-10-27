/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Unramified.Field

/-! # A fibre-regular germ at a separable smooth point

Source: Stacks Project, Tags 057D and 057G; affine differential rank from Tag 02G1,
regularity from Tag 00TT (blueprint: lem-trf-separable-smooth-cotangent-germ).

The transparent chart predicate expands the conclusion, keeping every scalar action
explicit. Tensor factors use extension-of-scalars order, canonically commuting the
factors in the displayed tensors in the node. Its comparison equations specify the
canonical maps on generators and on germs, rather than choosing arbitrary isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Hom

/-- The full affine-chart conclusion of the cotangent-germ lemma. All scalar actions
come from the indicated section maps, evaluations, localization maps and residue map.
The map `j` is specified by its two projections; the localization equivalence is
specified on all elements of the fibre ring; differential comparisons are specified
on differentials and on every germ of a local section. The coordinate comparison is
exactly the extension of the chosen differential basis.

Source: Stacks Project, Tags 057D, 057G, 02G1, 00RV, 00RT and 01UT
(blueprint: lem-trf-separable-smooth-cotangent-germ). -/
noncomputable def SeparableSmoothCotangentGermChart {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) (d : ℕ) (V : S.Opens) (W : X.Opens)
    (hWV : W ≤ f ⁻¹ᵁ V) (hx : x ∈ W) (hs : f x ∈ V)
    (hW : IsAffineOpen W) : Prop :=
  let B := Γ(S, V)
  let A := Γ(X, W)
  let k := S.residueField (f x)
  let L := X.residueField x
  letI : Algebra B A := (f.appLE V W hWV).hom.toAlgebra
  letI : Algebra B k := (S.evaluation V (f x) hs).hom.toAlgebra
  letI : Algebra A L := (X.evaluation W x hx).hom.toAlgebra
  let C := k ⊗[B] A
  Algebra.Smooth B A ∧
    ∃ b : Module.Basis (Fin d) A (KaehlerDifferential B A),
      Algebra.Smooth k C ∧ Algebra.FiniteType k C ∧
      ∃ (j : Spec (.of C) ⟶ f.fiber (f x)) (q : PrimeSpectrum C),
        IsOpenImmersion j ∧
        Set.range j = (f.fiberι (f x)) ⁻¹' (W : Set X) ∧
        j ≫ f.fiberι (f x) =
          Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫ hW.fromSpec ∧
        j ≫ f.fiberToSpecResidueField (f x) =
          Spec.map (CommRingCat.ofHom (algebraMap k C)) ∧
        ∃ hq : j q = f.asFiber x,
        ∃ eR : Localization.AtPrime q.asIdeal ≃+*
            (f.fiber (f x)).presheaf.stalk (f.asFiber x),
          (∀ c : C,
            (j.stalkMap q).hom
              (((f.fiber (f x)).presheaf.stalkCongr (.of_eq hq)).inv
                (eR (algebraMap C (Localization.AtPrime q.asIdeal) c))) =
              ((Scheme.ΓSpecIso (.of C)).inv ≫
                (Spec (.of C)).presheaf.germ ⊤ q trivial) c) ∧
          IsRegularLocalRing (Localization.AtPrime q.asIdeal) ∧
          IsDomain (Localization.AtPrime q.asIdeal) ∧
          ∃ eL : IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal) ≃+* L,
            (∀ t : X.presheaf.stalk x,
              eL (IsLocalRing.residue _ (eR.symm ((f.fiberStalkMap x).hom t))) =
                (X.residue x).hom t) ∧
            (let R := Localization.AtPrime q.asIdeal
             letI : Algebra k R :=
               ((algebraMap C R).comp (algebraMap k C)).toAlgebra
             letI : Algebra R L :=
               (eL.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
             letI : Algebra (X.presheaf.stalk x) L := (X.residue x).hom.toAlgebra
             let E := L ⊗[R] KaehlerDifferential k R
             let EA := L ⊗[A] KaehlerDifferential B A
             let F := L ⊗[X.presheaf.stalk x]
               ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj f.relativeDifferentials)
             ∃ (eA : E ≃ₗ[L] EA) (eCoord : EA ≃ₗ[L] (Fin d → L))
                 (eSheaf : EA ≃ₗ[L] F),
               (∀ (a : A) (l : L),
                 eCoord (l ⊗ₜ[A] KaehlerDifferential.D B A a) =
                   fun i ↦ l * (X.evaluation W x hx) (b.repr
                     (KaehlerDifferential.D B A a) i)) ∧
               (∀ (l : k) (a : A),
                 eA (1 ⊗ₜ[R] KaehlerDifferential.D k R
                   (algebraMap C R (l ⊗ₜ[B] a))) =
                   (f.residueFieldMap x l) • (1 ⊗ₜ[A] KaehlerDifferential.D B A a)) ∧
               (∀ a : A,
                 eSheaf (1 ⊗ₜ[A] KaehlerDifferential.D B A a) =
                   ((1 : L) ⊗ₜ[X.presheaf.stalk x]
                     f.relativeDifferentials.presheaf.germ W x hx
                       (f.relativeDifferentialsDerivation.d (X := op W) a) : F)) ∧
               (∀ (U : X.Opens) (hxU : x ∈ U) (a : Γ(X, U)),
                 eSheaf (eA (1 ⊗ₜ[R] KaehlerDifferential.D k R
                   (eR.symm ((f.fiberStalkMap x).hom (X.presheaf.germ U x hxU a))))) =
                   ((1 : L) ⊗ₜ[X.presheaf.stalk x]
                     f.relativeDifferentials.presheaf.germ U x hxU
                       (f.relativeDifferentialsDerivation.d (X := op U) a) : F)) ∧
               (∃ δ : (IsLocalRing.maximalIdeal R).Cotangent →ₗ[R] E,
                 Function.Surjective δ ∧
                 ∀ z : IsLocalRing.maximalIdeal R,
                   δ ((IsLocalRing.maximalIdeal R).toCotangent z) =
                     1 ⊗ₜ[R] KaehlerDifferential.D k R z.val) ∧
               ∃ h : X.presheaf.stalk x,
                 h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
                 eR.symm ((f.fiberStalkMap x).hom h) ∈ IsLocalRing.maximalIdeal R ∧
                 (1 ⊗ₜ[R] KaehlerDifferential.D k R
                   (eR.symm ((f.fiberStalkMap x).hom h)) : E) ≠ 0 ∧
                 Function.Injective
                   (fun r : R ↦ eR.symm ((f.fiberStalkMap x).hom h) * r))

/-- A positive-dimensional smooth fibre at a closed point with finite separable
residue extension admits a maximal-ideal germ with nonzero relative differential
and injective multiplication on the fibre local ring, together with its affine
and cotangent comparison package.

Source: Stacks Project, Tags 057D and 057G
(blueprint: lem-trf-separable-smooth-cotangent-germ).

Proof:
1. Apply lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension to obtain
   affine neighbourhoods and a differential basis of rank d. Smooth restriction
   and lem-weil-pbc-smooth-ring-map-iff-smooth-affine give smoothness of B → A.
2. The affine fibre chart of lem-trf-affine-fibre-point-dimension identifies the
   fibre over this chart with Spec(k ⊗[B] A). The affine-open stalk localization
   identifies its localization with the fibre stalk. The quotient description
   lem-sbc-scheme-fibre-stalk-quotient identifies the residue field with L.
3. Smoothness survives base change. Apply lem-weil-pbc-smooth-over-field-regular-local
   and lem-sc-regular-local-domain to obtain the regular local domain R.
4. Base change and localization of differentials identify E with EA. Extending
   the chosen basis gives L^d. The affine description of the relative differential
   sheaf and localization of tilde stalks identify EA with the sheaf fibre. All
   comparisons preserve derivations: for any germ a/t both routes give
   t⁻¹ da - a t⁻² dt, by differentiating t t⁻¹ = 1.
5. The Jacobi–Zariski sequence has last term Ω[L/k] = 0 by finite separability
   (lem-trf-separable-field-differentials-vanish). Thus its conormal arrow is
   surjective. Since d ≥ 1, a nonzero vector in L^d lifts to a maximal-ideal
   element with nonzero differential.
6. Lift that element through fiberStalkMap using the quotient description of
   Step 2. The lift lies in the original maximal ideal. Step 4 gives the asserted
   nonzero sheaf differential. Its fibre image is nonzero, hence multiplication
   by it is injective in the domain R. -/
theorem exists_separableSmoothCotangentGermChart {X S : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] (x : X)
    (hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x))))
    (hfinite : (f.residueFieldMap x).hom.Finite)
    (hsep : @Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) _ _
      (f.residueFieldMap x).hom.toAlgebra)
    (d : ℕ) (hd : 1 ≤ d)
    (hdim : topologicalKrullDimAt (f.asFiber x) = (d : WithBot ℕ∞)) :
    ∃ (V : S.Opens) (W : X.Opens) (hWV : W ≤ f ⁻¹ᵁ V)
        (hx : x ∈ W) (hs : f x ∈ V) (hW : IsAffineOpen W),
      IsAffineOpen V ∧ f.SeparableSmoothCotangentGermChart x d V W hWV hx hs hW := by
  sorry

end AlgebraicGeometry.Scheme.Hom
