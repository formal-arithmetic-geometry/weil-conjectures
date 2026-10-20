/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.TraceFormula.LciPointwiseCriterion
public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
import Sheaf.TraceFormula.CILocalRingPrincipalNeighbourhood
import WeilConjectures.RingTheory.SyntomicAtPrimeRelativeGlobalCompleteIntersection

/-!
# A pointwise syntomic affine local model

Source: Stacks Project, Morphisms, Tag 01UE, implication (3) => (2), and the fibre-stalk
identification in lemma-syntomic-flat-fibres; Algebra, Tags 00SG, 00SY and 00SP
(blueprint: lem-trf-syntomic-pointwise-local-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A flat local map of stalks, finite presentation at the given point, and a
complete-intersection fibre local ring give an affine relative-global-complete-intersection
presentation over any prescribed affine neighbourhood of the image.
Source: Stacks Project, Morphisms, Tag 01UE (3) => (2), and Algebra, Tags 00SG, 00SY, 00SP
(blueprint: lem-trf-syntomic-pointwise-local-model).

The hypothesis `hfp` expands the pointwise clause of
`def-sbc-locally-finite-presentation`, rather than requiring finite presentation everywhere.
The hypothesis `hci` is the local-ring condition in `lem-trf-lci-pointwise-criterion`, with
its scalar map induced by the canonical fibre projection. The coefficient ring in the
conclusion is `Γ(S, V)` and the algebra structure on `Γ(X, U)` is the actual map `f.appLE`.
For an affine open these section rings are its canonical affine coordinates.
The presentation predicate includes the asserted dimension of every nonzero fibre.

Proof:
1. Choose affine neighbourhoods `U₀`, `V₀` witnessing `hfp`. The restriction to `U₀` is
   locally of finite presentation: the same pair witnesses it at each of its points.
   Choose an affine neighbourhood of `x` inside `U₀ ∩ f⁻¹(V)` using
   `lem-weil-pbc-affine-opens-basis`. Apply
   `lem-weil-pbc-lfp-affine-opens-finite-presentation` to that restriction and the prescribed
   `V`. This yields a finitely presented coordinate map `R → B` over that exact `V`.
2. The affine stalk identifications identify its localized map `R_p → B_q` with
   `f.stalkMap x`, so it is flat by `hflat` (`def-weil-flat-morphism`).
3. The affine fibre calculation (`def-pc-scheme-fibre`) identifies the localization of
   `B ⊗[R] κ(p)` at the canonical fibre prime with the stalk at `f.asFiber x`. Its local
   complete-intersection presentation is `hci`. Apply
   `lem-trf-ci-local-ring-principal-neighbourhood` to get a principal global-complete-
   intersection neighbourhood of that fibre prime (Stacks Algebra, Tag 00SG).
4. Apply `lem-weil-pbc-syntomic-at-prime-relative-global-complete-intersection` with `g=1`
   to the finitely presented map of step 1, flatness of step 2 and the fibre neighbourhood
   of step 3. It gives `g' ∉ q` and the required relative global complete intersection
   polynomial quotient isomorphic as an `R`-algebra to `B[1/g']` (Tag 00SY).
   The principal open `D(g')` is an affine neighbourhood of `x` still mapping into `V`.
5. By `def-weil-pbc-relative-global-complete-intersection`, the specified quotient has
   dimension `n-c` in each nonzero fibre (Tag 00SP), giving the final clause.
-/
theorem syntomic_pointwise_local_model
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (V : S.Opens) (hV : IsAffineOpen V) (hxV : f x ∈ V)
    (hfp : ∃ (U₀ : X.Opens) (V₀ : S.Opens),
      IsAffineOpen U₀ ∧ IsAffineOpen V₀ ∧ x ∈ U₀ ∧
        ∃ e₀ : U₀ ≤ f ⁻¹ᵁ V₀, (f.appLE V₀ U₀ e₀).hom.FinitePresentation)
    (hflat : (f.stalkMap x).hom.Flat)
    (hci : ∃ (A : Type u) (_ : CommRing A) (_ : Algebra (S.residueField (f x)) A)
      (_ : IsLocalRing A) (_ : IsNoetherianRing A),
      IsRegularLocalRing A ∧ Algebra.EssFiniteType (S.residueField (f x)) A ∧
        ∃ rs : List A, RingTheory.Sequence.IsRegular A rs ∧
          Nonempty
            (@AlgEquiv (S.residueField (f x))
              (A ⧸ Ideal.span (Set.range (fun i : Fin rs.length => rs.get i)))
              ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) _ _ _ _
              (((Scheme.ΓSpecIso (S.residueField (f x))).inv ≫
                (f.fiberToSpecResidueField (f x)).appLE ⊤ ⊤ le_top ≫
                (f.fiber (f x)).presheaf.germ ⊤ (f.asFiber x) trivial).hom.toAlgebra))) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∃ (e : U ≤ f ⁻¹ᵁ V) (n c : ℕ) (h : Fin c → MvPolynomial (Fin n) Γ(S, V)),
        Algebra.IsRelativeGlobalCompleteIntersectionPresentation h ∧
          Nonempty
            (@AlgEquiv Γ(S, V) Γ(X, U)
              (MvPolynomial (Fin n) Γ(S, V) ⧸ Ideal.span (Set.range h))
              _ _ _ (f.appLE V U e).hom.toAlgebra _) := by
  sorry

end AlgebraicGeometry
