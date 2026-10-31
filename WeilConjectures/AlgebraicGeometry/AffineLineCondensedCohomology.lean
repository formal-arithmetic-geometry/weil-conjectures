/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-! # Ordinary cohomology of the affine line with condensed coefficients

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/
sk-lem-wft-character-integral/lem-fd-affine-line-constant-cohomology.md and its proof.
(blueprint: lem-fd-affine-line-constant-cohomology).

The coefficients are the recorded finite-subextension-valued condensed ring pulled
back from the point. Cohomology means the right derived functors of evaluation at
`X`, the terminal object of the small pro-etale site, on abelian sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The constant section with value `a` of the pulled-back condensed Qbar coefficient.
This applies the existing monoidal inverse image to the existing constant global
section and evaluates the resulting tensor-unit morphism at the integer generator.
Source: the degree-zero normalization of the affine-line cohomology lemma
(blueprint: lem-fd-affine-line-constant-cohomology). -/
def condensedQbarConstantSection (X : Scheme.{v}) (ℓ : ℕ) [Fact ℓ.Prime]
    (a : PadicAlgCl ℓ) :
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X).obj.obj
      (op (Scheme.ProEt.mk (𝟙 X))) :=
  AddCommGrpCat.uliftZMultiplesAddEquiv _
    (((constantSheafAdj (Scheme.ProEt.topology X) AddCommGrpCat.{v + 1}
      (Scheme.ProEt.isTerminalMkId X)).homAddEquiv
        (AddCommGrpCat.of (ULift.{v + 1} ℤ))
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
      (MonObj.Γ.mapFunctorMonoidHom (upperStarFromPoint X)
        (Profinite.PadicAlgCl.constRingHom ℓ a)).hom)

/-- Ordinary constant cohomology of the geometric affine line, including normalization
by constant sections in degree zero.

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/
sk-lem-wft-character-integral/lem-fd-affine-line-constant-cohomology.md and its proof.
(blueprint: lem-fd-affine-line-constant-cohomology).

Proof: Put X = Spec K[t]. It is connected and is a smooth affine curve. For every
n >= 1, the affine-curve dimension bound kills etale cohomology with Z/ell^n
coefficients above degree one. The Kummer sequence kills degree one: K[t] has
unit group K^*, divisible by ell^n, and Pic(X) = 0. Degree zero is Z/ell^n by
constant sections. Finite-coefficient site comparison transfers this computation
to the small pro-etale site, compatibly with constants.

The coefficient comparison identifies Z_ell,X with the inverse limit of these
finite constant sheaves. Their reduction maps are epimorphisms. The continuous
cohomology Milnor sequence, with its lim^1 term zero because the finite-level
cohomology groups are finite, gives Z_ell in degree zero and zero above it.

In positive characteristic the scalar-six comparison for the structural map to
Spec K, followed by exact sections on that geometric point and the normalized
point tensor comparison, gives Qbar_ell in degree zero and zero above it. All
comparisons preserve the unit and hence constants. In characteristic zero use
bounded continuity of sections on the qcqs affine line: first invert ell in
Z_ell,X, then use a finite basis for every finite extension of Q_ell, and finally
take the filtered colimit over finite subextensions. The degree-zero transition
maps are inclusions because they commute with constants. This gives the same
computation in every characteristic, with the stated constant-section map. -/
theorem affineLine_condensedQbar_cohomology
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k))
    (K : Type v) [Field K] [Algebra k K] [IsAlgClosure k K] :
    (∃ e :
      (((Sheaf.sectionsFunctorAt
        (Scheme.ProEt.topology (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))))
        (Scheme.ProEt.mk (𝟙 (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K)))))).rightDerived
          0).obj (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
            (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))))) ≃+ PadicAlgCl ℓ,
      ∀ a : PadicAlgCl ℓ,
        e (((Sheaf.sectionsFunctorAt
          (Scheme.ProEt.topology (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))))
          (Scheme.ProEt.mk
            (𝟙 (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K)))))).toRightDerivedZero.app
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
                (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K)))))
                  (condensedQbarConstantSection
                    (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))) ℓ a)) = a) ∧
    ∀ (q : ℕ), 0 < q →
      IsZero (((Sheaf.sectionsFunctorAt
        (Scheme.ProEt.topology (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))))
        (Scheme.ProEt.mk (𝟙 (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K)))))).rightDerived
          q).obj (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
            (AffineSpace (ULift.{v} (Fin 1)) (Spec (.of K))))) := by
  sorry

end AlgebraicGeometry.ProEtale
