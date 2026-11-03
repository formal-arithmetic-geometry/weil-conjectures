/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeShriek.NativeShriekDefs

/-! # The native equivariant Leray filtration

Source: latest blueprint, sec-deligne-laumon-general/sk-thm-dl-general-sheaf/
lem-zl-composition-weight-bound.proof.md, paragraph 1 and paragraph 2,
first sentence about subquotients (blueprint: lem-zl-native-leray-filtration).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.DeligneLaumon.NativeShriek

/-- The cohomology of the iterated compact-support image has a finite Weil
filtration whose quotients are constructible subquotients of the E2 terms on
the indicated diagonal. This statement has no weight hypothesis or conclusion.

Source: latest blueprint, lem-zl-composition-weight-bound.proof.md,
paragraph 1 and paragraph 2, first two sentences
(blueprint: lem-zl-native-leray-filtration).

Proof: put K=Rh! F[0] in the ordinary bounded constructible category on Z.
Separated finite-type constructibility stability makes K bounded constructible.
Exact extension by zero followed by the proper right-derived pushforward makes
K nonnegative and T=Rg! exact and left t-exact: exact pullback is t-exact,
and the adjunction Hom test proves the lower bound for proper pushforward.
Use the standard bounded constructible t-structures and their constructible
hearts. The canonical Frobenius pullbacks are exact and t-exact; the
normalized proper/open exchange is shift-compatible and identifies QT with
TP. Apply lem-zl-finite-truncation-spectral-sequence to T and K with these
Frobenius data. Transport the heart to degree-zero constructible modules
using the canonical single/cohomology comparisons. Its E2 identification
then reads R^a g! R^b h! F with the same Weil structure as higherShriek,
by naturality of the truncation unit, counit and exchange. Negative-index
terms vanish. For each fixed n the finite abutment filtration has graded
pieces E-infinity(a,b), a+b=n. Every finite next page is a kernel modulo
an image, with both maps equivariant. Iterating images and inverse images
expresses the limiting page, which stabilizes in the bounded strip, as a
quotient A of a Weil subobject of E2(a,b). The coefficient heart is closed
under kernels and cokernels, so A and the filtration terms are constructible.
Reindex the finite image filtration increasingly by Fin(m+1), from zero to
the abutment, allowing repeated zero steps; the zero abutment may use m=0.
The canonical graded comparison gives the epimorphisms onto the cokernels
of its successive monomorphisms. All endpoint and quotient identifications
are Weil morphisms by the all-page and filtered equivariance equations of
the finite-truncation theorem. This yields the displayed data without any
choice of a derived Weil realization of the strict input pair. -/
theorem lerayFiltration
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ Z₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [QuasiSeparated Z₀.hom]
    [IsSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    [IsSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    (ch : Compactification h₀.left) (cg : Compactification g₀.left)
    (F : NativeL2.WeilModule D l X₀)
    (hF : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left F.carrier) (n : ℕ) :
    ∃ (m : ℕ) (G : Fin (m + 1) → NativeL2.WeilModule D l Y₀)
      (φ : ∀ j : Fin m, G j.castSucc ⟶ G j.succ),
      (∀ j, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber Y₀).left (G j).carrier) ∧
      IsZero (G 0) ∧
      Nonempty (G (Fin.last m) ≅ (cohomology D l Y₀ n).obj
        ((image D l g₀ cg).obj ((image D l h₀ ch).obj ((single D l X₀).obj F)))) ∧
      (∀ j, Mono (φ j)) ∧
      ∀ j : Fin m, ∃ (a b : ℕ), a + b = n ∧
        ∃ (A : NativeL2.WeilModule D l Y₀)
          (i : A ⟶ RelativeCurve.higherShriek D l g₀ cg
            (RelativeCurve.higherShriek D l h₀ ch F b) a)
          (p : A ⟶ cokernel (φ j)),
          Mono i ∧ Epi p ∧
          IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
            (D.geometricFiber Y₀).left A.carrier ∧
          IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
            (D.geometricFiber Y₀).left (cokernel (φ j)).carrier := by
  sorry

end WeilConjectures.DeligneLaumon.NativeShriek
