/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Sheaf.AlgebraicGeometry.SpaceInverseModuleDerivedLimit
public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage

/-! # Finite-presentation realization near the infinitesimal locus

Source: Stacks Project, spaces-flat.tex, Situation 0CX4 and Lemma 0CX9
(blueprint: lem-sfb-space-inverse-modules-near-special-fibre).

The Lean index n is the paper's level n + 1. An open subspace is represented by
its algebraic space W and its representable open immersion j. The maps k are the
factorizations of the actual infinitesimal fibres through this open subspace.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A compatible infinitesimal tower is realized by a finitely presented module on an
open neighborhood of the common special fibre. The final equation uses the existing
tensor-normalized composition comparison, so it respects the specified reduction isos.
Source: Stacks Project, spaces-flat.tex, Tags 0CX4, 0CX5, 0CX7, 0CX8 and 0CX9
(blueprint: lem-sfb-space-inverse-modules-near-special-fibre).

Proof:
1. Apply lem-sfb-space-inverse-module-derived-limit to the given tower. Its bounded
   quasi-coherent homotopy limit K has no negative cohomology and has compatible
   projections q_n to the pushed-forward M_n. Put F_* = H^0(K) and a_n = H^0(q_n).
2. At a point of the special fibre choose an affine etale chart Spec B to X,
   with B finitely presented over A, and a polynomial surjection P to B with
   finitely many variables. Apply lem-sfb-space-inverse-module-polynomial-model
   to get a bounded-above finite-free P-complex E representing derived sections,
   also after principal localization. By lem-sfb-space-inverse-module-affine-base-change
   its derived reductions have cohomology M_n in degree zero only. The affine etale
   realization lem-sfb-affine-etale-derived-module-realization identifies these
   cohomology calculations with sheaf cohomology and detects zero objects.
3. Remove positive terms of E by downward induction. At a positive highest degree,
   reduction modulo A_1 makes the top differential surjective at the chosen point.
   Invert a nonvanishing maximal minor. Write this block as [I D]; the coordinate
   change (v,w) to (v-Dw,w) changes it to [I 0]. The preceding differential lands
   in the complementary free kernel, so delete the split identity two-term complex.
   This homotopy equivalence persists under all reductions. Repeat finitely often,
   obtaining G with no positive terms on a principal neighborhood of the point.
4. Its degree-zero cokernel C is finitely presented over the localized P. The action
   factors through the corresponding localized B; tensoring its finite presentation
   with B gives a finite presentation over B. Affine etale realization identifies
   its associated sheaf with F_* there. Right exactness of tensor and G^{>0}=0 give
   C tensor_A A_n = H^0(G tensor_A A_n). The projection-induced base-change maps
   therefore identify a_n with isomorphisms on this chart, for every n.
5. By lem-a1-space-etale-open-image the images of these chart neighborhoods are open.
   Their union W contains the common special fibre; restrict the single module F_*
   to W. Finite presentation descends from these etale charts. Every X_n factors
   through W, since its image is that same special fibre. The a_n induce the desired
   reduction isomorphisms, as detected on the covering charts. The projection equation
   a_n = t_n a_(n+1), with tensor associativity, gives the final compatibility equation.
   For an empty special fibre take W empty and F zero; every X_n is empty as well.
-/
theorem exists_inverseModule_nearSpecialFibre
    (A : ℕ → CommRingCat.{u}) (r : ∀ n : ℕ, A (n + 1) ⟶ A n)
    (hsurj : ∀ n : ℕ, Function.Surjective (r n))
    (hnil : ∀ (n : ℕ) (a : A (n + 1)), (r n) a = 0 → IsNilpotent a)
    (c : Cone (Functor.ofOpSequence r)) (hc : IsLimit c)
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (f : X ⟶ schemeSpace (inverseModuleSpec c.pt))
    (hsep : MapIsSeparated f) (hfp : ProperQuotFinitePresentation f)
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    (hqc : ∀ n : ℕ, (M n).IsQuasicoherent)
    (hfin : ∀ n : ℕ, (M n).IsFinitePresentation)
    (hflat : ∀ (n : ℕ) (U : (properQuotFibre f (inverseModuleTest c n)).EtaleSite),
      ((schemeRestriction _ U).obj (M n)).IsFlatOver
        (yoneda.preimage (U.obj.hom ≫ (properQuotSnd f (inverseModuleTest c n)).hom.hom)).left)
    (hsupp : ∀ n : ℕ, ∃ (Z : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
      (i : Z ⟶ properQuotFibre f (inverseModuleTest c n)),
      IsRepresentableWith (fun _ _ a ↦ IsClosedImmersion a.left) i.hom.hom ∧
      MapIsProper (i ≫ properQuotSnd f (inverseModuleTest c n)) ∧ ∃ G : Z.Modules,
        G.IsQuasicoherent ∧ G.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj G ≅ M n))
    (e : ∀ n : ℕ,
      (moduleTensorPullback (properQuotFibreMap f (inverseModuleTestMap c n))).obj
        (M (n + 1)) ≅ M n) :
    ∃ (W : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) (j : W ⟶ X),
      IsRepresentableWith (fun _ _ a ↦ IsOpenImmersion a.left) j.hom.hom ∧
      ∃ (k : ∀ n : ℕ, properQuotFibre f (inverseModuleTest c n) ⟶ W),
        (∀ n : ℕ, k n ≫ j = properQuotFst f (inverseModuleTest c n)) ∧
        ∃ (hk : ∀ n : ℕ,
          properQuotFibreMap f (inverseModuleTestMap c n) ≫ k (n + 1) = k n)
          (F : W.Modules),
          F.IsQuasicoherent ∧ F.IsFinitePresentation ∧
          ∃ α : ∀ n : ℕ, (moduleTensorPullback (k n)).obj F ≅ M n,
            ∀ n : ℕ,
              (moduleTensorComposition
                  (properQuotFibreMap f (inverseModuleTestMap c n)) (k (n + 1))).hom.app F ≫
                (eqToIso (congrArg (fun a ↦ (moduleTensorPullback a).obj F) (hk n))).hom ≫
                  (α n).hom =
              (moduleTensorPullback (properQuotFibreMap f (inverseModuleTestMap c n))).map
                (α (n + 1)).hom ≫ (e n).hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
