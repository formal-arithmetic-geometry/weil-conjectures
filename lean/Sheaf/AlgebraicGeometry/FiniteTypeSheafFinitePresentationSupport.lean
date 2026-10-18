/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde

/-!
# A finitely presented closed subscheme supporting a finite type sheaf on one fibre

Source: Stacks Project, More on Flatness, Tag 057Q, lemma-sheaf-lives-on-subscheme
(blueprint: lem-trf-finite-type-sheaf-fp-support).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- A finite type quasi-coherent module on an affine finite type scheme is the pushforward
of a finite type quasi-coherent module on a finitely presented closed subscheme whose
fibre at the image of the chosen point is precisely the support of the pulled-back module.
The fibre is identified with its image under the canonical base change of the immersion;
support means the locus of nonzero stalks.
Source: Stacks Project, More on Flatness, Tag 057Q, lemma-sheaf-lives-on-subscheme
(blueprint: lem-trf-finite-type-sheaf-fp-support).

Proof:
1. Write S = Spec A, X = Spec B and F = tilde M using
   lem-weil-pbc-affine-tilde-gamma-adjunction. By lem-weil-pbc-lft-affine-pairs,
   A → B is finite type. By lem-weil-pbc-quasi-coherent-finite-type-affine,
   M is finite over B. Set I = Ann_B(M).
2. Put s = f(x), k = κ(s), R = B ⊗_A k. The affine fibre-product and tilde-pullback
   formulas (lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-tilde-pullback-base-change and def-pc-module-pullback) identify
   X_s with Spec R and F_s with the tilde of M ⊗_A k. The support theorems
   lem-weil-pbc-finite-type-module-support-closed and
   lem-weil-pbc-support-pullback-finite-type give Supp(F_s) = V(IR): pulling back
   V(I) along Spec R → Spec B gives V(IR).
3. By lem-wf-affine-noetherian-components, the finite type k-algebra R is Noetherian.
   Choose finitely many elements of I whose images generate IR and let J be their
   ideal in B. Then J ⊆ I and JR = IR.
4. Set Z = Spec(B/J). The quotient map defines a closed immersion j : Z → X
   (def-weil-closed-immersion), of finite presentation since J is finitely generated
   (def-sbc-locally-finite-presentation); affine morphisms are quasi-compact and
   quasi-separated. Regard M as a B/J-module and let H be its tilde on Z.
   It is quasi-coherent and finite type by lem-weil-pbc-quasi-coherent-finite-type-affine.
   The affine pushforward formula (lem-weil-pbc-pushforward-tilde-spec and
   lem-weil-pbc-spec-module-tilde-sections) gives j_*H ≅ F.
5. By lem-weil-pbc-fibre-product-affine-spectra and right exactness of tensor,
   Z_s = Spec(R/JR), whose image in Spec R is V(JR) = V(IR) = Supp(F_s). -/
theorem exists_finitePresentation_closedImmersion_fiber_support
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (x : X) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X),
      IsClosedImmersion j ∧ LocallyOfFinitePresentation j ∧ QuasiCompact j ∧
        QuasiSeparated j ∧
        ∃ H : Z.Modules, H.IsFiniteType ∧ H.IsQuasicoherent ∧
          Nonempty ((pushforward j).obj H ≅ F) ∧
          Set.range
            (pullback.map (j ≫ f) (S.fromSpecResidueField (f x))
              f (S.fromSpecResidueField (f x)) j
              (𝟙 (Spec (S.residueField (f x)))) (𝟙 S) (by simp) (by simp)).base =
            {z : Limits.pullback (C := Scheme.{u}) f (S.fromSpecResidueField (f x)) |
              ¬ Subsingleton
                (((tensorPullback
                  (pullback.fst f (S.fromSpecResidueField (f x)))).obj F).presheaf.stalk z)} := by
  sorry

end AlgebraicGeometry.Scheme.Modules
