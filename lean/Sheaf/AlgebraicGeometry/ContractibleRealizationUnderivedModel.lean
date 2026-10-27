/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat

/-! An ordinary module model for scalar realization.

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), equations (3.1)--(3.2).
(blueprint: lem-zl-contractible-realization-underived-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

/-- An ordinary scalar-extension/constant-module left adjoint whose total left derivative
is the fixed realization functor.  No exactness assumption on sections is required.

Source: Hemo--Richarz--Scholbach, Section 3, Remark 3.2; Stacks 03D3 and 06YY.
(blueprint: lem-zl-contractible-realization-underived-model).

Proof: put L(M) equal to the internal module associated with the sheafification of
V ↦ O(V) tensor_A M, with restrictions induced by those of O and by U's terminal maps.
Tensor adjunction and sheafification adjunction identify maps L(M) → N with A-linear
maps M → N(U), naturally in both arguments. This proves the ordinary adjunction.
Addition of maps is preserved sectionwise. Give L its strong symmetric structure by
the balanced map (a tensor x) tensor (b tensor y) ↦ ab tensor (x tensor y), with inverse
inserting 1; tensor associativity, unit and symmetry are checked on these generators.
If M is flat over A, tensoring with L(M) identifies with sheafification of tensoring
section modules with M, hence is exact. Thus L preserves flat objects. An acyclic K-flat A-complex
remains acyclic
after tensoring with each O(V), so L preserves quasi-isomorphisms between K-flat complexes.
For a flat-term K-flat A-resolution P, exact constant sheafification carries P to a
flat-term K-flat constant-coefficient complex: the tensor identity is checked on
constant generators and descends by exact sheafification. The fixed extension model's
counit is therefore invertible there, and identifies F(Q(P)) with Q(L(P)). These
comparisons are natural in resolutions and their maps. The universal left-derived
property yields the claimed natural isomorphism, including its comparison with Q.
The section-module equivalence is exact and commutes with localization. -/
theorem realization_underived_model
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    (U : C) (hU : IsTerminal U)
    : ∃ (L : ModuleCat.{u + 1} (A J O U) ⥤ Mod (Sheaf J Ab.{u + 1}) O)
      (hadd : L.Additive),
      letI := hadd
      ∃ (hflat : L.PreservesKFlatQuasiIso) (hpres : L.PreservesFlat)
        (hbraid : L.Braided),
        letI := hflat
        Nonempty (L ⊣ sections J O U) ∧
          Nonempty (L.leftDerivedFunctor ≅ F J O U hU) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.Evaluation
