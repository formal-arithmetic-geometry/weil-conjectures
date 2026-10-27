/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Geometry and quotient data in a flat blowup square

Source: Stacks Project, Divisors, Tags 0805, 02OS and 080D (1), including the
paragraph before Definition `definition-strict-transform`
(blueprint: lem-trf-blowup-square-pullback-quotient-data).

The upstream blowup comparison has the factors in the order `B ×[S] T`.
Consequently its first projection is the map called `β` in the source.
`moduleStrictTransformOpen` is the complement of the exceptional closed set.
Equality of these complementary opens records equality of the closed sets.
The kernel objects and cokernel quotient maps below are the existing strict-transform
constructions, with no new choices of submodules or quotient maps.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Geometry, local equations, supported kernels and ordinary-pullback comparison for
an arbitrary flat commutative square. The `IsPullback` clause gives the unique
projection-compatible isomorphism `Q ≅ Y ×[X] P`. The equations of complementary
opens mean `D ∩ V = V(a)` and `D_Q ∩ W = V(a_W)`; they impose no regularity on `a`.
The range formulas identify the kernel inclusions with the stated subsheaves on
*every* open. The final equality fixes the comparison isomorphism canonically.
Source: Stacks, Tags 0805, 02OS, 080D (1), 01BG and 07ZP
(blueprint: lem-trf-blowup-square-pullback-quotient-data).

Proof: (1) thm-nagata-blowup-flat-base-change makes the specified comparison an
isomorphism over T. Together with the original square and the two pullback
identities, this defines u with both displayed projections (def-pc-fibre-product).
(2) Given maps y:R→Y and z:R→P with jy=pz, the pair (gy,qz) maps to T×[S]B.
The inverse blowup comparison yields t:R→B_T; the pair (y,t) maps to Q.
Uniqueness of both pullbacks proves that this construction is inverse to (r,u).
Thus u is the base change of j, and is flat by
lem-weil-pbc-flat-morphism-base-change.
(3) def-nagata-extended-ideal identifies the extended centre with the inverse-image
closed subscheme: on affine opens A→C, its quotient is C/IC = C⊗_A A/I.
The prime-ideal criterion identifies its support with the inverse image of V(I),
so D_Q=u⁻¹D. Images of finite local generators prove finite type of the new centre.
(4) lem-weil-pbc-module-pullback-quasi-coherent applied to p,j,r proves
quasi-coherence of both ordinary pullbacks and of j*F.
(5) thm-nagata-blowup-principalizes-center makes the exceptional divisor locally
principal. lem-trf-locally-principal-supported-kernel applies to q and qu,
proving quasi-coherence of both supported kernels. Shrinking to affine V gives a;
on every affine W⊆u⁻¹V its image under u.appLE cuts out the inverse-image set.
The sectionwise kernel of open restriction is exactly the displayed vanishing
condition on V∩Dᶜ (respectively W∩D_Qᶜ).
(6) def-trf-module-strict-transform is the cokernel of each such kernel inclusion;
the companion quotient-presentation statement records its universal property.
Finally def-pc-module-pullback supplies the normalized composition isomorphisms.
Composing their inverse for (u,p), the equality pu=jr and the comparison for (r,j)
gives precisely the displayed γ, with no arbitrary isomorphism chosen. -/
theorem blowupSquare_pullback_quotientData {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (e : T ⟶ S) (g : Y ⟶ T) (j : Y ⟶ X)
    (h : j ≫ f = g ≫ e) [Flat e] [Flat j]
    (I : S.IdealSheafData) [I.toModules.IsFiniteType] :
    IsIso (I.blowupFlatBaseChange e) ∧
    I.blowupFlatBaseChange e ≫ pullback.snd I.blowupMap e = (I.comap e).blowupMap ∧
    ∃ u : Limits.pullback (C := Scheme.{u}) g (I.comap e).blowupMap ⟶
      Limits.pullback (C := Scheme.{u}) f I.blowupMap,
    ∃ hu : u ≫ pullback.fst f I.blowupMap = pullback.fst g (I.comap e).blowupMap ≫ j,
      u ≫ pullback.snd f I.blowupMap =
        pullback.snd g (I.comap e).blowupMap ≫
          I.blowupFlatBaseChange e ≫ pullback.fst I.blowupMap e ∧
      IsPullback (pullback.fst g (I.comap e).blowupMap) u j
        (pullback.fst f I.blowupMap) ∧
      Flat u ∧
      moduleStrictTransformOpen g (I.comap e) = u ⁻¹ᵁ moduleStrictTransformOpen f I ∧
      (∀ x : Limits.pullback (C := Scheme.{u}) f I.blowupMap,
        ∃ V : (Limits.pullback (C := Scheme.{u}) f I.blowupMap).Opens, x ∈ V ∧ IsAffineOpen V ∧
          ∃ a : (Limits.pullback (C := Scheme.{u}) f I.blowupMap).presheaf.obj (op V),
            V ⊓ moduleStrictTransformOpen f I =
              (Limits.pullback (C := Scheme.{u}) f I.blowupMap).basicOpen a ∧
            ∀ (W : (Limits.pullback (C := Scheme.{u}) g (I.comap e).blowupMap).Opens)
              (_ : IsAffineOpen W)
              (hW : W ≤ u ⁻¹ᵁ V),
              W ⊓ moduleStrictTransformOpen g (I.comap e) =
                (Limits.pullback (C := Scheme.{u}) g (I.comap e).blowupMap).basicOpen
                  ((u.appLE V W hW) a)) ∧
      (I.comap e).toModules.IsFiniteType ∧
      ∀ (F : X.Modules) [F.IsQuasicoherent],
        ((tensorPullback (pullback.fst f I.blowupMap)).obj F).IsQuasicoherent ∧
        ((tensorPullback j).obj F).IsQuasicoherent ∧
        ((tensorPullback (pullback.fst g (I.comap e).blowupMap)).obj
          ((tensorPullback j).obj F)).IsQuasicoherent ∧
        (moduleStrictTransformKernel f I F).IsQuasicoherent ∧
        (moduleStrictTransformKernel g (I.comap e) ((tensorPullback j).obj F)).IsQuasicoherent ∧
        (∀ V : (Limits.pullback (C := Scheme.{u}) f I.blowupMap).Opens,
          Set.range ((kernel.ι (moduleStrictTransformRestriction f I F)).app V) =
            {s | ((tensorPullback (pullback.fst f I.blowupMap)).obj F).presheaf.map
              (homOfLE (inf_le_left : V ⊓ moduleStrictTransformOpen f I ≤ V)).op s = 0}) ∧
        (∀ W : (Limits.pullback (C := Scheme.{u}) g (I.comap e).blowupMap).Opens,
          Set.range ((kernel.ι (moduleStrictTransformRestriction g (I.comap e)
            ((tensorPullback j).obj F))).app W) =
            {s | ((tensorPullback (pullback.fst g (I.comap e).blowupMap)).obj
              ((tensorPullback j).obj F)).presheaf.map
                (homOfLE (inf_le_left : W ⊓ moduleStrictTransformOpen g (I.comap e) ≤ W)).op
                  s = 0}) ∧
        ∃ γ : (tensorPullback u).obj
            ((tensorPullback (pullback.fst f I.blowupMap)).obj F) ≅
          (tensorPullback (pullback.fst g (I.comap e).blowupMap)).obj
            ((tensorPullback j).obj F),
          γ = (tensorPullbackSectionComp u (pullback.fst f I.blowupMap)).symm.app F ≪≫
            eqToIso (congrArg (fun k ↦ (tensorPullback k).obj F) hu) ≪≫
            (tensorPullbackSectionComp (pullback.fst g (I.comap e).blowupMap) j).app F := by
  sorry

/-- The quotient presentation used on both sides of the flat blowup square:
`moduleStrictTransform f I F = H/K`, with its defining cokernel quotient map.
Apply this first to `(f,I,F)` and then to `(g,I.comap e,j*F)`; the preceding
statement supplies finite type and quasi-coherence for the latter application.
Source: Stacks Project, Divisors, Tag 080D (1)
(blueprint: lem-trf-blowup-square-pullback-quotient-data).

Proof: Step (6) of the node: def-trf-module-strict-transform defines the strict
transform as the cokernel of the inclusion of the supported-section kernel.
The cokernel universal property gives a unique factorization of every map killing
that inclusion through its defining quotient map. This is applied to the two
centres and ordinary pullbacks; no flatness assumption is needed for this
purely definitional quotient-presentation clause. -/
theorem blowupSquare_strictTransform_quotientPresentation {X S : Scheme.{u}}
    (f : X ⟶ S) (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent]
    (M : (Limits.pullback (C := Scheme.{u}) f I.blowupMap).Modules)
    (k : (tensorPullback (pullback.fst f I.blowupMap)).obj F ⟶ M)
    (hk : kernel.ι (moduleStrictTransformRestriction f I F) ≫ k = 0) :
    ∃! l : moduleStrictTransform f I F ⟶ M,
      cokernel.π (kernel.ι (moduleStrictTransformRestriction f I F)) ≫ l = k := by
  sorry

end AlgebraicGeometry.Scheme.Modules
