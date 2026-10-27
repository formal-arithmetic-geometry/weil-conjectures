/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.Connected.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
import Sheaf.AlgebraicGeometry.GroupScheme.ConnectedExtension
import Sheaf.AlgebraicGeometry.FpqcAffineDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.MorphismProperty.Descent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Smooth quotients by affine normal subgroups

Source: Milne, Algebraic Groups (2017), Theorem 5.14, Propositions 5.24--5.25,
Corollary 5.26, Theorem 5.55, Proposition 5.59 and Proposition 8.1(a).
(blueprint: lem-sfb-smooth-affine-normal-quotient-lifts)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Quotients by smooth connected affine closed normal subgroups, including the fppf
covering property and inverse images of smooth connected affine closed normal subgroups.
Kernel isomorphisms commute with the given inclusion into `G`; the cartesian square
specifies the actual scheme-theoretic inverse image, up to its unique isomorphism.

Source: Milne, Algebraic Groups (2017), Theorem 5.14, printed pp.102,105;
Propositions 5.24--5.25 and Corollary 5.26, pp.104--105; Proposition 1.62, p.24;
Theorem 5.55 and Proposition 5.59, pp.113--114; Proposition 8.1(a), p.149.
(blueprint: lem-sfb-smooth-affine-normal-quotient-lifts)

Proof:
1. Apply `lem-sfb-algebraic-group-homogeneous-quotient` to `N` in `G`. The pointwise
   coset criterion and `lem-galois-yoneda-fully-faithful` identify its kernel pair
   with `G × N`. The quotient map is an fpqc cover, being flat, surjective and
   quasi-compact (`def-weil-pbc-fpqc-covering`).
2. Base change this covering with a parameter, using
   `lem-galois-fpqc-covering-base-change`. By
   `lem-weil-pbc-fpqc-representable-descent`, morphisms constant on its kernel pair
   descend uniquely. Apply this one variable at a time.
3. Normality gives `(g₁n₁)(g₂n₂) = g₁g₂(g₂⁻¹n₁g₂)n₂`. Thus multiplication descends
   in each variable (`def-sc-group-scheme-subgroup`).
4. Inversion descends by the same normality calculation; the unit is the image of
   the unit of `G`. Associativity, unit and inverse identities hold after the
   covering, hence by uniqueness hold on `Q` (`def-sc-group-scheme`).
5. The coset criterion at the identity identifies `N` with the scheme-theoretic
   kernel, compatibly with its inclusion, by `lem-galois-yoneda-fully-faithful`
   and `def-pc-fibre-product`.
6. The base change of `q` by itself, after swapping factors, is the projection
   `G × N → G`. It is affine and smooth. Descend these properties using
   `lem-weil-pbc-fpqc-descend-affine` and `lem-trf-smooth-fpqc-base-descent`, with
   `pqf-def-affine-morphism`, `lem-weil-pbc-affine-morphism-permanence` and
   `lem-pc-proper-base-change`.
7. Apply `lem-sbc-smooth-flat-surjective-source-descent` to obtain smoothness of
   `Q`. Connectedness descends along the continuous surjection from `G`
   (`def-weil-connected-scheme`); separatedness and finite type came from step 1.
8. Arbitrary base changes are flat, surjective and finitely presented by
   `lem-weil-pbc-flat-morphism-base-change`, `lem-weil-pbc-surjective-base-change`
   and `lem-weil-pbc-qcqs-morphism-permanence`. They are one-member fppf covers
   (`def-pc-fppf-site`).
9. Form the inverse image of `S`. Its inclusion is closed by
   `lem-weil-pbc-closed-immersion-base-change`; the pointwise inverse-image
   subgroup is normal by `def-sc-group-scheme-subgroup`. Pullback pasting
   (`def-pc-fibre-product`) identifies its kernel with the same `N` inside `G`.
   Its projection to `S` is surjective by step 8.
10. This projection is affine by step 6 and base change, so its source is affine
    (`lem-weil-pbc-affine-morphism-permanence`). Its closed inclusion into `G`
    makes it finite type by `lem-weil-pbc-proper-fp-permanence`,
    `def-weil-proper-morphism` and `lem-sfb-finite-type-composition-base-change`.
11. Smoothness follows by `lem-pc-proper-base-change` and
    `lem-trf-smooth-composition`. The affine smooth `S` is finite type
    (`def-sbc-smooth-morphisms`, `def-sbc-locally-finite-presentation`,
    `def-weil-finite-type-morphism`). Apply `lem-sfb-connected-group-extension`
    to its flat surjective projection with connected kernel `N` and connected
    target `S`; this proves connectedness of the inverse image. -/
theorem exists_smoothAffineNormalQuotient (k : Type u) [Field k] [IsAlgClosed k]
    (G N : Over (Spec (.of k))) [GrpObj G] [GrpObj N]
    [Smooth G.hom] [ConnectedSpace G.left] [IsSeparated G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth N.hom] [ConnectedSpace N.left] [IsAffine N.left]
    (i : N ⟶ G) [IsClosedSubgroupScheme i] [IsNormalSubgroupScheme i] :
    ∃ (Q : Over (Spec (.of k))) (_ : GrpObj Q) (q : G ⟶ Q) (_ : IsMonHom q),
      Smooth Q.hom ∧ ConnectedSpace Q.left ∧ IsSeparated Q.hom ∧
      LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom ∧
      Smooth q.left ∧ Surjective q.left ∧ LocallyOfFinitePresentation q.left ∧
      QuasiCompact q.left ∧ QuasiSeparated q.left ∧
      (∃ e : N ≅ GrpObj.ker q, e.hom ≫ GrpObj.kerι q = i) ∧
      (∀ (T : Over (Spec (.of k))) (t : T ⟶ Q),
        Flat (pullback.snd q t).left ∧ Surjective (pullback.snd q t).left ∧
        LocallyOfFinitePresentation (pullback.snd q t).left ∧
        QuasiCompact (pullback.snd q t).left ∧ QuasiSeparated (pullback.snd q t).left ∧
        Presieve.ofArrows (fun _ : PUnit ↦ (pullback q t).left)
          (fun _ ↦ (pullback.snd q t).left) ∈ Scheme.fppfPrecoverage T.left) ∧
      (∀ (S : Over (Spec (.of k))) [GrpObj S]
        [Smooth S.hom] [ConnectedSpace S.left] [IsAffine S.left]
        (j : S ⟶ Q) [IsClosedSubgroupScheme j] [IsNormalSubgroupScheme j],
        ∃ (P : Over (Spec (.of k))) (_ : GrpObj P) (a : P ⟶ G) (r : P ⟶ S)
          (_ : IsMonHom r),
          IsPullback a r q j ∧ IsClosedSubgroupScheme a ∧ IsNormalSubgroupScheme a ∧
          Smooth P.hom ∧ ConnectedSpace P.left ∧ IsAffine P.left ∧ Surjective r.left ∧
          ∃ e : N ≅ GrpObj.ker r, e.hom ≫ GrpObj.kerι r ≫ a = i) := by
  sorry

end AlgebraicGeometry
