/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.ClosedPointField
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
import Sheaf.AlgebraicGeometry.FreeFlatGroupSpaceQuotient
import Sheaf.AlgebraicGeometry.AlgebraicSpaceDenseSchemeOpen
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFourPropertyFppfDescent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCompactFppfLocal
import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Homogeneous quotients for homomorphisms with trivial kernel

Source: Milne, Algebraic Groups (2017), Definition 5.20(a), Theorem 5.28,
printed pp.104--105, and Appendix B, Theorem B.37, printed p.605
(blueprint: lem-sfb-trivial-kernel-homogeneous-quotient).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- A homomorphism of separated finite-type group schemes with trivial scheme-theoretic
kernel has a finite-type homogeneous scheme quotient. Its orbit-map fibres are precisely
right cosets on every scheme test. The action is Mathlib's internal left action.

Source: Milne, Algebraic Groups (2017), Definition 5.20(a), Theorem 5.28,
printed pp.104--105, and Appendix B, Theorem B.37, printed p.605
(blueprint: lem-sfb-trivial-kernel-homogeneous-quotient).

Proof plan (the eleven steps of the node):
1. Triviality of the scheme-theoretic kernel implies injectivity on all scheme tests:
   if i(h)=i(h'), then h⁻¹h' factors through the kernel and equals the identity.
   Thus h · g = g i(h)⁻¹ is a free left H-action, even on nonreduced tests.
2. Regard the schemes as algebraic spaces by def-trf-scheme-algebraic-space.
   Use lem-pc-flat-field and pqf-lem-lft-fp-locnoeth for flatness and local finite
   presentation of H. Apply lem-sfb-free-flat-group-space-quotient to obtain F=G/H
   and a surjective flat lfp q, with kernel pair (g,h) ↦ (g,g i(h)).
3. Left translations commute with the right H-action. Choose fppf local lifts to G;
   the kernel-pair formula makes their translated images agree on overlaps. Glue
   uniquely in F. This constructs its natural G-action, with o_F=q(1) and q(g)=g o_F.
4. The pullback of the diagonal of F by q × q is G × H → G × G. Its source is
   quasi-compact and its target quasi-separated. Use lem-sfb-space-qcqs-permanence,
   lem-sfb-space-fppf-covering-calculus and lem-sfb-space-quasicompact-fppf-local
   to descend quasi-compactness of the diagonal, without asserting separatedness.
5. Apply lem-sfb-representable-lft-fppf-source-descent to get local finite type of F.
   The continuous surjection from G makes F quasi-compact, using
   lem-sfb-stack-point-topology-flat-lfp-open and lem-sfb-space-qcqs-permanence.
6. By lem-sfb-quasiseparated-space-dense-scheme-open take a nonempty dense scheme
   open V in F. For finite K/k inside an algebraic closure, let V[K] be the largest
   scheme open in F_K, using lem-sfb-space-largest-schematic-open. It contains V_K,
   is invariant under translations by G(K), and grows under finite field extension.
7. A closed point in q⁻¹(V) has finite residue field by lem-weil-pbc-zariski-lemma.
   Over this finite extension translation puts all rational images in V[K]. Apply
   lem-sfb-finite-extension-open-exhaustion to q_K⁻¹(V[K]) to get F_K=V[K], a scheme.
   Use covering calculus and lem-sfb-space-four-property-fppf-descent for finite type.
8. In this scheme quotient over K, o_K is closed by lem-kun-closed-point-field and
   is a closed immersion by lem-trf-closed-point-residue-immersion. The kernel pair
   identifies H_K with its fibre. By lem-weil-pbc-closed-immersion-base-change, i_K
   is closed; lem-sfb-space-closed-immersion-fppf-descent descends closedness to i.
9. Apply lem-sfb-algebraic-group-homogeneous-quotient to this now-closed subgroup
   to obtain a finite-type scheme X and a flat surjective finitely presented p.
10. Identify X with F as fppf sheaves by gluing p-images of local q-lifts and,
    conversely, q-images of local p-lifts. Their shared coset relation gives overlap
    agreement; def-pc-fppf-site and def-trf-scheme-algebraic-space give gluing.
    The maps are inverse on local lifts. Transport the action to X by Yoneda and
    put o=p(1); its orbit map is p.
11. The all-test-schemes coset relation for p is exactly the displayed equivalence.
    This includes non-affine and nonreduced schemes and needs no initial closedness. -/
theorem exists_homogeneousQuotient_of_trivialKernel
    (k : Type u) [Field k]
    (H G : Over (Spec (.of k))) [GrpObj H] [GrpObj G]
    [IsSeparated H.hom] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (i : H ⟶ G) [IsMonHom i]
    (hker : IsIso (toUnit (GrpObj.ker i))) :
    ∃ (X : Over (Spec (.of k))) (act : ModObj G X)
      (o : 𝟙_ (Over (Spec (.of k))) ⟶ X),
      LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
      ∀ (T : Over (Spec (.of k))) (a b : T ⟶ G),
        lift a (toUnit T ≫ o) ≫ act.smul = lift b (toUnit T ≫ o) ≫ act.smul ↔
          a⁻¹ * b ∈ Set.range (fun h : T ⟶ H ↦ h ≫ i) := by
  sorry

end AlgebraicGeometry
