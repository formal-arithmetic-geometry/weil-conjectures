/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction

/-!
# Schematic closure of a quasi-compact open algebraic subspace

Source: Stacks Project, Morphisms of Spaces, Tags 082X and 082Z, and
`definition-scheme-theoretically-dense`
(blueprint: lem-sfb-space-qc-open-schematic-closure).

Schematic density is written as joint detection of regular functions on all étale
scheme charts of the inverse image. This is sectionwise injectivity into the direct
image structure sheaf, whose sections are compatible families on those charts.
Minimality and equality are over the ambient space, retaining the closed structures.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact open immersion has a smallest closed factorization, with a
quasi-compact open, topologically dense and schematically dense factor map. The
smallest closed factorization commutes with étale base change and open restriction;
where the original open subspace is closed, both closed subspaces are isomorphic over
the restricted target.
Source: Stacks Project, Morphisms of Spaces, Tags 082X and 082Z, and
`definition-scheme-theoretically-dense`
(blueprint: lem-sfb-space-qc-open-schematic-closure).

Proof:
1. The open immersion is separated, since its diagonal is an isomorphism. The
quasi-compact separated pushforward theorem
(lem-trf-space-qc-separated-quasi-coherent-pushforward) and the kernel theorem
(lem-sfb-space-qcoh-kernels-colimits) make the kernel of the structure-sheaf map a
quasi-coherent ideal. The ideal/closed-subspace correspondence
(lem-sfb-space-ideal-closed-subspace-correspondence) constructs its closed subspace C.
2. The zero-map factorization criterion factors O through C. Any other closed
factorization has defining ideal contained in this kernel, so C factors through it.
The inclusion-reversing correspondence gives minimality and uniqueness as a subspace.
3. The étale direct-image restriction comparison
(lem-trf-space-etale-module-pushforward-restriction) identifies the restricted ring
maps and kernels. The base-change clause of the ideal correspondence identifies the
closed subspace with C times the new base. Open restriction gives the same section
calculation. Thus these pullbacks are the smallest closed factorizations.
4. Restrict to O: the kernel of its identity structure map is zero, so C times O is O.
The factor map O to C is consequently the base change of the original quasi-compact
open immersion, and is a quasi-compact open immersion on every scheme test.
5. Apply the kernel and pushforward theorems to O to C. The closed subspace of C cut
out by its structure-map kernel is also closed in B and contains O. Minimality makes
it all of C, hence that kernel is zero. On every étale chart of C, two functions with
equal pullbacks to every chart of its inverse image therefore agree.
6. If the point image were not dense, take a nonempty affine étale chart in the open
complement of its closure (lem-a1-space-point-open-calculus). Its inverse image in O
is empty, and the injection of step 5 forces its regular-function ring to be zero,
contradicting nonemptiness.
7. Where O is closed, it is itself an admissible closed factorization. Minimality
and the original factorization give inverse inclusions, hence an isomorphism of the
two closed subspaces over that open base. All these arguments include the empty open
subspace and the identity open immersion. -/
theorem exists_qcOpen_schematicClosure {S : Scheme.{u}} {O B : AlgebraicSpace S}
    (j : O ⟶ B)
    (hj : IsRepresentableWith
      (fun _ _ p ↦ IsOpenImmersion p.left ∧ QuasiCompact p.left) j.hom.hom) :
    ∃ (C : AlgebraicSpace S) (c : C ⟶ B) (q : O ⟶ C),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) c.hom.hom ∧
      q ≫ c = j ∧
      (∀ (D : AlgebraicSpace S) (d : D ⟶ B),
        IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) d.hom.hom →
        (∃ a : O ⟶ D, a ≫ d = j) → ∃ b : C ⟶ D, b ≫ d = c) ∧
      IsRepresentableWith
        (fun _ _ p ↦ IsOpenImmersion p.left ∧ QuasiCompact p.left) q.hom.hom ∧
      Dense (pointImage q.hom.hom) ∧
      (∀ (V : C.EtaleSite) (a b : C.structureSheaf.obj.obj (op V)),
        (∀ (T : O.EtaleSite) (p : T.obj.left ⟶ V.obj.left),
          T.obj.hom ≫ q.hom.hom = yoneda.map p ≫ V.obj.hom →
          (Scheme.Γ.map p.left.op).hom a = (Scheme.Γ.map p.left.op).hom b) → a = b) ∧
      (∀ (V : AlgebraicSpace S) (g : V ⟶ B),
        (IsEtale g.hom.hom ∨
          IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) g.hom.hom) →
        IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
          (Limits.pullback.snd c.hom g.hom).hom ∧
        (∀ (D : AlgebraicSpace S) (d : D ⟶ V),
          IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) d.hom.hom →
          (∃ a : Limits.pullback j.hom g.hom ⟶ D.obj,
            a ≫ d.hom = Limits.pullback.snd j.hom g.hom) →
          ∃ b : Limits.pullback c.hom g.hom ⟶ D.obj,
            b ≫ d.hom = Limits.pullback.snd c.hom g.hom)) ∧
      (∀ (V : AlgebraicSpace S) (g : V ⟶ B),
        IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) g.hom.hom →
        IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
          (Limits.pullback.snd j.hom g.hom).hom →
        ∃ e : Limits.pullback c.hom g.hom ≅ Limits.pullback j.hom g.hom,
          e.hom ≫ Limits.pullback.snd j.hom g.hom =
            Limits.pullback.snd c.hom g.hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
