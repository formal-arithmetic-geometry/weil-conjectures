/-
Copyright (c) 2026 Q91. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q91
-/
module

public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Rigidity of actions on central multiplicative-type extensions

Source: Milne, Algebraic Groups (2017), Corollary 12.41, printed p.244, with the
Chapter 12 erratum requiring the kernel to be central
(blueprint: lem-sfb-multiplicative-extension-action-rigidity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A smooth connected affine algebraic group acts trivially by group automorphisms
on a central extension of multiplicative-type groups if it preserves the kernel.

Source: Milne, Algebraic Groups (2017), Corollary 12.41, printed p.244, corrected by
its Chapter 12 erratum; Theorem 12.36 and Corollary 12.37, printed pp.243--244
(blueprint: lem-sfb-multiplicative-extension-action-rigidity).

The action is Mathlib's internal `ModObj`. Its action laws give inverses at g and
inverse g, so `hmul` is precisely the additional automorphism requirement. Conditions
on all test schemes are equivalent to the stated conditions on all affine test
schemes: the identities are local, and kernel preservation factors the universal
point of G times the kernel through the kernel fibre product.

Proof plan:
1. The faithfully flat coordinate map makes q an fpqc cover by the affine
   fibre-product formula, faithful-flat base change, affine flatness and spectrum
   surjectivity (lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-faithfully-flat-base-change, lem-weil-pbc-flat-ring-map-iff-flat-affine,
   lem-weil-pbc-faithfully-flat-surjective-spectrum, def-weil-pbc-fpqc-covering).
   Products of q are composites of its base changes, hence fpqc covers by
   lem-weil-pbc-fpqc-covering-axioms. The kernel pair is E times ker q,
   via (e,n) mapping to (e,en), with inverse (e,e') mapping to (e,inverse(e)*e').
2. Descend q after the action along G times q by
   lem-weil-pbc-fpqc-representable-descent and lem-galois-fpqc-covering-base-change.
   The overlap identity follows from hmul and hpreserve. Check the action and
   homomorphism laws after the product covers to obtain an action on Q.
3. Apply lem-sfb-connected-action-multiplicative-type-rigidity to Q and ker q.
   Both actions are trivial, so q(a(g,e)) = q(e) and a(g,n) = n.
4. The difference c(g,e) = a(g,e)*inverse(e) lands in ker q and is invariant
   under replacing e by en. Descend it to d : G times Q to ker q using the same
   fpqc descent nodes. Centrality gives c(g,ee') = c(g,e)*c(g,e'), so d is a
   family of group homomorphisms Q to ker q. The action unit gives d(1,t) = 1.
5. Apply lem-sfb-diagonalizable-hom-family-rigidity with parameter G and base
   point its identity. Thus d = 1, whence a(g,e) = e on every algebra. Evaluating
   on the universal point of the affine source identifies the two morphisms. -/
theorem multiplicativeExtensionAction_eq_snd {F : Type u} [Field F] [IsAlgClosed F]
    (E Q G : Over (Spec (.of F))) [GrpObj E] [GrpObj Q] [GrpObj G]
    [IsAffine E.left] [IsAffine Q.left] [IsAffine G.left]
    [LocallyOfFiniteType E.hom] [QuasiCompact E.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth G.hom] [ConnectedSpace G.left]
    (q : E ⟶ Q) [IsMonHom q]
    (hflat : q.left.appTop.hom.FaithfullyFlat)
    (hN : ∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
      Nonempty (Grp.mk (GrpObj.ker q) ≅ diagonalizableGroup F M))
    (hQ : ∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
      Nonempty (Grp.mk Q ≅ diagonalizableGroup F M))
    (hcentral : ∀ (T : Over (Spec (.of F))) (n : T ⟶ GrpObj.ker q) (e : T ⟶ E),
      (n ≫ GrpObj.kerι q) * e = e * (n ≫ GrpObj.kerι q))
    [ModObj G E]
    (hmul : ∀ (T : Over (Spec (.of F))) (g : T ⟶ G) (e e' : T ⟶ E),
      g • (e * e') = (g • e) * (g • e'))
    (hpreserve : ∀ (T : Over (Spec (.of F))) (g : T ⟶ G) (n : T ⟶ GrpObj.ker q),
      ∃ n' : T ⟶ GrpObj.ker q, g • (n ≫ GrpObj.kerι q) = n' ≫ GrpObj.kerι q) :
    ModObj.smul (M := G) (X := E) = snd G E := by
  sorry

end AlgebraicGeometry
