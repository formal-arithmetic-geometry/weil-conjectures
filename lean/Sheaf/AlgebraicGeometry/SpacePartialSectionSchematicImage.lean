/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward
import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction

/-! # Schematic image of a partial section of a separated algebraic-space morphism

Source: Stacks Project, Morphisms of Spaces, Tags 0CP3, 082X and 082Z
(blueprint: lem-sfb-space-partial-section-schematic-image).

The closed subspace is characterized by minimality. The sheaf-pullback isomorphism
has the projection to the open as its forward map and the given section as the first
component of its inverse.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The smallest closed subspace containing a partial section is isomorphic to its open
domain after base change. The isomorphism is the projection; its inverse is induced by
the factorization of the section and the identity of the open.
Source: Stacks Project, Morphisms of Spaces, Tags 0CP3, 082X and 082Z
(blueprint: lem-sfb-space-partial-section-schematic-image).

Proof:
1. The closed diagonal of f is quasi-compact, so f is quasi-separated. Apply
   lem-sfb-space-qc-cancellation to s followed by f: their composite is the quasi-compact
   open a. The affine-test pullbacks of s are quasi-compact; by
   lem-sfb-qc-space-affine-etale-atlas they have quasi-compact scheme atlases, as needed
   for direct image. The equality s followed by f equals a, and monicity of a, imply
   monicity of s. Its diagonal is an isomorphism, so s is separated.
2. The structure modules are quasi-coherent. Apply
   lem-trf-space-qc-separated-quasi-coherent-pushforward to s, then
   lem-sfb-space-qcoh-kernels-colimits to obtain the quasi-coherent ideal
   I = ker(O_B to s_* O_O). By lem-sfb-space-ideal-closed-subspace-correspondence its
   vanishing locus C is a closed subspace, and s factors through it by t.
3. If s factors through another closed subspace D with ideal J, the factorization
   criterion makes J to s_* O_O zero. Thus J is contained in I. The inclusion-reversing
   correspondence of lem-sfb-space-ideal-closed-subspace-correspondence gives C <= D.
4. Put B_O = B times_Y O and g = (s,id) : O to B_O. This graph is a pullback of the
   closed diagonal of f, hence a closed immersion on scheme tests. The other projection
   B_O to B is open. Monicity of a identifies O times_B B_O with O, with map g.
   These are the sheaf fibre products of lem-trf-space-fibre-products-etale-covers.
5. By lem-trf-space-etale-module-pushforward-restriction the structural ring map
   restricted to B_O is O_(B_O) to g_* O_O: on each scheme chart both maps are the same
   pullback of regular functions. Open restriction preserves its sectionwise kernel.
   The base-change clause of lem-sfb-space-ideal-closed-subspace-correspondence thus
   identifies C times_B B_O with the closed subspace g(O).
6. Associate the sheaf fibre products using lem-trf-space-fibre-products-etale-covers.
   This identifies C times_Y O with O via (t,id). Its composite with the projection to O
   is the identity. Consequently that projection is its inverse, giving the asserted
   isomorphism and the specified first component of its inverse.
No Noetherian, finite-type, reducedness or properness assumption is used. -/
theorem partialSection_schematicImage
    {S : Scheme.{u}} (B Y O : AlgebraicSpace S) (f : B ⟶ Y)
    (hsep : IsSeparatedPresheafMap f.hom.hom) (a : O ⟶ Y)
    (hopen : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) a.hom.hom)
    (hqc : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left) a.hom.hom)
    (s : O ⟶ B) (hs : s ≫ f = a) :
    ∃ (C : ClosedSubspace B) (t : O ⟶ (C.val : AlgebraicSpace S)),
      t ≫ C.val.arrow = s ∧
      (∀ D : ClosedSubspace B,
        (∃ v : O ⟶ (D.val : AlgebraicSpace S), v ≫ D.val.arrow = s) → C.val ≤ D.val) ∧
      ∃ e : Limits.pullback (C.val.arrow ≫ f).hom a.hom ≅ O.obj,
        e.hom = Limits.pullback.snd (C.val.arrow ≫ f).hom a.hom ∧
        e.inv ≫ Limits.pullback.fst (C.val.arrow ≫ f).hom a.hom = t.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
