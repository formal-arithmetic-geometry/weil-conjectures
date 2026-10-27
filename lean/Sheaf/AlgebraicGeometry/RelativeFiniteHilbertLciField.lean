/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q155
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.TraceFormula.GenericCMLocusField
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.AlgebraicGeometry.CohenMacaulayClosedFibreRegularSlice
import Sheaf.AlgebraicGeometry.DimZeroFiniteOverField
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Finite positive-degree unramified lci slices over a field

Source: Stacks Project, criteria.tex, Tag 06DA, lemma-lci-surjective, proof
(blueprint: lem-sfb-relative-finite-hilbert-lci-field).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A nonempty algebraic space locally of finite presentation over any field has a
finite locally free positive-degree slice whose map to the space is unramified and lci.
Nonemptiness is expressed by a section over a nonempty test scheme. The chartwise lfp
hypothesis ranges over every representable étale scheme chart. Both properties of the
slice map use the two-chart predicates of the relative finite Hilbert construction.

Source: Stacks Project, criteria.tex, Tag 06DA, lemma-lci-surjective, proof
(blueprint: lem-sfb-relative-finite-hilbert-lci-field).

Proof:
1. Choose an étale atlas and a nonempty affine open V. Its structure map is locally
finitely presented, hence finite type. By lem-trf-generic-cm-locus-field its Cohen-Macaulay
locus is nonempty open. By lem-sc-lft-over-field-jacobson-space it contains a point v
closed in V. The stalk at v is Noetherian with depth equal to dimension. The structure
map is flat because every module over the field is a vector space and is flat.
2. Apply lem-sfb-cm-closed-fibre-regular-slice at v. It gives a nonempty regular immersion
Z into V, with singleton underlying space and flat locally finitely presented structure
map. An affine open containing its sole point is all of Z, so Z is affine of finite type
and dimension zero.
3. Apply lem-pc-algebraic-dim-zero-affine-finite. The structure map is finite and hence
finite locally free. Its degree d is the dimension of its coordinate ring over k;
nonemptiness makes this dimension positive, as required by def-pc-finite-locally-free.
4. The immersion is unramified: it is locally finite type and a monomorphism, so its
diagonal is an isomorphism. The étale chart is unramified. Compose using
lem-sfb-space-unramified-permanence.
5. The regular immersion is lci: its local regular generators are Koszul-regular by
lem-weil-pbc-regular-sequence-koszul-regular, and the open factor is smooth by
def-sbc-smooth-morphisms. The étale chart is lci and composition is lci by
lem-sfb-space-lci-composition. This gives the two chartwise properties of
def-sfb-relative-finite-hilbert-groupoids. All maps remain over the original field k.
-/
theorem exists_finiteLocallyFree_positiveDegree_unramified_lci_slice
    (k : Type u) [Field k] (X : AlgebraicSpace (Spec (.of k)))
    (hne : ∃ T : Over (Spec (.of k)),
      Nonempty T.left ∧ Nonempty (X.obj.obj.obj (op T)))
    (hlfp : ∀ (V : Over (Spec (.of k))) (a : yoneda.obj V ⟶ X.obj.obj),
      AlgebraicSpace.IsEtale a → LocallyOfFinitePresentation V.hom) :
    ∃ (d : ℕ) (_ : 1 ≤ d) (Z : Over (Spec (.of k)))
      (i : yoneda.obj Z ⟶ X.obj.obj),
      Z.hom.IsFiniteLocallyFreeOfDegree d ∧
        RelativeFiniteHilbert.SpaceProperty (fun _ _ f ↦ IsUnramified f) i ∧
        RelativeFiniteHilbert.SpaceProperty (fun _ _ f ↦ RelativeFiniteHilbert.SchemeLci f) i := by
  sorry

end AlgebraicGeometry
