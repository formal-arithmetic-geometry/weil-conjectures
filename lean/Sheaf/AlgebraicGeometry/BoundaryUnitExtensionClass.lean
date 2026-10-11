/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.LocallyFreeExtCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-! # The boundary of the unit section is the extension class

Source: Stacks Project, Cohomology, Tag 0B3A, Lemma `lemma-h1-extensions`
(blueprint: lem-sc-p1-boundary-one-extension-class).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- For a short exact extension of the structure sheaf by A, the cohomology boundary
sends the unit section to the canonical image of its Yoneda class.
Source: Stacks Project, Cohomology, Tag 0B3A, Lemma `lemma-h1-extensions`.

Proof:
1. Specialize lem-sc-ext-locally-free to the structure sheaf. The degree-zero
identification Hom(O,-) = Gamma sends the identity to 1. The right derived functors
are universal delta-functors (lem-weil-pbc-right-derived-universal-delta-functor),
so their canonical comparison commutes with connecting maps. Here cohomology is
computed on the underlying abelian sheaf, whose connecting map is postcomposition
by the Ext class of the forgotten short exact sequence.
2. By lem-sc-p1-ext-connecting-yoneda, the Ext connecting map sends the identity
to the Yoneda class composed with the identity. By lem-sc-p1-ext-yoneda-functoriality
this is the original class. Thus the cohomology boundary of 1 is its canonical image.
(blueprint: lem-sc-p1-boundary-one-extension-class). -/
theorem boundary_unit_eq_extensionClass {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (A E : X.Modules) (f : A ⟶ E) (g : E ⟶ SheafOfModules.unit X.ringCatSheaf)
    (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact) :
    H.δ hS 0
      ((H.zeroLinearEquiv (SheafOfModules.unit X.ringCatSheaf)).symm
        (unitSectionsEquiv ⊤ 1)) =
        locallyFreeUnitExtAddEquivH A 1 hS.extClass := sorry

end AlgebraicGeometry.Scheme.Modules
