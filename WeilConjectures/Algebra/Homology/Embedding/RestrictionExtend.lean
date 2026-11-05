/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Embedding.IsSupported
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-!
# Complexes supported on an embedding are extensions of their restrictions

Let `e : c.Embedding c'` be an embedding of complex shapes and `K` a complex for `c'` which is
strictly supported on `e`. Then `K` is isomorphic to the extension of its restriction
(`HomologicalComplex.isoExtendRestriction`), and a morphism `φ : K ⟶ L.extend e` is a
quasi-isomorphism if and only if the corresponding morphism `K.restriction e ⟶ L` is
(`HomologicalComplex.quasiIso_iff_quasiIso_homRestrict`).
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  [e.IsRelIff] {C : Type*} [Category* C]

section HasZero

variable [HasZeroMorphisms C] [HasZeroObject C]

end HasZero

section Abelian

variable [Abelian C]

end Abelian

end HomologicalComplex
