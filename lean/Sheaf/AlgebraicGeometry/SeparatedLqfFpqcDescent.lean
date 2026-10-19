/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import Sheaf.AlgebraicGeometry.IndQuasiAffineFpqcDescent

/-!
# Effective fpqc descent of separated locally quasi-finite schemes

Source: Stacks Project, More on Groupoids in Spaces, Tag 0APK, lemma-ind-quasi-affine,
combined with More on Morphisms, Tag 0AP9, lemma-etale-separated-ind-quasi-affine
(blueprint: lem-a1-separated-lqf-fpqc-effective-descent).
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace CategoryTheory.Over.DescentDatum

/-- A descent datum on a separated locally quasi-finite scheme over a singleton fpqc
covering is effective. No quasi-compactness or finite-presentation assumption on the
scheme over the cover, and no separatedness assumption on either base, is required.

Source: Stacks Project, Tags 0APK and 0AP9.
(blueprint: lem-a1-separated-lqf-fpqc-effective-descent)

Here local quasi-finiteness is the Stacks predicate, including local finite type.
`D.IsEffective` gives a scheme `W` over `T` and a Cartesian square identifying `V`
with `W ×_T T'`; its transport-invariance clause says that this identification induces
precisely the given descent datum, including the cocycle.

Proof:
1. For every affine open U of T', take a quasi-compact open K of its inverse image
   in V. The restricted morphism K -> U is separated: its diagonal is the restriction
   of the closed diagonal of V -> T' to the appropriate open of the fibre product.
2. It is locally quasi-finite by lem-weil-pbc-lqf-restriction-to-opens. Since K is
   quasi-compact and U is affine, hence quasi-separated by lem-weil-pbc-affine-scheme-qcqs,
   it is quasi-compact by clause (1) of lem-weil-pbc-qcqs-morphism-permanence.
3. It is locally of finite type by lem-weil-pbc-lqf-locally-finite-type. Apply
   lemma-nagata-quasi-affine-morphism-of-quasi-finite to these four properties to
   conclude that K -> U is quasi-affine (def-nagata-quasi-affine-morphism).
   This is precisely the ind-quasi-affine condition of Tag 0AP9.
4. Apply lem-a1-ind-quasi-affine-fpqc-effective-descent (Tag 0APK) to f, the condition
   established in steps 1--3, and D. The result is a T-scheme W and a compatible
   isomorphism W ×_T T' -> V, which is D.IsEffective. This argument does not require
   V -> T' to be quasi-compact or locally of finite presentation. -/
theorem isEffective_of_isSeparated_isLocallyQuasiFinite_fpqc
    {T' T : Scheme.{u}} (f : T' ⟶ T)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage T) {V : Over T'}
    [IsSeparated V.hom] (hV : V.hom.IsLocallyQuasiFinite)
    (D : Over.DescentDatum f V) : D.IsEffective := by
  sorry

end CategoryTheory.Over.DescentDatum
