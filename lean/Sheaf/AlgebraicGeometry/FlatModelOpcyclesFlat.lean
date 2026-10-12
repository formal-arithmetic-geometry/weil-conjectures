/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.Algebra.Homology.FlatOpcyclesTorCriterion
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.Algebra.Category.ModuleCat.FilteredColimitFlat
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
import Sheaf.AlgebraicGeometry.IntrinsicFlatModuleStalkTensorPresentation
import Mathlib.RingTheory.Flat.Localization

/-! # Flatness of degree-zero opcycles of a free model

Source: Stacks Project, Tag 0653, applied on stalks; Tags 01U4 and 00HT
for the affine-local flatness comparisons
(blueprint: lem-pc-flat-model-opcycles-flat-zero).
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Source: Stacks Project, Tag 0653 (the last cokernel of a flat complex).
Proof: fix a point and an affine neighbourhood with coordinate ring A. For
smaller affine neighbourhoods the hypothesis makes every term of C flat over A.
Their filtered colimit is the stalk, which is flat over A. The stalk ring is a
localization of A, so flatness over A equals flatness over the stalk ring.
Take stalks of e: stalks preserve exact sequences and hence quasi-isomorphisms.
The stalk complex of Q has finite free terms. Its upper bound, and both bounds
of C, remain valid because stalks send zero objects to zero objects. The
bounded-above free complex and the bounded flat complex are
K-flat. Thus tensoring either with any module over the local ring computes derived
tensor, and their tensor complexes have the same homology. The flat complex is
strictly nonnegative, so that homology vanishes in degree -1. Apply
`Module.Flat.opcycles_of_exactAt` at zero to the stalk complex of Q. Stalks commute
with the cokernel defining opcycles, so every stalk of the opcycles is flat.
The opcycles are quasi-coherent, since the two terms defining their cokernel are
finite free. On an affine open they correspond to a module whose localizations
at every prime are flat; the local criterion makes that module flat. For an
inclusion of affine opens W in V, quasi-coherence identifies sections on W with
extension of scalars from V. They are flat over the ring of W, which is flat over
the ring of V because W to V is an open immersion. Transitivity gives flatness
over the ring of V, proving the affine-pair condition `IsFlatOver` for the identity.
There is no assertion of finite freeness here, and no neighbourhood is chosen.
(blueprint: lem-pc-flat-model-opcycles-flat-zero). -/
theorem isFlatOver_opcycles_zero_of_quasiIso {X : Scheme.{u}}
    (C Q : CochainComplex X.Modules ℤ) (d : ℕ)
    (hCge : C.IsStrictlyGE 0) (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 X))
    (hQle : Q.IsStrictlyLE d)
    (hQfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := X.ringCatSheaf) (ULift.{u} (Fin r))))
    (e : Q ⟶ C) (he : QuasiIso e) :
    (Q.opcycles 0).IsFlatOver (𝟙 X) := by sorry

end AlgebraicGeometry.Scheme.Modules
