/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.FiberDegreeBound
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EtaleSplitsOffQuasiFinitePart
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant
import Sheaf.AlgebraicGeometry.FiniteFiberDegreeBaseChange

/-!
# Étale neighbourhoods of points of maximal fibre degree

Source: Stacks Project, More on Morphisms, Tag 07RY, proof, second paragraph.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- A point of maximal degree has an étale neighbourhood on which the pullback is finite
locally free of that degree.
Source: Stacks Project, More on Morphisms, Tag 07RY, proof, second paragraph.
(blueprint: lem-weil-pbc-flat-fp-lqf-maximal-degree-etale-neighborhood)

Proof: the finite fibre over `s` has finitely many points. An elementary étale
neighbourhood splits the pullback into complementary open parts `W` and `V`, with `V`
finite and `W` having empty fibre at the distinguished point (Tag 02LP). The finite
part is flat and locally of finite presentation by base change and restriction, hence
finite locally free. Shrink the neighbourhood to the locus where its degree equals
its degree at the distinguished point, using local constancy of degree (Tag 04MH).
That degree is `m`: finite fibre degrees are invariant under residue-field extension,
and the fibre of `W` is empty. At any point of the shrunken neighbourhood, the fibre of
the whole pullback is finite of degree at most `m`. Its decomposition into the fibres
of `W` and `V` gives a product of rings of global sections, and therefore an additive
degree formula. Since the `V` degree is `m`, the `W` degree is zero. A finite scheme
over a field with zero-dimensional global sections is empty: its ring of global
sections is the zero ring, and it is the spectrum of this ring. Thus every fibre of
`W` is empty, and every point of `W` would belong to one of these fibres; hence `W` is
empty. The whole pullback equals the finite locally free part of degree `m`.
Restriction preserves the distinguished point and étaleness, giving the result.
For `m = 0` the same argument makes both parts empty. An unattained bound and an empty
base have no point satisfying the hypotheses, so impose no additional assertion. -/
theorem exists_etale_isFiniteLocallyFreeOfDegree_of_maximal_fiber_degree
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated f] (h_lqf : IsLocallyQuasiFinite f) (m : ℕ)
    (hm : BoundsFiberDegrees f m) (s : S)
    (hs : (f.fiberToSpecResidueField s).finrankΓ = m) :
    ∃ (T : Scheme.{u}) (φ : T ⟶ S) (t : T), Etale φ ∧ φ t = s ∧
      (pullback.snd f φ).IsFiniteLocallyFreeOfDegree m := by
  sorry

end AlgebraicGeometry.Scheme.Hom
