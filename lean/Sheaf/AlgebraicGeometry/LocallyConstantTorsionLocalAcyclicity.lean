/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.GroupTheory.OrderOfElement
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.Paper.ConstantSheafSectionsLocallyConstant
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.CategoryTheory.Sites.GlobalSections
import Sheaf.AlgebraicGeometry.KInjectiveResolutions
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift

/-!
# Local acyclicity for locally constant torsion coefficients

Source: Stacks Project, Tag 0GJR, lemma-locally-acyclic-locally-constant
(blueprint: lem-weil-pbc-locally-constant-torsion-local-acyclicity).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Local acyclicity extends to locally constant abelian sheaves whose stalk elements
have finite order prime to the residue characteristic; in characteristic zero every
finite order is allowed. No finiteness of stalks or common annihilator is assumed.
Source: Stacks Project, Tag 0GJR, lemma-locally-acyclic-locally-constant
(blueprint: lem-weil-pbc-locally-constant-torsion-local-acyclicity).

Proof:
1. Fix a geometric point `x`. Pull a constant trivialization of `G` on an étale
neighbourhood back to the strict localization `T` at `x`, using strict-henselization
functoriality and `upperStarConstantSheafIso`. Sections of a constant sheaf on this
local spectrum are constant (constantSheaf_sections_locallyConstant). The strict-local
sections--stalk isomorphism and inverseImage_stalk_germ identify this coefficient group
with the stalk `M`, compatibly with the germ map. Thus the restriction to `T` and to
any strict-local fibre `V` is the constant sheaf with coefficient group `M`.
2. The finitely generated subgroups of `M`, ordered by inclusion, form a nonempty
directed system with colimit `M`. Each is finite: representatives in a finite generating
set can have their integer coefficients reduced modulo the generators' finite orders.
All their elements retain the required prime-to-characteristic orders. The colimit
universal property follows by defining a map on an element in any subgroup containing it;
directedness makes this independent of the choice and additive.
3. The finitely generated abelian group structure theorem decomposes each finite subgroup
as a finite sum of cyclic prime-power groups. The free rank is zero by finiteness, and
each cyclic generator has order prime to the residue characteristic.
4. Local acyclicity of `f` gives the constant-section isomorphism in degree zero and
vanishing in positive degrees for each cyclic summand, on every fibre `V`. The
characteristic of the residue field agrees with that of the geometric field.
5. Constant sheaves preserve finite sums by their adjunction. Choose K-injective
resolutions of the summands. Their finite sum is K-injective: its Hom complex from an
acyclic complex is the finite sum of the acyclic Hom complexes. Kernels and images split
componentwise, so the sum of resolution maps is a quasi-isomorphism. Global sections
preserve finite products, hence finite sums. Cohomology therefore preserves these finite
sums, including the empty sum. The degree-zero isomorphism sends a tuple to the sum of
its constant sections.
6. The strict-local fibre `V` is affine by the tensor-product description of fibre
products of spectra, hence qcqs. The constant-sheaf left adjoint preserves the filtered
colimit of finite subgroups. The qcqs cohomology filtered-colimit theorem applies in
every nonnegative degree, without torsion or Noetherian hypotheses on `V`.
7. Positive cohomology is a colimit of zero groups. In degree zero the finite-subgroup
constant-section maps commute with inclusions, so their colimit is the constant-section
isomorphism for `M`. The germ-compatible trivialization in step 1 identifies this with
the specified canonical map `localAcyclicityAlpha`. Thus both defining clauses of local
acyclicity relative to `G` hold at every `x` and every test geometric point. -/
theorem isLocallyAcyclicRelative_of_locallyConstant_torsion
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : IsLocallyAcyclic f)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Scheme.IsLocallyConstantSheaf G]
    (hG : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
      (m : ((Scheme.pointSmallEtale x).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj G),
      IsOfFinAddOrder m ∧
        (ringChar (X.residueField (x default)) = 0 ∨
          (addOrderOf m).Coprime (ringChar (X.residueField (x default))))) :
    IsLocallyAcyclicRelative f G := by
  sorry

end AlgebraicGeometry.Etale
