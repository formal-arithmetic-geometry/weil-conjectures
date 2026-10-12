/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.ConstructibleCurveSubQuotient
import Sheaf.AlgebraicGeometry.CurveCoefficientPair
import Sheaf.AlgebraicGeometry.LocallyClosedStratification
import Sheaf.AlgebraicGeometry.TorsionSheafCharacterizations
import Sheaf.Paper.InverseImageStalkGerm
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.SixFunctors.Finite.Stalk

/-!
# Constructibility descends from finite direct image on curves

Source: Stacks Project, Etale Cohomology, Tags 03QP (1), 095G and 09BH (2),
combined in the converse of Tag 095R in the blueprint
(blueprint: lem-weil-pbc-finite-pushforward-constructible-descent).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A torsion abelian sheaf on a curve is constructible if its finite direct image,
assumed torsion, is constructible. Source: the agent's composition of Stacks Project,
Tags 03QP (1), 095G and 09BH (2), the converse of 095R
(blueprint: lem-weil-pbc-finite-pushforward-constructible-descent).

Proof (the node's six steps):
1. Set `G = f_* F` and `F' = f⁻¹ G` (def-weil-pbc-direct-image,
def-weil-pbc-inverse-image). Finite type over the field makes X and Y Noetherian;
locally closed strata are constructible (def-weil-constructible-subset).
2. At a geometric point x, the counit stalk map is the restriction of germs composed
with the inverse-image stalk isomorphism (lem-weil-pbc-counit-stalk-germ-restriction,
lem-weil-pbc-inverse-image-stalk-germ). The finite stalk formula identifies restriction
with projection onto the x factor, hence it is surjective
(lem-weil-pbc-finite-stalk-formula-restriction, lemma-weil-pbc-finite-stalk-formula).
3. Exactness of geometric stalks gives zero cokernel at every geometric point
(prop-weil-pbc-geometric-stalks-exact). Stalks of a covering family detect monomorphisms
(lem-weil-pbc-geometric-stalks-detect-mono), so the cokernel is zero. Thus the counit
is an epimorphism and gives the short exact sequence `0 → K → F' → F → 0`.
4. Pull back a finite constructible stratification for G
(lemma-constructible-pullback-stratification, def-constructible-stratification).
The inverse-image composition isomorphisms identify its restrictions with pullbacks
of the original restrictions (lem-weil-pbc-inverse-image-composition).
These are locally constant by lemma-constructible-pullback-locally-constant and
lemma-constructible-iso-invariance. Their stalks remain finite by
lemma-openclosed-stalk-upperstar. The same stalk isomorphism and
lem-weil-pbc-torsion-sheaf-characterizations give torsion of F'.
5. Exact stalks identify the stalks of K with subgroups of torsion stalks of F',
so K is torsion (prop-weil-pbc-geometric-stalks-exact,
lem-weil-pbc-torsion-sheaf-characterizations). All three terms are curve coefficient pairs.
6. Apply lem-weil-pbc-curve-constructible-sub-quotient to this short exact sequence:
a quotient of the constructible middle term is constructible (09BH (2)). -/
theorem CurveCoefficientPair.isConstructible_of_finite_pushforward
    {k : Type u} [Field k] [IsAlgClosed k] (P : CurveCoefficientPair k)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsCurve g]
    (f : P.C ⟶ Y) [IsFinite f] (hf : f ≫ g = P.toSpec)
    (hT : Y.IsTorsionAbelianSheaf (Etale.lowerStar AddCommGrpCat.{u + 1} f |>.obj P.F)) :
    (CurveCoefficientPair.IsConstructible
      ({ C := Y
         toSpec := g
         isCurve := inferInstance
         F := (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F
         isTorsion := hT } : CurveCoefficientPair k)) →
      P.IsConstructible := by
  sorry

end AlgebraicGeometry
