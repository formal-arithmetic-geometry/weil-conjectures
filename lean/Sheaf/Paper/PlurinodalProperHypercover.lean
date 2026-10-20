/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.Paper.OrgogozoInductionData
public import Sheaf.AlgebraicGeometry.ProperHypercover
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.GenericComponentsSplit
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import Sheaf.RingTheory.QuasiExcellentNagata
import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.JapaneseDomain
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.ProperDimZeroFiniteOverField
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Ideal.GoingDown
import Sheaf.AlgebraicGeometry.ClosedDominantDimension
import Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular

/-!
# An almost plurinodal first term of a proper hypercover

Source: Orgogozo, Modifications et cycles proches sur une base générale, Proposition 3.3.1
and Lemma 3.3.2, printed pp. 9--10 (blueprint: lem-trf-plurinodal-proper-hypercover).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Orgogozo

/-- The number of curve factors in the recorded tower; the identity tower has length zero.
Source: Orgogozo §3.3, plurinodal morphisms as composites of curve fibrations
(blueprint: lem-trf-plurinodal-proper-hypercover). -/
def SemistableTower.length {S X : Scheme.{u}} {f : X ⟶ S}
    (P : SemistableTower S X f) : ℕ :=
  match P with
  | .identity => 0
  | .step tower _ _ => tower.length + 1

/-- A proper dominant morphism between integral excellent Noetherian schemes of finite
 dimension has, after an integral alteration of the base of the same dimension, a proper
 hypercover with almost plurinodal degree zero. The isomorphism of degree zero respects
 the structure map to the altered base. The lengths of all its semistable summands equal
 the original generic-fibre dimension. The datum already includes finite closed singular
 subschemes with relatively smooth complements and a proper nowhere dense vertical part.
 Every degree is of finite type and has its own finite fibre-dimension bound.

Source: Orgogozo, Proposition 3.3.1 and Lemma 3.3.2, printed pp. 9--10
(blueprint: lem-trf-plurinodal-proper-hypercover).

Proof plan:
1. Set K to the function field of S and d to the generic-fibre dimension. Finite type gives
   finite d [lem-kun-dimension-finite-type]. Split generic components over a finite separable
   extension L/K [lem-sbc-generic-components-split]; only geometric irreducibility is needed.
2. Normalize S in L [lem-weil-pbc-normalization-in-residue-field-extension]. Excellence implies
   Nagata [lem-exc-quasi-excellent-nagata, def-weil-pbc-nagata-ring,
   def-weil-pbc-japanese-domain], hence finiteness, properness [lem-weil-pbc-finite-proper],
   excellence [lem-exc-finite-type-localization-excellent] and Noetherianness
   [lem-weil-pbc-finite-type-over-noetherian]. This is an alteration with unchanged dimension
   [lem-trf-closed-dominant-dimension].
3. Take reduced component closures of the base change
   [lem-weil-pbc-proper-base-change, lem-weil-pbc-noetherian-finite-components,
   lem-weil-pbc-reduced-induced-closed-subscheme]. They are proper
   [lem-weil-pbc-closed-immersion-proper], excellent and Noetherian. Flat going down
   [lem-sc-flat-going-down] shows the dominating generic components have dimension d;
   use [lem-trf-closed-dominant-dimension] for their dimensions.
4. For positive d apply de Jong [lem-trf-de-jong-geometrically-irreducible-tower] to each
   dominating component, obtaining towers of length d. For d=0 the generic fibre is finite
   [lem-pc-dim-zero-finite-over-field], hence finite over a dense open
   [lem-weil-pbc-generic-finite-morphism-open-neighborhood]; use the identity tower.
5. Form the finite product of the altered bases over the normalization
   [def-pc-fibre-product, lem-weil-pbc-proper-base-change, lem-weil-pbc-proper-composition].
   A prime of its nonzero finite generic algebra has an integral reduced closure
   [lem-weil-pbc-reduced-induced-closed-subscheme], proper
   [lem-weil-pbc-closed-immersion-proper] and finite over a dense open
   [lem-weil-pbc-generic-finite-morphism-open-neighborhood]. This is a common alteration.
6. Its composite to S is an alteration by proper composition and generic finiteness. It is
   excellent and Noetherian by the finite-type permanence results above, and has dimension
   equal to that of S [lem-trf-closed-dominant-dimension].
7. Pull back all towers to this common base. Properness, flatness and finite presentation
   persist [lem-weil-pbc-proper-base-change, lem-weil-pbc-flat-morphism-base-change,
   lem-weil-pbc-qcqs-morphism-permanence]; geometric curve conditions persist as well.
   The maps to the pulled-back components are proper [lem-weil-pbc-proper-to-separated].
8. Geometric irreducibility [def-pc-geometrically-irreducible] makes the generic component
   unique after field extension. Proper images cover that component, and surjectivity
   persists under the final field extension [lem-weil-pbc-surjective-base-change].
9. Adjoin the reduced union of all vertical components. Its proper closed image omits the
   generic point, so is nowhere dense. The finite disjoint union P maps properly and
   surjectively to Z = X times_S T; this follows componentwise from properness and the
   two classes of components [def-weil-proper-morphism].
10. For every curve factor use its first-Fitting singular closed subscheme
    [lem-trf-nodal-family-fitting-singular]. It is proper, unramified, hence locally
    quasi-finite [lem-weil-pbc-unramified-quasi-finite-at-points], and finite
    [pqf-lem-proper-lqf-finite]. Its complement is relatively smooth; the geometric fibres
    have exactly the curve conditions of [def-trf-orgogozo-induction-data].
11. Take the augmented Cech nerve of P over Z (all products over Z). Its degree-zero map
    is proper surjective; positive matching maps are isomorphisms by the fibre-product
    universal property [def-pc-fibre-product], including all simplicial identities.
12. Every Cech term is proper over T by base change and composition, hence finite type.
    Apply [lem-fin-finite-type-fibre-dimension-bound] to each term separately. Steps 6
    and 10 supply the base-dimension equality and all tower and vertical data. -/
theorem exists_plurinodal_proper_hypercover {S X : Scheme.{u}}
    [IsIntegral S] [IsIntegral X] [IsNoetherian S] [IsNoetherian X]
    (hS : IsExcellentScheme S) (hX : IsExcellentScheme X)
    (hdimS : topologicalKrullDim S < ⊤) (hdimX : topologicalKrullDim X < ⊤)
    (f : X ⟶ S) [IsProper f] [IsDominant f] :
    ∃ (T : Scheme.{u}) (a : T ⟶ S) (_ : IsIntegral T) (_ : IsNoetherian T)
      (D : AlmostPlurinodalDatum T) (Y : SimplicialObject (Over (pullback f a)))
      (e : (Y.obj (op (SimplexCategory.mk 0))).left ≅ D.source),
      IsExcellentScheme T ∧ IsAlteration a ∧ IsProperHypercover Y ∧
      e.hom ≫ D.morphism = (Y.obj (op (SimplexCategory.mk 0))).hom ≫ pullback.snd f a ∧
      (∀ i : Fin D.count,
        ((D.towers i).length : WithBot ℕ∞) = topologicalKrullDim (f.fiber (genericPoint S))) ∧
      (∀ n : ℕ,
        LocallyOfFiniteType ((Y.obj (op (SimplexCategory.mk n))).hom ≫ pullback.snd f a) ∧
        QuasiCompact ((Y.obj (op (SimplexCategory.mk n))).hom ≫ pullback.snd f a) ∧
        ∃ b : ℕ, ∀ t : T,
          topologicalKrullDim
            (((Y.obj (op (SimplexCategory.mk n))).hom ≫ pullback.snd f a).fiber t) ≤
              (b : WithBot ℕ∞)) ∧
      topologicalKrullDim T = topologicalKrullDim S := by
  sorry

end AlgebraicGeometry.Orgogozo
