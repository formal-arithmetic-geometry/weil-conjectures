/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.EtaleImmersionShriekNormalization
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives

/-! # The specified compact-support comparison of an equal factored chart

Source: Stacks Project, Tags 0F7I, 0F7J and 0F7K; blueprint main-20261015,
opening and final paragraphs of sk-prop-sf-rf-shriek-preservation
(blueprint: lem-sf-etale-chart-left-compositor).

The helpers transport the existing canonical comparisons through the fully faithful
inclusions of D+. They construct the specified transformation, including its equality
transport, rather than choosing an isomorphism between its endpoint objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The existing open normalization, read in D+ by full faithfulness of its inclusion.
Source: Stacks Project, Tag 0F7I (blueprint: lem-sf-etale-chart-left-compositor). -/
noncomputable def etaleChartOpenNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W T : Scheme.{u}} (j : W ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (d : Compactification j) :
    rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility _ d ≪≫
      etaleOpenCompactSupportNormalization A j d ≪≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlusCompatibility.symm)

/-- The existing closed normalization, read in D+ by full faithfulness of its inclusion.
Source: Stacks Project, Tags 0F7I and 0F51
(blueprint: lem-sf-etale-chart-left-compositor). -/
noncomputable def etaleChartClosedNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (c : Z ⟶ T) [IsClosedImmersion c]
    (d : Compactification c) :
    rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d ≅
      (lowerStar (ModuleCat.{u + 1} A) c).mapDerivedCategoryPlus :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility _ d ≪≫
      etaleClosedCompactSupportNormalization A c d ≪≫
      (lowerStar (ModuleCat.{u + 1} A) c).mapDerivedCategoryPlusCompatibility.symm)

/-- The canonical compositor with three explicitly supplied compactifications, obtained
from the recorded compositor by the canonical changes of choice.
Source: Stacks Project, Tag 0F7J (blueprint: lem-sf-etale-chart-left-compositor). -/
noncomputable def etaleChartCompactSupportCompositor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g)) :
    rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cf ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cg ≅
      rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cfg := by
  letI := cf.hasCompactification
  letI := cg.hasCompactification
  letI := cfg.hasCompactification
  exact Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationPlusIso A cf
        (HasCompactification.compactification f)) _ ≪≫
    Functor.isoWhiskerLeft (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f)
      (rightDerivedLowerShriekOfCompactificationPlusIso A cg
        (HasCompactification.compactification g)) ≪≫
    rightDerivedLowerShriekPlusCompIso A f g ≪≫
    rightDerivedLowerShriekOfCompactificationPlusIso A
      (HasCompactification.compactification (f ≫ g)) cfg

/-- Substitution along the chart equality, followed by the canonical change between the
compactifications of the now identical morphism. Equality elimination supplies the transport.
Source: Stacks Project, Tag 0F7I (blueprint: lem-sf-etale-chart-left-compositor). -/
noncomputable def etaleChartCompactSupportTransport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} [QuasiCompact f] [QuasiCompact g]
    (h : f = g) (cf : Compactification f) (cg : Compactification g) :
    rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cf ≅
      rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cg := by
  subst g
  exact rightDerivedLowerShriekOfCompactificationPlusIso A cf cg

section Chart

variable (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U V P : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U] [IsNoetherian V] [IsNoetherian P]
    (f : X ⟶ Y) (s : U ⟶ X) (v : V ⟶ Y) (i : U ⟶ P) (p : P ⟶ V)
    [IsOpenImmersion s] [IsOpenImmersion v] [IsClosedImmersion i]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (h : s ≫ f = (i ≫ p) ≫ v)
    (cf : Compactification f) (cs : Compactification s) (cv : Compactification v)
    (ci : Compactification i) (cp : Compactification p)
    (csf : Compactification (s ≫ f)) (cip : Compactification (i ≫ p))
    (cipv : Compactification ((i ≫ p) ≫ v))

/-- The six specified arrows, with equality transport inserted between the middle values.
Every functor and every input in this construction belongs to D+.
Source: Stacks Project, Tags 0F7I, 0F7J, 0F7K
(blueprint: lem-sf-etale-chart-left-compositor). -/
noncomputable def etaleChartLeftCompositorPlus :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cf ≅
      (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cp ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus :=
  Functor.isoWhiskerRight (etaleChartOpenNormalization A s cs).symm _ ≪≫
    etaleChartCompactSupportCompositor A s f cs cf csf ≪≫
    etaleChartCompactSupportTransport A h csf cipv ≪≫
    (etaleChartCompactSupportCompositor A (i ≫ p) v cip cv cipv).symm ≪≫
    Functor.isoWhiskerRight
      (etaleChartCompactSupportCompositor A i p ci cp cip).symm _ ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (etaleChartClosedNormalization A i ci) _) _ ≪≫
    Functor.isoWhiskerLeft
      ((lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cp)
      (etaleChartOpenNormalization A v cv)

/-- The specified chart comparison in the ambient unbounded category, evaluated only on D+.
The endpoint compatibility maps identify the preceding six-arrow D+ construction with
Rf_! Ds_! and Dv_! Rp_! Di_* in the ordinary unbounded derived categories.
Source: Stacks Project, Tags 0F7J and 0F7K
(blueprint: lem-sf-etale-chart-left-compositor). -/
noncomputable def etaleChartLeftCompositor :
    DerivedCategory.Plus.ι ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) s).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf ≅
      DerivedCategory.Plus.ι ⋙ (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cp ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory :=
  Functor.isoWhiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility _ cf).symm ≪≫
    Functor.isoWhiskerRight
      (etaleChartLeftCompositorPlus A f s v i p h cf cs cv ci cp csf cip cipv)
      DerivedCategory.Plus.ι ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus
        (rightDerivedLowerShriekOfCompactificationPlusCompatibility _ cp))
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory

end Chart

/-- The constructed ambient chart isomorphism is natural on bounded-below inputs and
commutes with all canonical compactification changes. The definitions above specify its
six-factor value, including transport along h; its type asserts componentwise invertibility.

Source: Stacks Project, Tags 0F7I, 0F7J and 0F7K; blueprint main-20261015,
opening and final paragraphs of sk-prop-sf-rf-shriek-preservation
(blueprint: lem-sf-etale-chart-left-compositor).

Proof plan:
1. By lem-weil-pbc-module-sheaves-enough-injectives and
   lem-weil-pbc-dplus-injective-representative, represent any input with lower bound m by
   injectives vanishing below m. Extension by zero preserves that termwise bound. Resolve
   again with the same bound on the compactification; the resulting complex is K-injective.
   The construction def-amb-etale-compact-support computes Rr_* Dj_! by this complex,
   whose direct image still vanishes below m. Thus each compact-support intermediate is D+.
2. The exact immersion functors preserve the same bound by
   lem-sf-etale-immersion-shriek-normalization. Start with the inverse open normalization
   whiskered by Rf_!, then the (f,s) compositor of lem-amb-etale-compact-comparisons.
   Eliminate h to transport the middle value to the other factorization and apply the
   inverse (v,pi) compositor. These are the first three arrows of the specified formula.
3. Apply the inverse (p,i) compositor whiskered by Rv_!, then the closed normalization
   whiskered by Rp_! and Rv_!, then the open normalization for v at Rp_! Di_* H.
   All inputs are D+ by steps 1 and 2. These are the last three arrows of the formula.
4. Each arrow is an isomorphism. Reverse the arrows and take their inverses; associativity
   and adjacent inverse cancellations give both inverse equations.
5. Naturality of every normalization and compositor gives its component square. Inverse
   squares follow by multiplication by inverses; whiskered squares follow by applying the
   outer functor. Paste the six squares to obtain the displayed naturality equation.
6. For changed compactifications, use the canonical comparison at every intermediate
   functor. The compositor squares commute by lem-amb-etale-compact-comparisons, and the
   normalization squares by lem-sf-etale-immersion-shriek-normalization. Whisker and invert
   these squares as in step 5, then paste. Intermediate comparisons cancel, leaving exactly
   the endpoint equation below. Elimination of h handles equality transport, and the
   comparison cocycle law handles successive changes. -/
theorem etaleChartLeftCompositor_spec
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U V P : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U] [IsNoetherian V] [IsNoetherian P]
    (f : X ⟶ Y) (s : U ⟶ X) (v : V ⟶ Y) (i : U ⟶ P) (p : P ⟶ V)
    [IsOpenImmersion s] [IsOpenImmersion v] [IsClosedImmersion i]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (h : s ≫ f = (i ≫ p) ≫ v)
    (cf : Compactification f) (cs : Compactification s) (cv : Compactification v)
    (ci : Compactification i) (cp : Compactification p)
    (csf : Compactification (s ≫ f)) (cip : Compactification (i ≫ p))
    (cipv : Compactification ((i ≫ p) ≫ v)) :
    (∀ (H' H : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (a : H' ⟶ H),
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) s).mapDerivedCategory.map
            (DerivedCategory.Plus.ι.map a)) ≫
          (etaleChartLeftCompositor A f s v i p h cf cs cv ci cp csf cip cipv).hom.app H =
        (etaleChartLeftCompositor A f s v i p h cf cs cv ci cp csf cip cipv).hom.app H' ≫
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cp).map
              ((lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory.map
                (DerivedCategory.Plus.ι.map a)))) ∧
    (∀ (cf' : Compactification f) (cs' : Compactification s) (cv' : Compactification v)
      (ci' : Compactification i) (cp' : Compactification p)
      (csf' : Compactification (s ≫ f)) (cip' : Compactification (i ≫ p))
      (cipv' : Compactification ((i ≫ p) ≫ v)),
      (Functor.isoWhiskerLeft
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus
          (rightDerivedLowerShriekOfCompactificationPlusιIso A cf cf')).hom ≫
          (etaleChartLeftCompositor A f s v i p h cf' cs' cv' ci' cp' csf' cip' cipv').hom =
        (etaleChartLeftCompositor A f s v i p h cf cs cv ci cp csf cip cipv).hom ≫
          (Functor.isoWhiskerRight
            (Functor.isoWhiskerLeft
              (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus
              (rightDerivedLowerShriekOfCompactificationPlusιIso A cp cp'))
            (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory).hom) := by
  sorry

end AlgebraicGeometry.Etale
