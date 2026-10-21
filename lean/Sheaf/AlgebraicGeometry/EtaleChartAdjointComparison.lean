/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Mathlib.CategoryTheory.HomCongr
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.Etale.OpenExtensionZeroEtaleAdjunctionAgreement

/-! # Natural Hom comparison on an ordinary etale factored chart

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-sf-rf-shriek-preservation`, opening and final paragraphs; Stacks Tags
0F7I, 0F7J, 0F7K, 04FX and 03S5
(blueprint: lem-sf-etale-chart-adjoint-comparison).

The helpers construct the specified compact-support comparison from the canonical
bounded-below compositors. Only the test object belongs to D+; the targets of the
Hom functors, and the input K, remain in the ordinary unbounded categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.ChartAdjointComparison

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Normalize compact support along an open immersion by its compactification `(j,id)`.
Source: Stacks Tag 0F7I, open normalization in proof step 1
(blueprint: lem-sf-etale-chart-adjoint-comparison). -/
noncomputable def openNormalization {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [HasCompactification j] [QuasiCompact j] :
    R(j)_![ModuleCat.{u + 1} A]+ ≅ D+((j)_!open[ModuleCat.{u + 1} A]) :=
  (derivedPlusFormalism (ModuleCat.{u + 1} A)).shriekIso
      (HasCompactification.compactification j) (Compactification.ofIsOpenImmersion j) ≪≫
    Functor.isoWhiskerLeft D+((j)_!open[ModuleCat.{u + 1} A])
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pfId X) ≪≫
    Functor.rightUnitor _

/-- Normalize compact support along a closed immersion by `(id,i)` and exactness of `i_*`.
Source: Stacks Tags 0F51 and 04FX, proof step 1
(blueprint: lem-sf-etale-chart-adjoint-comparison). -/
noncomputable def closedNormalization {U P : Scheme.{u}} (i : U ⟶ P)
    [IsClosedImmersion i] [HasCompactification i] :
    R(i)_![ModuleCat.{u + 1} A]+ ≅ D+((i)_*[ModuleCat.{u + 1} A]) :=
  (derivedPlusFormalism (ModuleCat.{u + 1} A)).shriekIso
      (HasCompactification.compactification i) (Compactification.ofIsProper i) ≪≫
    Functor.isoWhiskerRight
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shId U)
      R+((i)_*[ModuleCat.{u + 1} A]) ≪≫
    Functor.leftUnitor _ ≪≫
    (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus

variable {X Y U V P : Scheme.{u}}
variable (f : X ⟶ Y) (s : U ⟶ X) (v : V ⟶ Y) (i : U ⟶ P) (p : P ⟶ V)
variable [IsOpenImmersion s] [IsOpenImmersion v] [IsClosedImmersion i]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
variable [QuasiCompact s] [QuasiCompact v]
variable [HasCompactification f] [HasCompactification s] [HasCompactification v]
variable [HasCompactification i] [HasCompactification p]
variable [HasCompactification (s ≫ f)] [HasCompactification (i ≫ p)]
variable [HasCompactification (i ≫ p ≫ v)] [HasCompactification ((i ≫ p) ≫ v)]
variable (w : s ≫ f = i ≫ p ≫ v)

/-- The canonical bounded-below left comparison, with the open and closed factors normalized.
It is alpha(f,s), transport along `fs=vpi`, then the inverses of alpha(v,pi) and alpha(p,i).
Source: Stacks Tags 0F7I--0F7K, proof steps 1 and 3
(blueprint: lem-sf-etale-chart-adjoint-comparison). -/
noncomputable def leftComparisonPlus :
    D+((s)_!open[ModuleCat.{u + 1} A]) ⋙ R(f)_![ModuleCat.{u + 1} A]+ ≅
      D+((i)_*[ModuleCat.{u + 1} A]) ⋙ R(p)_![ModuleCat.{u + 1} A]+ ⋙
        D+((v)_!open[ModuleCat.{u + 1} A]) :=
  Functor.isoWhiskerRight (openNormalization A s).symm _ ≪≫
    rightDerivedLowerShriekPlusCompIso A s f ≪≫
    rightDerivedLowerShriekPlusCongr A w ≪≫
    (rightDerivedLowerShriekPlusCongr A (Category.assoc i p v)).symm ≪≫
    (rightDerivedLowerShriekPlusCompIso A (i ≫ p) v).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerShriekPlusCompIso A i p).symm _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight (closedNormalization A i) _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D+((i)_*[ModuleCat.{u + 1} A])
      (Functor.isoWhiskerLeft R(p)_![ModuleCat.{u + 1} A]+ (openNormalization A v))

/-- The same specified comparison in the ambient category, evaluated only on a D+ input.
The compatibility isomorphisms retain the unbounded `Rf_!` and `Rp_!`.
Source: Stacks Tags 0F7I--0F7K, proof step 3
(blueprint: lem-sf-etale-chart-adjoint-comparison). -/
noncomputable def leftComparison
    (H : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    R(f)_![ModuleCat.{u + 1} A].obj
        (D((s)_!open[ModuleCat.{u + 1} A]).obj H.obj) ≅
      D((v)_!open[ModuleCat.{u + 1} A]).obj
        (R(p)_![ModuleCat.{u + 1} A].obj
          (D((i)_*[ModuleCat.{u + 1} A]).obj H.obj)) :=
  ((rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).app
      (D+((s)_!open[ModuleCat.{u + 1} A]).obj H)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso ((leftComparisonPlus A f s v i p w).app H) ≪≫
    D((v)_!open[ModuleCat.{u + 1} A]).mapIso
      ((rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) p).app
        (D+((i)_*[ModuleCat.{u + 1} A]).obj H))

/-- The normalization `Ri_! H ≅ i_* H` for a bounded-below test object, in the ambient category.
Source: Stacks Tags 0F51 and 04FX, proof steps 1 and 5
(blueprint: lem-sf-etale-chart-adjoint-comparison). -/
noncomputable def closedNormalizationAmbient {U P : Scheme.{u}} (i : U ⟶ P)
    [IsClosedImmersion i] [HasCompactification i]
    (H : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    R(i)_![ModuleCat.{u + 1} A].obj H.obj ≅
      D((i)_*[ModuleCat.{u + 1} A]).obj H.obj :=
  ((rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) i).app H).symm ≪≫
    DerivedCategory.Plus.ι.mapIso ((closedNormalization A i).app H)

variable (F : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
variable (G : DerivedCategoryModule A V ⥤ DerivedCategoryModule A P)
variable (I : DerivedCategoryModule A P ⥤ DerivedCategoryModule A U)
variable (adjF : R(f)_![ModuleCat.{u + 1} A] ⊣ F)
variable (adjP : R(p)_![ModuleCat.{u + 1} A] ⊣ G)
variable (adjI : R(i)_![ModuleCat.{u + 1} A] ⊣ I)

/-- The forward chain of ordinary Hom adjunctions specified by the node, before inversion.
Source: blueprint main-20261015, `sk-prop-sf-rf-shriek-preservation`, opening and final
paragraphs, expanded in proof steps 2--6
(blueprint: lem-sf-etale-chart-adjoint-comparison). -/
noncomputable def homChain
    (H : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : DerivedCategoryModule A Y) :
    (H.obj ⟶ D((s)^*[ModuleCat.{u + 1} A]).obj (F.obj K)) ≃
      (H.obj ⟶ I.obj (G.obj (D((v)^*[ModuleCat.{u + 1} A]).obj K))) :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) s).homEquiv H.obj (F.obj K)).symm |>.trans
    ((adjF.homEquiv _ K).symm) |>.trans
    (Iso.homCongr (leftComparison A f s v i p w H) (Iso.refl K)) |>.trans
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) v).homEquiv _ K) |>.trans
    (adjP.homEquiv _ _) |>.trans
    (Iso.homCongr (closedNormalizationAmbient A i H).symm (Iso.refl _)) |>.trans
    (adjI.homEquiv H.obj _)

/-- The canonical Hom comparison is the inverse of `homChain`, natural in both variables.
Neither representing target is required to be bounded below.

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-sf-rf-shriek-preservation`, opening and final paragraphs
(blueprint: lem-sf-etale-chart-adjoint-comparison).

Proof plan, following the six steps of the node:
1. Normalize opens by `(j,id)` and the closed immersion by `(id,i)`, using
   lem-amb-etale-compact-comparisons. The latter is proper and finite by
   lem-weil-pbc-closed-immersion-proper and lem-weil-pbc-closed-immersion-finite.
   Apply lemma-weil-pbc-finite-direct-image-exact with module coefficients. Exactness
   and lem-weil-pbc-extension-by-zero-exact preserve the lower bounds of all inputs.
2. Apply the inverse Hom direction of the unbounded open adjunction at s and then
   of thm-amb-etale-exceptional-adjoint at f. The open adjunction agrees with the sum
   adjunction of lem-amb-etale-adjoint-locality by
   lem-cbc-open-extension-zero-etale-adjunction-agreement, since s is etale by
   lem-weil-pbc-open-immersion-etale. K remains arbitrary.
3. Compose the canonical bounded-below compact-support compositors of
   lem-amb-etale-compact-comparisons, transport along w, and invert the other two
   compositors. After normalization this is exactly `leftComparison`. Precompose
   with its inverse; its target Hom object can be arbitrary.
4. Apply the unbounded open adjunction at v, with the same agreement as at s.
5. Apply the ambient compact-support adjunctions at p and i, transporting through
   `closedNormalizationAmbient` for the exact i_*. The intermediate object
   p^times(v^*K) need not belong to D+.
6. Invert this chain of bijections. Naturality of every adjunction Hom equivalence,
   the compact-support compositor, and the normalization isomorphisms gives the two
   naturality identities below. Cancel adjacent inverse equivalences for the two
   inverse identities. This proves exactly the specified inverse-chain comparison,
   without using bounded-below tests to assert an isomorphism of representing objects. -/
theorem exists_homEquiv
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U]
    [IsNoetherian V] [IsNoetherian P] :
    ∃ e : ∀
        (H : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (K : DerivedCategoryModule A Y),
        (H.obj ⟶ I.obj (G.obj (D((v)^*[ModuleCat.{u + 1} A]).obj K))) ≃
          (H.obj ⟶ D((s)^*[ModuleCat.{u + 1} A]).obj (F.obj K)),
      (∀ H K, (e H K).symm = homChain A f s v i p w F G I adjF adjP adjI H K) ∧
      (∀ (H H' : DerivedCategory.Plus
          (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) (a : H' ⟶ H)
          (K : DerivedCategoryModule A Y)
          (b : H.obj ⟶ I.obj (G.obj (D((v)^*[ModuleCat.{u + 1} A]).obj K))),
        e H' K (DerivedCategory.Plus.ι.map a ≫ b) =
          DerivedCategory.Plus.ι.map a ≫ e H K b) ∧
      (∀ (H : DerivedCategory.Plus
          (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
          (K K' : DerivedCategoryModule A Y) (a : K ⟶ K')
          (b : H.obj ⟶ I.obj (G.obj (D((v)^*[ModuleCat.{u + 1} A]).obj K))),
        e H K' (b ≫ I.map (G.map (D((v)^*[ModuleCat.{u + 1} A]).map a))) =
          e H K b ≫ D((s)^*[ModuleCat.{u + 1} A]).map (F.map a)) := by
  sorry

end AlgebraicGeometry.Etale.ChartAdjointComparison
