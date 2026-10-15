/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover
import Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Continuity of ordinary condensed-coefficient pushforward

Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).
-/

@[expose] public section

universe u v w x y z

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj


namespace AlgebraicGeometry.ProEtale

/-- The cocone obtained from good truncation, retaining the original complexes as its
source. Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity). -/
noncomputable def condensedContinuityCocone
    {A : Type v} [Category.{w} A] [Abelian A]
    {I : Type x} [Category.{y} I] (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)] : Cocone D :=
  (Cocone.precompose (Functor.whiskerLeft D
    ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A))).obj
      (colimit.cocone (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A))

/-- The canonical comparison induced by the maps to the termwise truncated colimit.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity). -/
noncomputable def condensedContinuityComparison
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type u} [Category.{z} B]
    {I : Type x} [Category.{y} I] (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    (T : CochainComplex A ℤ ⥤ B)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (D ⋙ T)] :
    colimit (D ⋙ T) ⟶ T.obj (condensedContinuityCocone D a).pt :=
  colimit.desc (D ⋙ T) (T.mapCocone (condensedContinuityCocone D a))

/-- Naturality in the strict diagram, including the specified map of truncated colimits.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).
Proof: precompose both sides with each colimit inclusion. Functoriality of good
truncation and naturality of its projection identify the resulting maps. The colimit
universal property gives equality. -/
theorem condensedContinuityComparison_naturality
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type u} [Category.{z} B]
    {I : Type x} [Category.{y} I] (D E : I ⥤ CochainComplex A ℤ) (α : D ⟶ E)
    (a : ℤ) (T : CochainComplex A ℤ ⥤ B)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (E ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (D ⋙ T)] [HasColimit (E ⋙ T)] :
    colimMap (Functor.whiskerRight α T) ≫ condensedContinuityComparison E a T =
      condensedContinuityComparison D a T ≫
        T.map (colimMap (Functor.whiskerRight α
          ((ComplexShape.embeddingUpIntGE a).truncGEFunctor A))) := by
  sorry

/-- The canonical comparison respects natural transformations of the output functor.
Together with the shifted cocone statements below, this specifies the comparison under
the usual derived shift and cohomology identifications.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).
Proof: precompose with every colimit inclusion and use naturality at the corresponding
map to the truncated colimit. The colimit universal property identifies the maps. -/
theorem condensedContinuityComparison_functor_naturality
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type u} [Category.{z} B]
    {I : Type x} [Category.{y} I] (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    (T S : CochainComplex A ℤ ⥤ B) (β : T ⟶ S)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (D ⋙ T)] [HasColimit (D ⋙ S)] :
    colimMap (Functor.whiskerLeft D β) ≫ condensedContinuityComparison D a S =
      condensedContinuityComparison D a T ≫ β.app (condensedContinuityCocone D a).pt := by
  sorry

/-- Evaluation of the underlying abelian sheaf at the terminal pro-etale object.
Its right derived functor is ordinary uncompleted derived global sections of modules.
Source: Hemo--Richarz--Scholbach, proof of Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity). -/
noncomputable abbrev condensedModuleSections
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) (condensedRingObj Λ X) ⥤
      AddCommGrpCat.{u + 1} :=
  Mod.forget (condensedRingObj Λ X) ⋙
    sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
      (evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
        (Opposite.op (Scheme.ProEt.mk (𝟙 X)))

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
/-- The ordinary uncompleted derived pushforward commutes with uniformly bounded-below
filtered colimits on cohomology. There is no torsion, completeness, or constructibility
condition on the coefficient ring or its modules.

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).

Proof: replace each complex by its good truncation at the common lower bound. Exactness
of filtered colimits in module sheaves identifies cohomology of their termwise colimit
with the colimit of cohomology. Cover every object of the target site by affine weakly
contractible objects V. Their inverse images W are qcqs because f is qcqs. Resolve W
by an acyclic hypercover whose terms are finite disjoint unions of weakly contractible
affines. On each component, evaluation is exact and preserves filtered colimits
(lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits). The hypercover
computes derived sections (lem-weil-pbc-proetale-hypercover-computes-bounded-complex).
In total degree r only the finitely many hypercover degrees 0 through r-a occur.
Evaluation commutes with the filtered colimit in each of these degrees; finite products
and finite sums commute with filtered colimits of modules. Thus the total complexes
are canonically identified, including both differential summands. Exact filtered
colimits then commute with cycles, boundaries and their quotient. On K-injective
resolutions, the formula (f_*J)(V)=J(W) identifies this with precisely the cohomology
comparison induced by the original cocone legs. The comparison is invertible on every
V. A sheaf map invertible on this covering basis is invertible: injectivity follows
from separation and surjectivity follows by lifting locally and gluing. -/
theorem condensed_qcqs_pushforward_continuity
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (q : ℤ) :
    IsIso (condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ q)) := by
  sorry

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
/-- Ordinary derived global sections of a qcqs scheme satisfy the same comparison.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).

Proof: apply the finite-diagonal hypercover calculation in the pushforward proof
directly to W=X. Exact evaluation on weakly contractible affines commutes with the
filtered colimit, and a common lower bound makes every total diagonal finite.
Filtered colimits of modules are exact, so taking cohomology gives precisely the
map induced by derived sections of each original cocone leg. Forgetting the scalar
action gives the asserted isomorphism of abelian groups. -/
theorem condensed_qcqs_globalSections_continuity
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (q : ℤ) :
    IsIso (condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ (condensedModuleSections Λ X).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ q)) := by
  sorry

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
/-- Compatibility of pushforward continuity with every integral shift. The shifted
cocone has exactly the shifts of the original cocone legs; its vertex is the shift of
Q(colim τ≥a D). Under the standard shift comparisons its universal colimit map is thus
the shifted original comparison, with lower bound a-s and cohomology degree q+s.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).
Proof: shift the bounded-below hypercover calculation. Reindex total degree r by r+s
and use the signed shift differential. The comparison on every colimit leg agrees
with the original one under the canonical derived shift identifications. The
universal property determines the comparison uniquely. -/
theorem condensed_qcqs_pushforward_continuity_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (s q : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q).mapCocone
        ((shiftFunctor _ s).mapCocone (condensedContinuityCocone D a)))) := by
  sorry

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
/-- Compatibility of derived global sections continuity with every integral shift. The shifted
cocone has exactly the shifts of the original cocone legs; its vertex is the shift of
Q(colim τ≥a D). Under the standard shift comparisons its universal colimit map is thus
the shifted original comparison, with lower bound a-s and cohomology degree q+s.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).
Proof: shift the bounded-below hypercover calculation. Reindex total degree r by r+s
and use the signed shift differential. The comparison on every colimit leg agrees
with the original one under the canonical derived shift identifications. The
universal property determines the comparison uniquely. -/
theorem condensed_qcqs_globalSections_continuity_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (s q : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.Q ⋙ (condensedModuleSections Λ X).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q).mapCocone
        ((shiftFunctor _ s).mapCocone (condensedContinuityCocone D a)))) := by
  sorry

/-- The representative form of continuity, independent of the choice of functorial
quasi-isomorphic representatives. The equation on each leg requires the specified
canonical derived map, rather than an arbitrary map of representatives.

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), hypercover proof
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-continuity).

Proof: exact filtered colimits in B commute with kernels, images, and cokernels,
so cohomology of the termwise colimit P is the colimit of its cohomology.
The natural isomorphism e identifies each term with F(QD_i), and ε identifies the
value at the truncated colimit. The leg equation identifies the cohomology map of
the displayed chain map with precisely the continuity comparison. It is an
isomorphism in every degree by h. Thus the chain map is a quasi-isomorphism.
The argument quantifies over all choices of P,L,e,ε and the normalized cocone, so
objectwise quasi-isomorphic replacements give the same derived comparison under
these identifications. Apply this with F equal to derived pushforward, or to derived
module sections, and h the corresponding continuity theorem above. -/
theorem condensedContinuityComparison_representatives
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type u} [Category.{z} B] [Abelian B] [HasDerivedCategory.{z} B]
    {I : Type x} [Category.{y} I] [IsFiltered I]
    [HasColimitsOfShape I B] [HasExactColimitsOfShape I B]
    (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    (F : DerivedCategory A ⥤ DerivedCategory B)
    [∀ q : ℤ, HasColimit (D ⋙ (DerivedCategory.Q ⋙ F ⋙
      DerivedCategory.homologyFunctor B q))]
    (h : ∀ q : ℤ, IsIso (condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor B q)))
    (P : I ⥤ CochainComplex B ℤ) [HasColimit P] (L : CochainComplex B ℤ)
    (e : D ⋙ DerivedCategory.Q ⋙ F ≅ P ⋙ DerivedCategory.Q)
    (ε : F.obj (DerivedCategory.Q.obj (condensedContinuityCocone D a).pt) ≅
      DerivedCategory.Q.obj L)
    (ι : P ⟶ (Functor.const I).obj L)
    (hι : ∀ i : I, e.hom.app i ≫ DerivedCategory.Q.map (ι.app i) =
      F.map (DerivedCategory.Q.map ((condensedContinuityCocone D a).ι.app i)) ≫ ε.hom) :
    QuasiIso (colimit.desc P (Cocone.mk L ι)) := by
  sorry

end AlgebraicGeometry.ProEtale
