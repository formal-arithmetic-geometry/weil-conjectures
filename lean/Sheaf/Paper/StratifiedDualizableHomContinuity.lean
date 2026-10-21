/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.CondensedScalarRealization
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisPushforward
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Constructible
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

import Sheaf.Paper.RHomColimitCohomologyLadder
import Sheaf.SixFunctors.ConstructibleOpenClosedRefinement
import Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import Sheaf.Algebra.Homology.ProEtaleInternalHomLowerBound
import Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import WeilConjectures.Algebra.Homology.DerivedInternalHomShiftRight
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # Hom continuity for stratified dualizable condensed complexes

Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3(2), including
its final global-Hom assertion (blueprint: lem-pod-stratified-dualizable-hom-continuity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w x y
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]

/-- A scalar section, viewed as a map from the tensor unit and pulled back to X.
Source: HRS Lemma 5.3, scalar action on global Hom
(blueprint: lem-pod-stratified-dualizable-hom-continuity). -/
def stratifiedHomScalarSection (X : Scheme.{u}) (s : condensedScalarRing Λ.X) :
    𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ condensedRingObj Λ.X X :=
  Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
    (upperStarFromPoint X).map
      (Functor.LaxMonoidal.ε
          (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
        ((constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
          terminalIsTerminal).homEquiv _ Λ.X).symm
            (AddCommGrpCat.ofHom ((zmultiplesHom _ s).comp
              AddEquiv.ulift.toAddMonoidHom)))

/-- The canonical central action of a scalar on the ordinary derived category.
Source: HRS Lemma 5.3, final assertion
(blueprint: lem-pod-stratified-dualizable-hom-continuity). -/
def stratifiedHomScalarCenter (X : Scheme.{u}) (s : condensedScalarRing Λ.X) :
    CatCenter (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))) :=
  qbar_derivedCenter (Mod.qbar_scalarNatEndo (stratifiedHomScalarSection Λ X s))

/-- The canonical scalar action respects all ring operations.
Source: HRS Lemma 5.3, module structure in the global-Hom assertion
(blueprint: lem-pod-stratified-dualizable-hom-continuity).
Proof: the constant-sheaf adjunction sends s to multiplication by its restrictions.
The strong monoidal inverse image carries products and the unit to those of B.
The regular-module action gives the same multiplication on every module; commuting
with the action uses commutativity of B. Termwise extension and localization preserve
these equalities and their additive versions. Thus the induced central endomorphisms
respect one, multiplication, zero and addition. -/
theorem stratifiedHomScalarCenter_laws (X : Scheme.{u}) :
    stratifiedHomScalarCenter Λ X 1 = 1 ∧
    (∀ s t, stratifiedHomScalarCenter Λ X (s * t) =
      stratifiedHomScalarCenter Λ X s * stratifiedHomScalarCenter Λ X t) ∧
    stratifiedHomScalarCenter Λ X 0 = 0 ∧
    (∀ s t, stratifiedHomScalarCenter Λ X (s + t) =
      stratifiedHomScalarCenter Λ X s + stratifiedHomScalarCenter Λ X t) := by
  sorry

/-- The ring map specifying the pulled-back central scalar action, with fixed values.
Source: HRS Lemma 5.3, global-Hom assertion
(blueprint: lem-pod-stratified-dualizable-hom-continuity). -/
def stratifiedHomScalarMap (X : Scheme.{u}) :
    condensedScalarRing Λ.X →+* CatCenter (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))) where
  toFun := stratifiedHomScalarCenter Λ X
  map_one' := (stratifiedHomScalarCenter_laws Λ X).1
  map_mul' := (stratifiedHomScalarCenter_laws Λ X).2.1
  map_zero' := (stratifiedHomScalarCenter_laws Λ X).2.2.1
  map_add' := (stratifiedHomScalarCenter_laws Λ X).2.2.2

/-- Derived Hom groups carry the action of Γ(*,Λ) pulled back to X.
Source: HRS Lemma 5.3, global-Hom assertion
(blueprint: lem-pod-stratified-dualizable-hom-continuity). -/
instance stratifiedHomLinear (X : Scheme.{u}) :
    Linear (condensedScalarRing Λ.X) (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))) :=
  Linear.ofRingMorphism (stratifiedHomScalarMap Λ X)

end AlgebraicGeometry.ProEtale

namespace CategoryTheory

variable {R : Type w} [Ring R] {A : Type v} [Category.{x} A] [Abelian A]
  [HasDerivedCategory.{y} A] [Linear R (DerivedCategory A)]

/-- Shifted Hom as a functor to modules, with postcomposition transition maps.
Source: HRS Lemma 5.3, passage to degree r
(blueprint: lem-pod-stratified-dualizable-hom-continuity). -/
def stratifiedShiftedLinearHom (R : Type w) [Ring R] [Linear R (DerivedCategory A)]
    (K : DerivedCategory A) (r : ℤ) : CochainComplex A ℤ ⥤ ModuleCat.{y} R :=
  DerivedCategory.Q ⋙ shiftFunctor _ r ⋙ (linearCoyoneda R _).obj (op K)

/-- The actual colimit comparison on shifted Hom modules.
Source: HRS Lemma 5.3, canonical global-Hom comparison
(blueprint: lem-pod-stratified-dualizable-hom-continuity). -/
def stratifiedHomComparison (K : DerivedCategory A) (r : ℤ)
    {I : Type u} [Category.{u} I] (C : I ⥤ CochainComplex A ℤ)
    [HasColimit C] [HasColimit (C ⋙ stratifiedShiftedLinearHom R K r)] :
    colimit (C ⋙ stratifiedShiftedLinearHom R K r) ⟶
      (stratifiedShiftedLinearHom R K r).obj (colimit C) :=
  colimit.desc _ ((stratifiedShiftedLinearHom R K r).mapCocone (colimit.cocone C))

/-- Precomposition by a source map, as a transformation of the shifted Hom functors.
Source: HRS Lemma 5.3, naturality in the source
(blueprint: lem-pod-stratified-dualizable-hom-continuity). -/
def stratifiedHomPrecomp {K K' : DerivedCategory A} (f : K' ⟶ K) (r : ℤ) :
    stratifiedShiftedLinearHom R K r ⟶ stratifiedShiftedLinearHom R K' r :=
  Functor.whiskerLeft (DerivedCategory.Q ⋙ shiftFunctor _ r)
    ((linearCoyoneda R _).map f.op)

/-- The comparison has precisely the cocone-leg formula stated in the node.
Source: HRS Lemma 5.3, final global-Hom assertion
(blueprint: lem-pod-stratified-dualizable-hom-continuity).
Proof: the defining equation colimit.ι_desc identifies the map with the corresponding
component of the mapped cocone. Linear coyoneda is postcomposition, giving Q(ι)[r] ∘ u. -/
theorem stratifiedHomComparison_leg (K : DerivedCategory A) (r : ℤ)
    {I : Type u} [Category.{u} I] (C : I ⥤ CochainComplex A ℤ)
    [HasColimit C] [HasColimit (C ⋙ stratifiedShiftedLinearHom R K r)]
    (i : I) (f : K ⟶ (DerivedCategory.Q.obj (C.obj i))⟦r⟧) :
    (colimit.ι (C ⋙ stratifiedShiftedLinearHom R K r) i ≫
      stratifiedHomComparison (R := R) K r C) f =
        f ≫ (shiftFunctor _ r).map (DerivedCategory.Q.map (colimit.ι C i)) := by
  sorry

/-- Naturality of the module comparison under arbitrary morphisms of strict diagrams.
Source: HRS Lemma 5.3, canonical global-Hom comparison
(blueprint: lem-pod-stratified-dualizable-hom-continuity).
Proof: precompose with each colimit inclusion. Naturality of the map of colimits and
functoriality give the same postcomposition; the colimit universal property concludes. -/
theorem stratifiedHomComparison_diagram_naturality (K : DerivedCategory A) (r : ℤ)
    {I : Type u} [Category.{u} I] (C E : I ⥤ CochainComplex A ℤ) (α : C ⟶ E)
    [HasColimit C] [HasColimit E]
    [HasColimit (C ⋙ stratifiedShiftedLinearHom R K r)]
    [HasColimit (E ⋙ stratifiedShiftedLinearHom R K r)] :
    colimMap (Functor.whiskerRight α (stratifiedShiftedLinearHom R K r)) ≫
      stratifiedHomComparison (R := R) K r E =
        stratifiedHomComparison (R := R) K r C ≫
          (stratifiedShiftedLinearHom R K r).map (colimMap α) := by
  sorry

/-- Contravariant naturality of the module comparison in its source object.
Source: HRS Lemma 5.3, canonical global-Hom comparison
(blueprint: lem-pod-stratified-dualizable-hom-continuity).
Proof: precompose with each colimit inclusion. Both resulting maps send u to
Q(ι)[r] ∘ u ∘ f by associativity. The colimit universal property concludes. -/
theorem stratifiedHomComparison_source_naturality {K K' : DerivedCategory A}
    (f : K' ⟶ K) (r : ℤ) {I : Type u} [Category.{u} I]
    (C : I ⥤ CochainComplex A ℤ) [HasColimit C]
    [HasColimit (C ⋙ stratifiedShiftedLinearHom R K r)]
    [HasColimit (C ⋙ stratifiedShiftedLinearHom R K' r)] :
    colimMap (Functor.whiskerLeft C (stratifiedHomPrecomp (R := R) f r)) ≫
      stratifiedHomComparison (R := R) K' r C =
        stratifiedHomComparison (R := R) K r C ≫
          (stratifiedHomPrecomp (R := R) f r).app (colimit C) := by
  sorry

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Stratified dualizable sources commute with uniformly bounded-below filtered Hom colimits.
The comparison is an arrow in Γ(*,Λ)-modules, using the canonical central action above.
Source: HRS Lemma 5.3(2) and its final global-Hom assertion, in cohomological degree r
(blueprint: lem-pod-stratified-dualizable-hom-continuity).

Proof: (1) Exact filtered colimits of module sheaves commute with cohomology, preserve
quasi-isomorphisms and common lower bounds (lem-sfb-rhom-colimit-cohomology-ladder).
Good truncations give functorial strictly bounded-below representatives.
(2) Refine the finite constructible partition to a finite binary open-closed tree by
lem-fix-constructible-open-closed-refinement. Pullback preserves dualizability by
lem-zl-condensed-lisse-proetale-locality. Every vertex source is stratified dualizable
and bounded above by lem-pod-stratified-dualizable-bounded; constructible preimages use
lem-pur-scheme-constructible-preimage. Empty vertices give zero categories.
(3) On a leaf, the two exact-pairing contractions identify RHom(K,-) with D tensor -
by lem-sf-ringed-derived-closed-symmetric-monoidal. A K-flat model of D exists by
lem-pc-kflat-resolution. Its total tensor commutes with termwise filtered colimits by
lem-pc-module-filtered-colimits-tensor. Step (1) and
lem-weil-pbc-unbounded-derived-iso-cohomology prove internal-Hom continuity there.
The source upper bound gives uniform internal-Hom lower bounds by
lem-weil-pbc-proetale-internal-hom-lower-bound.
(4) For complementary open j and closed i, use the triangle i_* Ri! N → N → Rj_* j* N
from lem-weil-pbc-condensed-open-closed-recollement. Compare its cohomology sequences
using lem-weil-pbc-derived-cohomology-ladder. Continuity of the open direct image is
lem-weil-pbc-condensed-qcqs-pushforward-continuity. The five lemma
(lem-weil-pbc-five-lemma) gives continuity of i_* Ri!. Exactness and continuity of i_*
(lem-weil-pbc-proetale-ringed-open-closed) and i* i_* = id give continuity of Ri!;
its left t-exactness gives a common lower bound.
(5) The two evaluation-normalized formulas of lem-sfb-open-closed-internal-hom-formulas
then give continuity for j! K_U and i_* K_Z. The localization triangle for K and the
exact Hom ladder of lem-sfb-rhom-colimit-cohomology-ladder give continuity for K by
another five lemma. Induct up the finite tree.
(6) If K has upper bound b, its internal-Hom targets have common lower bound a-b.
Apply the global-sections clause of lem-weil-pbc-condensed-qcqs-pushforward-continuity.
Use lem-pur-rhom-global-sections and lem-pur-derived-internal-hom-shift-right to identify
its degree r comparison with Hom(K,QC_i[r]). Naturality identifies its legs with
postcomposition by Q(ι_i)[r]. Scalar multiplication is the pulled-back central action,
so the comparison is linear; the generic naturality theorems above give both variables. -/
theorem stratified_dualizable_hom_continuity
    (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y)))
    (hK : ∃ S : Y.FiniteLocallyClosedStratification,
      (∀ i, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i, Nonempty (HasRightDual
        ((CondensedRing.upperStar Λ.X (S.immersion i)).mapDerivedCategory.obj K)))
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (C : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (j : ℤ), j < a → IsZero ((C.obj i).X j)) (r : ℤ) :
    IsIso (stratifiedHomComparison (R := condensedScalarRing Λ.X) K r C) := by
  sorry

end AlgebraicGeometry.ProEtale
