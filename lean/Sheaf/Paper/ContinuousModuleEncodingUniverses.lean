/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.ContinuousRingUniverseRealization
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.LatticeSheafBasic
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # Section-action module encodings in the scheme universe

Source: Stacks Project, Tag 00YV; Bhatt--Scholze, Section 6.8.
(blueprint: def-sfb-continuous-coefficient-module-equivalence-universe)

These are the specified encodings formerly defined in IntegralScalarConstructibleImage.
They are separated here so ordinary module and scalar comparison lemmas can use them.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The section-action encoding, using the canonical continuous chart in arbitrary universe.
Source: Stacks Project, Tag 00YV; Bhatt--Scholze, Section 6.8.
(blueprint: def-sfb-continuous-coefficient-module-equivalence-universe). -/
def continuousRingModuleEquivalenceUniverse (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T] :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousCoefficientRingObj T) X) ≌
      SheafOfModules.{u + 1, u, u + 1, u + 1} (continuousCoefficientRingSheaf X T) := by
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
  let J := Scheme.ProEt.topology X
  let R := continuousCoefficientRingSheaf X T
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  letI : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj J R
    (fun V a b ↦ by
      exact @mul_comm (ULift.{u + 1} C(V.unop.left, T)) inferInstance a b)
  letI := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} T
  let φ := ContinuousRingUniverse.comparison X T
  letI := ContinuousRingUniverse.comparison_isIso X T
  exact (Mod.comapEquivalenceOfIsIso (inv φ)).trans
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J A).trans
      (ringModuleEquivalenceOfIso X (reconstructedRingIso X R).symm))

/-- The two section-ring presentations agree by the identity on continuous functions.
Source: Stacks Project, Tag 00YV; Bhatt--Scholze, Section 6.8.
(blueprint: def-sfb-continuous-coefficient-module-equivalence-universe). -/
def continuousSectionRingIso (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] :
    latticeModuleRing X T ≅ continuousCoefficientRingSheaf X T :=
  ObjectProperty.isoMk _
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

/-- The same encoding in the existing commutative coefficient-sheaf coordinates.
Source: Stacks Project, Tag 00YV; Bhatt--Scholze, Section 6.8.
(blueprint: def-sfb-continuous-coefficient-module-equivalence-universe). -/
def continuousLatticeModuleEquivalenceUniverse (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T] :=
  (continuousRingModuleEquivalenceUniverse X T).trans
    (ringModuleEquivalenceOfIso X (continuousSectionRingIso X T))

/-- The field encoding has the specified continuous section action.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Tag 00YV.
(blueprint: def-sfb-continuous-coefficient-module-equivalence-universe). -/
def continuousFieldModuleEquivalenceUniverse (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    (X : Scheme.{u}) :=
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  continuousLatticeModuleEquivalenceUniverse X E

/-- The integral encoding in completed coordinates, transported along the supplied
coefficient isomorphism. Consumers specify that isomorphism by every residue projection.
Source: Bhatt--Scholze, Lemma 6.8.2(1) and Section 6.8; Stacks Project, Tag 00YV.
(blueprint: def-weil-pbc-completed-continuous-module-encoding-universes). -/
def completedContinuousModuleEquivalence (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (c : Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E) ≅
      latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers l E)) :=
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  (continuousLatticeModuleEquivalenceUniverse X
    (Padic.coefficientExtensionIntegers l E)).trans
    (ringModuleEquivalenceOfIso X ((Scheme.adicLisseForget X).mapIso c))

/-- The inverse completed integral encoding is additive.
Source: Stacks Project, Tag 00YV; Bhatt--Scholze, Section 6.8.
(blueprint: def-weil-pbc-completed-continuous-module-encoding-universes).
Proof: each of the three equivalences leaves the additive section maps unchanged;
restriction along a ring isomorphism does likewise. Hence sums of arrows are preserved. -/
instance completedContinuousModuleEquivalence_inverse_additive (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (c : Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E) ≅
      latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers l E)) :
    (completedContinuousModuleEquivalence l E X c).inverse.Additive := by
  exact Functor.additive_of_preserves_binary_products _

/-- The inverse field encoding is additive.
Source: Stacks Project, Tag 00YV; Bhatt--Scholze, Section 6.8.
(blueprint: def-weil-pbc-completed-continuous-module-encoding-universes).
Proof: the section-action equivalence is the identity on additive sheaf maps, as is
transport along the reconstructed section-ring isomorphism. Ring restriction also
preserves addition of maps. Their composite and inverse therefore preserve addition. -/
instance continuousFieldModuleEquivalenceUniverse_inverse_additive (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E] (X : Scheme.{u}) :
    (continuousFieldModuleEquivalenceUniverse l E X).inverse.Additive := by
  exact Functor.additive_of_preserves_binary_products _

end AlgebraicGeometry.ProEtale.CondensedRing
