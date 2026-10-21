/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Sheaf.AlgebraicGeometry.CohomologyPullbackExactConservative
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.SpecFiniteProductFields
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Sheaf.AlgebraicGeometry.StrictLocalBaseAffine
import Sheaf.AlgebraicGeometry.StrictLocalBaseIndEtale
import WeilConjectures.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import Sheaf.AlgebraicGeometry.ZeroDimensionalSpectrumProfinite
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Pointwise comparison for strict-local geometric fibres

Source: Stacks Project, Tags 03Q9 and 03Q1; corrected Tag 0EZV proof, steps 6--7.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Points of the geometric strict-local base and lifts to the strict henselization
give the same pointwise bijectivity tests for the derived unit.
Source: Stacks Project, Tags 03Q9, 03Q1 and 03PN; corrected Tag 0EZV proof.
(blueprint: lem-weil-pbc-strict-local-fibre-unit-stalks).

Proof: put A=S_(xf), B=X_(x), T=Spec K, E=A×_S T, Y=B×_S T and p:Y→E.
The ind-etale coordinate ring of E is a filtered colimit of finite products of K.
At each prime, its local ring and residue field are K: the selected-factor idempotent
annihilates the difference between any represented element and its scalar value.
Thus points of E are exactly sections T→E, equivalently lifts v:T→A over the fixed map
t:T→S. For any algebraically closed extension of the residue field, pointed clopen
neighbourhoods are cofinal in pointed etale neighbourhoods, by spreading finitely many
generators and relations and then choosing a clopen inside the resulting principal open.
Their ring colimit is the ordinary local ring K, since every fraction is defined on a
clopen neighbourhood and every section with zero germ vanishes on a smaller clopen.
Hence the strict localization at every such geometric point is T, compatibly over E.

The schemes E and Y are affine, so p is qcqs. The unrestricted strict-henselization
stalk theorem applied to p and p⁻¹a⁻¹F identifies the target homology-sheaf stalk with
H^q(Y×_E T,F). The pullback universal property identifies Y×_E T with B×_(A,v)T.
For q=0, inverse-image stalk compatibility identifies the source with F(T), since
Spec K has a terminal pointed etale neighbourhood for computing every geometric stalk.
The germ and unit compatibilities identify the actual stalk map with fibre pullback:
a representative section restricts to the marked section, and the unit image restricts
to the base-changed section. For q>0, both the source homology sheaf of the degree-zero
complex and H^q(T,F) vanish; the latter follows from separably closed field acyclicity.
Thus the same bijectivity criterion holds in positive degrees. Every lift gives a point,
and every point gives a lift; their equality over A
is the displayed projection equation. The argument uses
every geometric point over each ordinary point, so no choice of algebraic closure or
embedding is a hypothesis. -/
theorem strictLocalFibre_unit_stalks
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (K : Type u) [Field K] [IsSepClosed K]
    (u : Spec (.of K) ⟶ Scheme.strictHenselizationScheme (x ≫ f))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let t := u ≫ Scheme.strictHenselizationStructuralMap (x ≫ f)
    let p := pullback.map
      (Scheme.strictHenselizationStructuralMap x ≫ f) t
      (Scheme.strictHenselizationStructuralMap (x ≫ f)) t
      (Scheme.strictHenselizationMap f x) (𝟙 _) (𝟙 _)
      (by simpa using (Scheme.strictHenselizationMap_over f x).symm) (by simp)
    let a := pullback.snd (Scheme.strictHenselizationStructuralMap (x ≫ f)) t
    let E := pullback (Scheme.strictHenselizationStructuralMap (x ≫ f)) t
    let M := derivedPullbackUnitHomology p
      ((upperStar AddCommGrpCat.{u + 1} a).obj F) q
    (∀ z : E, ∃ v : Spec (.of K) ⟶ Scheme.strictHenselizationScheme (x ≫ f),
      v ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) = t ∧
      E.algClosurePoint z ≫
          pullback.fst (Scheme.strictHenselizationStructuralMap (x ≫ f)) t =
        (E.algClosurePoint z ≫ a) ≫ v ∧
      (IsIso ((Scheme.pointSmallEtale (E.algClosurePoint z)).sheafFiber.map M) ↔
        Function.Bijective (cohomologyMap
          (pullback.snd (Scheme.strictHenselizationMap f x) v) F q))) ∧
    (∀ (v : Spec (.of K) ⟶ Scheme.strictHenselizationScheme (x ≫ f)),
      v ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) = t →
      ∃ z : E,
        E.algClosurePoint z ≫
            pullback.fst (Scheme.strictHenselizationStructuralMap (x ≫ f)) t =
          (E.algClosurePoint z ≫ a) ≫ v ∧
        (IsIso ((Scheme.pointSmallEtale (E.algClosurePoint z)).sheafFiber.map M) ↔
          Function.Bijective (cohomologyMap
            (pullback.snd (Scheme.strictHenselizationMap f x) v) F q))) := by
  sorry

end AlgebraicGeometry.Etale
