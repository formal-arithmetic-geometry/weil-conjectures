/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.EtaleStalkSpecialization
public import Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.Paper.StrictHenselizationFunctoriality
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit
import Sheaf.AlgebraicGeometry.GeometricPointPullbackStalk
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion
import Sheaf.Paper.StrictlyHenselianEtaleAcyclic
import Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.AlgebraicGeometry.DerivedExchangeTermwise
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Proper locally acyclic specialization

Source: Stacks Project, Tag 0GJW, lemma-sp-isom-proper-torsion-loc-ac, applied to `G[0]`
(blueprint: lem-weil-pbc-proper-locally-acyclic-specialization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Proper local acyclicity makes specialization on every higher direct-image stalk
invertible for torsion abelian coefficients, without any common annihilator or finite-stalk
hypothesis. Source: Stacks Project, Tag 0GJW, applied to `G[0]`
(blueprint: lem-weil-pbc-proper-locally-acyclic-specialization).

Proof:
1. Form the strict-local base change `f'` and the fibre maps `i,h` as in
`lem-weil-pbc-local-acyclicity-closed-fibre-unit`. Strict henselization functoriality
identifies the closed geometric lift. Properness is preserved by base change. Proper
maps are qcqs, and `h`, a base change of a map between affine schemes, is affine and qcqs.
2. Proper base change (`thm-weil-pbc-bounded-below`) identifies the derived stalks of
`Rf_*G[0]` with the cohomology of the geometric fibres. The Leray identification and
cohomology pullback derived unit, geometric-point pullback/stalk identification, and
exact derived inverse image identify these with the canonical exchange fibre maps.
3. Local acyclicity makes `i⁻¹β` invertible by the closed-fibre unit lemma. Inverse-image
stalk/germ compatibility preserves torsion of `G` under pullback. The qcqs higher-image
prime-torsion theorem, with all primes allowed, makes `Rh_*G_t[0]` bounded below with
torsion cohomology. Stalkwise annihilators give local annihilators by shrinking germs.
4. Apply proper base change to `f'` and this complex. Strictly henselian étale acyclicity
and the sections/stalk isomorphism identify the source with global derived sections.
The termwise derived-exchange formula, underived exchange on section representatives,
and cohomology pullback identify the fibre map with restriction along `i`. Thus restriction,
and hence the cospecialization obtained using inverse Leray and `(i⁻¹β)⁻¹`, are invertible.
5. Specialization/cospecialization compatibility says `cosp ρ_t sp = ρ_s`.
The other three maps are invertible, so specialization is invertible. Apply degree `q`
cohomology. Exact geometric stalks identify it with the displayed higher-direct-image
stalks, and termwise pointed-neighbourhood restriction gives `etaleStalkSpecialization`. -/
theorem isIso_etaleStalkSpecialization_of_proper_locallyAcyclic
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : G.IsTorsion) (hf : IsLocallyAcyclicRelative f G)
    (q : ℕ) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
    IsIso (etaleStalkSpecialization s t
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) := by
  sorry

end AlgebraicGeometry.Etale
