module

public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.FlatQuasiFiniteStratification
import Sheaf.AlgebraicGeometry.HasUniversallyBoundedFibersOfIsLocallyQuasiFinite

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A flat locally finitely presented separated quasi-finite morphism over a qcqs scheme
admits a finite constructible locally closed stratification on whose strata it is finite.
This packages the construction from the closed degree filtration, including the induced
subscheme structures. Source: More on Morphisms, Lemma Tag 07RZ.
(blueprint: lem-weil-pbc-etale-separated-stratified-finite-intermediate)
-/
theorem exists_constructible_stratified_finite
    {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [Flat j] [LocallyOfFinitePresentation j] [IsSeparated j]
    (hj : j.IsQuasiFinite) :
    ∃ S : LocallyClosedStratification X,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      (∀ i : Fin S.n, IsFinite (pullback.snd j (S.immersion i))) := by
  sorry

end AlgebraicGeometry.Scheme
