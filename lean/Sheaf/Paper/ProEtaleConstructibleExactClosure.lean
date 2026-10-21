/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import all Sheaf.Paper.ConstructibleCoefficientSerre

/-!
# Exactness closure of globally constructible pro-etale sheaves

Source: Stacks Project, Tags 09B5, 03RZ and 093U
(blueprint: lem-weil-proetale-constructible-exact-closure).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Constructible module sheaves over a finite ring are closed under kernels,
cokernels and extensions, for the global finite-partition convention.
Source: Stacks Project, Tags 09B5 and 093U, with the common global partition
argument of Tag 03RZ.
(blueprint: lem-weil-proetale-constructible-exact-closure)

Proof: For two constructible sheaves choose the witnessing finite stratifications
and intersect them, retaining the fibre-product scheme structure on each intersection.
The number of strata is the product of two positive integers, hence remains positive,
even for the empty scheme. On each refined stratum the two restrictions remain locally
constant with finite geometric stalks: inverse image commutes with composition and
preserves finite constant local models. To see that a locally constant sheaf with finite
stalks has finite local models, discard empty covering members and choose a geometric
point on each remaining member; the constant-stalk and restriction-stalk identifications
identify its model with a finite stalk of the original sheaf. Conversely every geometric
point lifts to a pro-etale covering member. After base change to its algebraically closed
residue field, weak etaleness makes residue-field extensions separable algebraic, hence
trivial, so the constant-model stalk calculation applies at every point.

A finite coefficient ring is Noetherian, and a finite module is finitely generated.
Transport the site along `AsSmall.down`; its induced topology makes this an equivalence
of sites. The ring obtained by forgetting the constant commutative-ring sheaf and the
constant RingCat sheaf are both sheafifications of the same constant ring presheaf:
their constant-section units are locally bijective. The unique comparison commuting
with those units is therefore an isomorphism. Restriction of scalars along it identifies
the two module categories. Under this equivalence, both constructions of a constant
module are sheafifications of the same constant module presheaf, so the sheafification
universal properties identify them, also after localization. A trivializing covering of
the terminal object pulls back to one on every object; conversely the terminal object is
one of the objects in the generic local definition. Thus finite local models are exactly
the generic finite-type locally constant predicate after the finite-generation comparison
above. These equivalences preserve kernels, cokernels and short exact sequences.

The finite-type locally constant Serre theorem, Stacks Tag 093U(3), now applies on each
stratum. Exact module inverse image identifies restriction of a kernel or cokernel with that of
the restricted map. The Serre theorem makes these restrictions locally constant of finite
type. Their finitely generated models are finite sets, being quotients of finite powers
of the finite ring, so they have finite stalks. The same refined finite stratification
witnesses constructibility of the kernel and cokernel. For a short exact sequence use the
common refinement for its outside terms; exact restriction and extension closure in
Tag 093U(3) give the same conclusion for its middle term. No arbitrary geometric-stalk
conservativity, affine-local-to-global partition assertion or nonzero-ring assumption is
used. -/
theorem constructibleProEtale_exactClosure
    (Y : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    (∀ (F G : proEtaleRingModules Y (proEtaleConstantRing Y A)) (f : F ⟶ G),
      IsConstructibleProEtaleModuleSheaf Y A F →
      IsConstructibleProEtaleModuleSheaf Y A G →
      IsConstructibleProEtaleModuleSheaf Y A (kernel f) ∧
        IsConstructibleProEtaleModuleSheaf Y A (cokernel f)) ∧
    (∀ S : ShortComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)),
      S.ShortExact → IsConstructibleProEtaleModuleSheaf Y A S.X₁ →
      IsConstructibleProEtaleModuleSheaf Y A S.X₃ →
      IsConstructibleProEtaleModuleSheaf Y A S.X₂) := by
  have h (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
      IsConstructibleProEtaleModuleSheaf Y A F ↔
        IsConstructibleProEtaleCoefficientModuleSheaf Y (ULift.{u + 1, u} A) F :=
    (proEtaleModuleRestriction_constructible_iff Y A F).trans
      (CoefficientSerre.coefficient_constructible_iff Y (ULift.{u + 1, u} A) F).symm
  obtain ⟨hkc, hext⟩ := constructibleCoefficient_exactClosure Y (ULift.{u + 1, u} A)
  constructor
  · intro F G f hF hG
    obtain ⟨hk, hc⟩ := hkc F G f ((h F).mp hF) ((h G).mp hG)
    exact ⟨(h _).mpr hk, (h _).mpr hc⟩
  · intro S hS h₁ h₃
    exact (h _).mpr (hext S hS ((h _).mp h₁) ((h _).mp h₃))

end AlgebraicGeometry.Scheme
