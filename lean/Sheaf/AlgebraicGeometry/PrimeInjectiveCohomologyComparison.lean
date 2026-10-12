/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.SixFunctors.BaseChange.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Cohomology comparison from prime-module injective acyclicity

Source: Stacks Project, Tag 095T, the injective-resolution argument in paragraph two.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Degree-zero comparison and acyclicity of restricted injectives imply comparison
for abelian sheaves killed by a prime.

Source: Stacks Project, Tag 095T, second paragraph of the proof, abstracted from
projective lines; the identification with the canonical pullback is the comparison
of resolutions in prop-weil-pbc-p1-strict-henselian-comparison, steps (c)--(d).
(blueprint: lem-weil-pbc-prime-injective-cohomology-comparison)

Proof: the equation r • id G = 0 says sectionwise that every section is killed by r.
Give each section group its canonical Z/r-module structure. Restriction maps respect
integer multiplication and hence these module structures; transport along the ring
isomorphism ULift (ZMod r) ≃+* ZMod r. This gives a module sheaf with underlying
abelian sheaf canonically isomorphic to G. Choose an injective resolution in module
sheaves. Forgetting coefficients is exact, and injective module sheaves are acyclic
for abelian cohomology by Stacks 03FD. Exact inverse image gives a resolution on Y;
hacyclic makes each of its terms acyclic there. Leray's acyclic-resolution theorem
therefore computes both abelian cohomologies with these two section complexes.
hzero makes the restriction map between section complexes an isomorphism in every
degree, so its homology maps are bijective. To identify these maps with cohomologyMap,
compare the module resolution with an injective abelian resolution on X and then
resolve its inverse image on Y. Naturality of restriction gives the commuting square
of section complexes. Both comparison maps induce the acyclic-resolution
isomorphisms; independence of lifts follows from the homotopy uniqueness of maps
into an injective resolution. Thus the map in that square is exactly the canonical
Ext pullback defining cohomologyMap. Transport along the original isomorphism of
underlying abelian sheaves proves the displayed assertion. This includes q = 0,
where the comparison is just hzero, and the zero sheaf. -/
theorem Etale.bijective_cohomologyMap_of_prime_injective_acyclic
    {X Y : Scheme.{u}} (i : Y ⟶ X) (r : ℕ) [Fact r.Prime]
    (hzero : ∀ G : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))),
      IsIso (globalSectionsUpperStarMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) i G))
    (hacyclic : ∀ (J : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective J]
        (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
          AddCommGrpCat.{u + 1})).obj
            ((i)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))].obj J)) q))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : r • 𝟙 G = 0)
    (q : ℕ) : Function.Bijective (Etale.cohomologyMap i G q) := by sorry

end AlgebraicGeometry
