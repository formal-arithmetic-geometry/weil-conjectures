/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGluingData

/-! # Global chart adjunction for smooth coefficient towers

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gluing.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The global chart adjunction, before comparison with finite exceptional inverse images.
Source: blueprint det-sp-tower-gluing, Local pairs, Gluing, Uniformity, and
Uniqueness and functoriality (blueprint: lem-sp-tower-global-chart-adjunction).

Proof:
1. Choose the finite admissible coordinate cover. Chart admissibility gives common
cohomology and Tor intervals shifted by -2d, all open geometric properties, and
preservation for the intermediate open and affine operations. Use the given
section-normalized presentations for the ordinary coefficient towers throughout.
2. Construct finite coordinates and the compact-support calculus from the canonical
ordinary inverse image, direct image, and open adjunctions. Transport ordinary
sections to the varying-ring graph model. Its unit and counit are the identity on
sections, and its push comparison is the supplied ordinary evaluation comparison.
Adjunction uniqueness fixes pull, open extension, and etale sum comparisons. The
ordinary graph-extension map and its right-derived unit give EtaleNormalized;
thus no independent scalar automorphism can change the non-open etale counit.
3. Apply the coordinate-adjunction theorem. Retain every witness in its normalized
Construction, with its chart family as the explicit parameter of ConstructionAt.
The counit is the actual etale fibre sum followed by ordered P1 integrations.
For d=0 the projection comparison transports the identity adjunction.
4. For each K induct over the finite cover. Two local representing pairs restrict
to representing pairs on the intersection by binary counit representability.
Transpose their counits to get the unique overlap isomorphism. Binary ctf fibre
descent glues their objects with the same common intervals. Binary counit
representability lifts the compatible local counits and proves the global Hom
bijection by the five lemma. The empty cover gives the zero object and counit.
5. Choose a representing pair for each K. For K -> L define its image by
transposing eps_K followed by K -> L. Injectivity proves identity, composition,
and counit naturality. The transpose of the identity defines the unit; the two
transpose equations prove the triangle identities. This is a choice of objects
determined up to their unique counit-preserving isomorphisms, not a choice of
arbitrary cone data in a definition.
6. Restrict to any further chart. The open adjunction and compact-support
composition make the restricted pair represent the local functor. Transposing
the two counits gives the comparison isomorphism and its stated counit equation.
Collect the common coordinate data and these equations as Charts. No finite
exceptional adjunction, coefficient mate, or reduction equation is asserted here. -/
theorem tower_global_chart_adjunction
    (pchar : ℕ) [Fact pchar.Prime]
    (k : Type u) [Field k] [CharP k pchar] (hne : pchar ≠ l)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (hF : ∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F l E b o q
          (CondensedRing.compactificationOverField f)).obj M.obj)) :
    ∃ G : SpTowerCalculus.C l E b q Y.left ⥤ SpTowerCalculus.C l E b q X.left,
      ∃ adj : support l E b o q (CondensedRing.compactificationOverField f) hF ⊣ G,
        Nonempty (Charts l E b o q k X Y
          ⟨inferInstance, inferInstance, inferInstance⟩ f d
          (CondensedRing.compactificationOverField f) hF G adj) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerGluing
