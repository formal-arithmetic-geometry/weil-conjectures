/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.PulledKoszulTowerNormalization

/-! # Normalized ordinary pullback of the principal Koszul tower

Source: Stacks Project, sites-modules.tex, Tag 03EL, and sites-cohomology.tex,
Tag 07A4; the scalar and adjacent-transition calculation of steps 2--4 of
lem-a1-pulled-koszul-tower-chain-comparison.
(blueprint: lem-a1-pulled-koszul-tower-normalized-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
open WeilConjectures.PrincipalKoszulStrictReplacement
open WeilConjectures.PulledKoszulTowerModel

namespace WeilConjectures

/-- The ordinary tensor comparison and the action unitor identify the principal
Koszul towers, naturally in every complex, with both basis vectors normalized.
No flatness or quasi-isomorphism assertion is included here.

Source: Stacks Project, sites-modules.tex, Tag 03EL, lemma-tensor-product-pullback;
sites-cohomology.tex, Tag 07A4, lemma-pullback-tensor-product, ordinary constituents;
steps 2--4 of lem-a1-pulled-koszul-tower-chain-comparison.
(blueprint: lem-a1-pulled-koszul-tower-normalized-iso).

Proof:
1. At every finite quotient the completed structural ring map preserves the
residue of the uniformizer, since its finite component is the constant coefficient
map. The projections jointly determine a section of the inverse limit, so it
preserves the completed uniformizer and its powers.
2. The action unitor on ordinary module pullback sends a tensor b to c_g(a)b
and its inverse sends b to 1 tensor b. Apply it to both free terms of the
principal Koszul cone. The equality c_g(t^(n+1)a)b = t^(n+1)c_g(a)b is the chain
map equation. The two action maps and their inverses therefore identify the
pulled Koszul complex with the target Koszul complex.
3. Compose the ordinary cochain tensor comparison with identity tensor this
Koszul isomorphism. On the summand indexed by (p,i), with i = -1 or 0, this
sends ((x tensor e_i) tensor b) to (x tensor b) tensor e'_i. The coefficient
has degree zero and no homogeneous factors are interchanged. The two
contributions to the total differential have the same signs 1 and (-1)^p.
This proves exactly KoszulNormalization for both choices of negative.
4. The adjacent transition is multiplication by t in degree -1 and identity in
 degree 0. Step 1 shows that the action unitor intertwines both maps. Naturality
of the ordinary tensor comparison gives the strict adjacent tower squares;
composition gives every tower square. Assemble the level isomorphisms into a
strict tower isomorphism. Naturality in the other tensor argument gives the
asserted equality for every chain map f, on each level and total summand.
These constructions apply to every unbounded complex: the totalization uses
coproducts and ordinary pullback, a left adjoint, preserves those coproducts.
-/
theorem pulled_koszul_tower_normalized_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{t}} (g : X ⟶ Y) :
    ∃ θ : ∀ P : CochainComplex (CompletedTowerIndependent.Modules l E Y) ℤ,
        (diagramPull l E g).obj (H l E Y P) ≅ H l E X ((G l E g).obj P),
      (∀ P, KoszulNormalization l E g P (θ P)) ∧
      (∀ {P P' : CochainComplex (CompletedTowerIndependent.Modules l E Y) ℤ}
        (f : P ⟶ P'),
        Functor.whiskerRight (sourceTowerMap l E Y f) (G l E g) ≫ (θ P').hom =
          (θ P).hom ≫ sourceTowerMap l E X ((G l E g).map f)) := by sorry

end WeilConjectures
