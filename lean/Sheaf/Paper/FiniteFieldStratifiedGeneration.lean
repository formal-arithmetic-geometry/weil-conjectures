/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.SixFunctors.FlatModelGeneration
public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.CategoryTheory.GrothendieckSheafification
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.TruncationTriangle

/-!
# Finite stratified generation over a finite field

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemmas 6.3.3 and 6.3.9,
and the devissage in Lemma 6.7.13 (blueprint: lem-sfb-finite-field-stratified-generation).

The construction is recorded as a finite list. Its first object is zero, its last object
is isomorphic to the input, and each intervening object is either an allowed generator,
a shift of an earlier object, or a middle-term extension of two earlier objects.
Thus the formula explicitly records both finiteness and the permitted operations.
The coefficient and module categories are ordinary, uncompleted constant-ring modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- A bounded constructible complex over a finite field admits a finite construction from
locally closed extensions of locally constant finite-dimensional module sheaves. The
indices in each shift or triangle step refer only to earlier entries of the finite list.
The generator uses the canonical open immersion into the scheme-theoretic image followed
by the closed immersion, as in `flatModelProEtaleExtension`. Local finite-dimensionality
is expressed by the recorded local-model predicate with `Module.Finite` over the lifted
field; this is precisely finite-dimensionality, with no extra stalk or origin assumption.

Source: Bhatt--Scholze, Lemmas 6.3.3 and 6.3.9, finite devissage in Lemma 6.7.13
(blueprint: lem-sfb-finite-field-stratified-generation).

Proof plan. On the small-site skeleton apply `SheafOfModules.isFlat_constantFieldModule`
to each cohomology sheaf. Ordinary abelian sheafification and the locally bijective
criterion supply its site hypotheses. The coefficient ring is exactly the sheafification
of the constant field, so every such module sheaf is flat.

Apply clauses (1) and (2) of `det-sf-flat-model-generation` to a constructible sheaf F.
They give a finite ordered locally closed stratification with locally constant finite
projective restrictions and a finite filtration of F by the canonical g_* j_! extensions.
The strata are constructible because X is Noetherian; finite projective modules over A
are finite-dimensional. Each short exact sequence of this filtration gives the
single-object distinguished triangle by `ShortComplex.ShortExact.singleTriangle_distinguished`.
Beginning with zero and concatenating these middle-term extensions constructs F[0].

Choose the bounds a and b of P. Good truncation gives an acyclic truncation below a,
which is zero in the derived category, and identifies the truncation at b with P.
For each q from a to b the truncation triangle has first term tau_le(q-1) P,
middle term tau_le(q) P and third term H^q(P)[-q]. Construct H^q(P)[0] by the previous
paragraph and shift by -q. Append the corresponding middle-term extension. Finite
induction through this interval constructs P. Concatenating the finite lists for its
finitely many cohomology sheaves gives the displayed list; transport the endpoints
along the truncation isomorphisms. For acyclic P, including the empty scheme, take the
list consisting solely of a zero object. -/
theorem finiteField_stratifiedGeneration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type u) [Field A] [Finite A]
    (P : proEtaleDerivedCategory X A)
    (_hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((@_root_.DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
        (proEtaleRingModules X (proEtaleConstantRing X A)) _
        (@SheafOfModules.instAbelian _ _ _ _
          (WeilConjectures.integralCoefficientAbSheafify.{u, u + 1} X)
          (WeilConjectures.integralCoefficientAbLocallyBijective.{u, u + 1} X)) _ q).obj P))
    (_hconstructible : ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((@_root_.DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
        (proEtaleRingModules X (proEtaleConstantRing X A)) _
        (@SheafOfModules.instAbelian _ _ _ _
          (WeilConjectures.integralCoefficientAbSheafify.{u, u + 1} X)
          (WeilConjectures.integralCoefficientAbLocallyBijective.{u, u + 1} X)) _ q).obj P)) :
    ∃ (n : ℕ) (K : Fin (n + 1) → proEtaleDerivedCategory X A),
      IsZero (K 0) ∧ Nonempty (K (Fin.last n) ≅ P) ∧
      ∀ i : Fin n,
        (∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
          (L : proEtaleRingModules S (proEtaleConstantRing S A)),
          Topology.IsConstructible (Set.range a.base) ∧
          IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
            (fun M ↦ Module.Finite (ULift.{u + 1, u} A) M) L ∧
          Nonempty (K i.succ ≅ (@_root_.DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2}
            (proEtaleRingModules X (proEtaleConstantRing X A)) _
            (@SheafOfModules.instAbelian _ _ _ _
              (WeilConjectures.integralCoefficientAbSheafify.{u, u + 1} X)
              (WeilConjectures.integralCoefficientAbLocallyBijective.{u, u + 1} X)) _ 0).obj
            ((flatModelProEtaleExtension A a ha).obj L))) ∨
        (∃ (k : Fin (n + 1)) (m : ℤ), k.val ≤ i.val ∧
          Nonempty (K i.succ ≅ (K k)⟦m⟧)) ∨
        (∃ k l : Fin (n + 1), k.val ≤ i.val ∧ l.val ≤ i.val ∧
          ∃ (f : K k ⟶ K i.succ) (g : K i.succ ⟶ K l)
            (h : K l ⟶ (K k)⟦(1 : ℤ)⟧),
            Triangle.mk f g h ∈ distTriang (proEtaleDerivedCategory X A)) := by
  sorry

end AlgebraicGeometry
