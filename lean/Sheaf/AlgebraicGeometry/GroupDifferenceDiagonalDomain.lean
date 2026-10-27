/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.AlgebraicGeometry.FpqcMorphismsDescend

/-!
# The diagonal extension criterion for a group difference map

Source: Milne, Abelian Varieties, Chapter I, Lemma 3.3, printed p.17, first paragraph
(blueprint: lem-sfb-group-difference-diagonal-domain).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The actual difference morphism on an open of the product lying over `U` in both factors.
Source: Milne, Abelian Varieties I, Lemma 3.3, p.17, displayed multiplication/inverse formula
(blueprint: lem-sfb-group-difference-diagonal-domain).
The two restrictions are composed with `f`, the second with inversion, and the resulting
map into the fibre product of `G` with itself is composed with multiplication. -/
noncomputable def groupDifferenceOnOpen
    {k : Type u} [Field k] (X G : Over (Spec (.of k))) [GrpObj G]
    (U : X.left.Opens) (f : U.toScheme ⟶ G.left)
    (hf : f ≫ G.hom = U.ι ≫ X.hom)
    (H : (pullback X.hom X.hom).Opens)
    (h₁ : H ≤ (pullback.fst X.hom X.hom) ⁻¹ᵁ U)
    (h₂ : H ≤ (pullback.snd X.hom X.hom) ⁻¹ᵁ U) : H.toScheme ⟶ G.left :=
  pullback.lift
    ((pullback.fst X.hom X.hom).resLE U H h₁ ≫ f)
    ((pullback.snd X.hom X.hom).resLE U H h₂ ≫ f ≫ (GrpObj.inv (X := G)).left)
    (by
      simp only [Category.assoc, Over.w, hf, Scheme.Hom.resLE_comp_ι_assoc]
      rw [pullback.condition]) ≫ (MonObj.mul (X := G)).left

/-- The diagonal pulls back the maximal difference-extension domain to the maximal
extension domain of `f`, and the glued difference map is the identity along this diagonal.
Source: Milne, Abelian Varieties I, Lemma 3.3, printed p.17, first paragraph
(blueprint: lem-sfb-group-difference-diagonal-domain).

Here `H`, `φ`, `D`, and `B` are specified by their actual defining equations. Opens `N`
are represented in the ambient fibre product, with `N ≤ Ω`; this is exactly the lattice
of open subschemes of `Ω`. Compatibility is equality of scheme morphisms on intersections.
The existential equality `hδ` supplies the canonical restricted diagonal, without choosing
any additional map. The local compatibility quantifies over every extension morphism.
The `↔` clause says that `b` is the unique `k`-morphism compatible with every extension;
the diagonal value is a separate property of this unique `b`.

Proof following the eight steps of the node:
1. Finite type over the Noetherian field spectrum makes X Noetherian
   (lem-weil-pbc-finite-type-over-noetherian), so U is quasi-compact. Integral implies
   reduced, and lemma-nagata-reduced-dense-image-schematic makes U schematically dense.
   Restriction and transitivity preserve injectivity of the maps on structure sheaves
   (def-nagata-scheme-theoretically-dense-open).
2. Open restriction and composition preserve smoothness
   (lem-pc-open-immersion-smooth-composition). Smooth maps are flat and locally finitely
   presented (lem-pc-smooth-flat). The two projections are flat base changes
   (lem-weil-pbc-flat-morphism-base-change). Twice applying
   lemma-nagata-dense-flat-pullback proves schematic density of U × U in X × X and hence
   of N ∩ H in every N in Ω. The target is absolutely separated by composition with the
   separated field spectrum (lem-weil-pbc-proper-fp-permanence).
3. The extensions agree on overlaps by lem-chow-agree-on-dense-open. Glue their continuous
   maps and structure-sheaf homomorphisms to obtain b; its local-ring and base conditions
   are local. The same cover proves uniqueness, and H itself gives b restricted to H = φ.
4. On Ω ∩ (V × V), an extension F on V gives the group difference F(x)F(y)⁻¹
   (def-sc-group-scheme). Its diagonal pullback is e. This proves D is contained in the
   inverse image of B, together with the diagonal value locally on D.
5. If the diagonal point of x is in an extension open N, put T = N ∩ (X × U).
   The residue-field extension is flat (lem-weil-field-scalar-extension-exact), as is its
   base change (lem-weil-pbc-flat-morphism-base-change). By
   lemma-nagata-dense-flat-pullback the dense U over this residue field meets the nonempty
   open N_x. Thus x lies in W = image(T → X), which is open because the projection is
   flat locally finitely presented (lem-weil-pbc-flat-lfp-open).
6. T → W is a singleton fpqc covering (def-weil-pbc-fpqc-covering): images of affine
   opens are open (lem-weil-pbc-flat-lfp-open), and finitely many cover each affine open
   of W. The morphism a = c(x,y)f(y) equals f after pullback over U by the group identities
   (def-sc-group-scheme); commutativity is unnecessary.
7. T ×_W T → W is flat by base change and composition
   (lem-weil-pbc-flat-morphism-base-change, lem-pc-flat-compose). Flat density
   (lemma-nagata-dense-flat-pullback) and lem-chow-agree-on-dense-open identify the two
   pullbacks of a. Apply lem-galois-fpqc-morphisms-descend to obtain an extension on W;
   its uniqueness identifies it with f over W ∩ U. Thus x is in D, proving the reverse
   inclusion for every scheme point.
8. The two inclusions give the open equality. On each extension open V of D, b agrees
   with the group difference from step 4, hence its diagonal restriction is e. These V
   cover D, giving the asserted morphism equality. No rational point or geometric
   integrality assumption was used. -/
theorem group_difference_diagonal_domain
    (k : Type u) [Field k]
    (X : Over (Spec (.of k))) [IsIntegral X.left]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [Smooth X.hom]
    (G : Over (Spec (.of k))) [GrpObj G] [Smooth G.hom] [ConnectedSpace G.left]
    [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (U : X.left.Opens) (hU : Dense (U : Set X.left))
    (f : U.toScheme ⟶ G.left) (hf : f ≫ G.hom = U.ι ≫ X.hom)
    (Ω H : (pullback X.hom X.hom).Opens)
    (hΩ : (pullback.diagonal X.hom) ⁻¹ᵁ Ω = ⊤)
    (hH : H = Ω ⊓ (pullback.fst X.hom X.hom) ⁻¹ᵁ U ⊓
      (pullback.snd X.hom X.hom) ⁻¹ᵁ U)
    (φ : H.toScheme ⟶ G.left)
    (hφ : φ = groupDifferenceOnOpen X G U f hf H
      (hH.le.trans (inf_le_left.trans inf_le_right)) (hH.le.trans inf_le_right))
    (D : X.left.Opens)
    (hD : D = sSup {V : X.left.Opens | ∃ F : V.toScheme ⟶ G.left,
      F ≫ G.hom = V.ι ≫ X.hom ∧
      X.left.homOfLE (inf_le_left : V ⊓ U ≤ V) ≫ F =
        X.left.homOfLE (inf_le_right : V ⊓ U ≤ U) ≫ f})
    (B : (pullback X.hom X.hom).Opens)
    (hB : B = sSup {N : (pullback X.hom X.hom).Opens | N ≤ Ω ∧
      ∃ c : N.toScheme ⟶ G.left,
        c ≫ G.hom = N.ι ≫ pullback.fst X.hom X.hom ≫ X.hom ∧
        (pullback X.hom X.hom).homOfLE (inf_le_left : N ⊓ H ≤ N) ≫ c =
          (pullback X.hom X.hom).homOfLE (inf_le_right : N ⊓ H ≤ H) ≫ φ}) :
    ∃ hδ : (pullback.diagonal X.hom) ⁻¹ᵁ B = D,
      ∃ b : B.toScheme ⟶ G.left,
        (∀ b' : B.toScheme ⟶ G.left,
          ((b' ≫ G.hom = B.ι ≫ pullback.fst X.hom X.hom ≫ X.hom) ∧
            (∀ (N : (pullback X.hom X.hom).Opens) (hNB : N ≤ B)
              (c : N.toScheme ⟶ G.left),
              c ≫ G.hom = N.ι ≫ pullback.fst X.hom X.hom ≫ X.hom →
              (pullback X.hom X.hom).homOfLE (inf_le_left : N ⊓ H ≤ N) ≫ c =
                (pullback X.hom X.hom).homOfLE (inf_le_right : N ⊓ H ≤ H) ≫ φ →
              (pullback X.hom X.hom).homOfLE hNB ≫ b' = c)) ↔ b' = b) ∧
        (pullback.diagonal X.hom).resLE B D (le_of_eq hδ.symm) ≫ b =
          D.ι ≫ X.hom ≫ (MonObj.one (X := G)).left := by
  sorry

end AlgebraicGeometry
