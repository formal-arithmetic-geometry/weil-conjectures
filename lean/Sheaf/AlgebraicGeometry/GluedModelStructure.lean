/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Sheaf.AlgebraicGeometry.FpqcMorphismsDescend
import Sheaf.AlgebraicGeometry.FpqcOpenSubschemeDescent

/-!
# Descended charts with compatible local maps

Source: Stacks Project, Descent, Tag 0AP4, construction of the descended overlaps.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace CategoryTheory.Over.DescentDatum

/-- Descended local models admit covering open embeddings for which the local maps agree.

Source: Stacks Project, Descent, Tag 0AP4, proof before the final global map is glued.
(blueprint: lem-pd-glued-model-compatible-charts).

Proof: On U_i take the inverse image of U_k under the inclusion into V. The restricted
transports agree with D, and inverse transport shows that this open is invariant under E_i.
The cartesian square identifies U_i with W_i ×_Y X. Its projection q_i is an fpqc cover
by base change of p, and transport invariance identifies E_i with the canonical datum.
Descent of opens (03N0) gives an open W_ik of W_i pulling back to U_i ∩ U_k.
The identity on U_i ∩ U_k is compatible with both restricted data, so full faithfulness
of fpqc descent (02W0) descends it to an isomorphism W_ik ≅ W_ki over Y.
Descend the inverse as well; faithfulness proves the inverse identities and triple cocycle.
Uniqueness of the descended opens identifies the domains on triple intersections.
Glue these schemes and transitions using Scheme.GlueData. Its chart inclusions are open
immersions and jointly surjective. The maps W_i → Y agree on the descended overlaps,
so their multicoequalizer descent defines a map from the glued scheme to Y.
The local composites q_i ≫ j_i agree on U_i ∩ U_k by the gluing relation for W_ik:
both factor through its descended transition. The pullback of the inclusions U_i → V
and U_k → V is precisely this intersection, giving the displayed overlap equation.
No global map from V is constructed here. If I is empty, hcover forces V empty;
the empty gluing and its unique map to Y satisfy the assertions vacuously. -/
theorem exists_glued_model_structure
    {X Y : Scheme.{u}} {p : X ⟶ Y}
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage Y)
    {V : Over X} (D : Over.DescentDatum p V)
    {I : Type u} (U : I → V.left.Opens)
    (hcover : ∀ x : V.left, ∃ i, x ∈ U i)
    (E : ∀ i, Over.DescentDatum p (Over.mk ((U i).ι ≫ V.hom)))
    (hcompat : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ (U i).ι =
        (D.transport f₁ f₂ h (Over.homMk (a.left ≫ (U i).ι)
          (by simpa only [Over.mk_hom, Category.assoc] using Over.w a))).left)
    (W : I → Over Y) (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (hcart : ∀ i, IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hinv : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ q i = a.left ≫ q i) :
    ∃ (W₀ : Over Y) (j : ∀ i, (W i).left ⟶ W₀.left),
      (∀ i, IsOpenImmersion (j i)) ∧
      (∀ w : W₀.left, ∃ i, ∃ z : (W i).left, j i z = w) ∧
      (∀ i, j i ≫ W₀.hom = (W i).hom) ∧
      (∀ i k, pullback.fst (U i).ι (U k).ι ≫ q i ≫ j i =
        pullback.snd (U i).ι (U k).ι ≫ q k ≫ j k) := by sorry

end CategoryTheory.Over.DescentDatum
