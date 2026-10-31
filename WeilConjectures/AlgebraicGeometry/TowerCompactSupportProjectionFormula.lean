/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.TowerCompactSupportProjectionFormulaCore
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import WeilConjectures.AlgebraicGeometry.TowerGeometryAdjunctionEvaluation
import WeilConjectures.AlgebraicGeometry.TowerOpenAdjunctionEvaluation
import WeilConjectures.AlgebraicGeometry.TowerCompactSupportProjectionFormulaBounds
import WeilConjectures.AlgebraicGeometry.TowerCompactSupportProjectionFormulaIsos

/-!
# Tower compact-support projection over an arbitrary standing field

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-integral-adjunction,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraph (3)
(blueprint: lem-sp-tower-compact-support-projection-formula).

The section-site model, its tensor and all geometric operations are the recorded
SpTowerShriek operations. Constructibility is transported from the recorded full
subcategory of the ordinary derived category of coefficient towers. No normalization
or etale-origin witness is imposed. Index n always means positive exponent n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerProjection

open SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The tower projection formula over any field of positive characteristic different
from ell, for constructible finite-Tor towers with uniform bounds. Normalization is
not required. The two bounds put both tensor inputs in D+; the two IsIso clauses
refer to the actual proper and open adjunction transposes above. The final IsIso
clause uses the recorded pullback-composition comparison to identify j^{-1}p^{-1}
with f^{-1}.

The level-evaluation assertion is inherited from Geometry.projectionEvaluation,
Geometry.tensorPullback_eq and the ordinary unit/counit equations of Open, descended
termwise by Open.unit_termwise and Open.counit_termwise. Thus these are the finite
projection maps under the specified tensor and adjunction comparisons, rather than
unspecified levelwise isomorphisms.

Source: blueprint main-20261015, integral direct-image proof, paragraph (3)
(blueprint: lem-sp-tower-compact-support-projection-formula).

Proof:
1. At level n use ell = unit times uniformizer^e to identify the actual quotient
   with A_(E,e(n+1)). The finite-discrete condensed-ring and scheme-ring comparisons,
   followed by the internal-abelian-module equivalence, identify ordinary module
   sheaves with the finite coefficient module objects. The exact derived equivalence
   preserves tensor, constructibility and Tor intervals. Internal-module operations
   transport identifies inverse image, direct image and open extension together
   with their units and counits. The same holds for their derived adjunctions.
   Finite presented modules over a finite ring are exactly finite modules, so the
   recorded intrinsic Dctf tests are precisely the finite-coefficient ones.
2. Choose common cohomological bounds [a,b] for C and Tor bounds [v,w] for B.
   At each level the ringed-site Tor-flat-model lemma represents B by a flat complex
   in [v,w], hence K-flat by the bounded-above-flat K-flat lemma. Pullback preserves
   these flat K-flat complexes. Good truncation represents C in [a,b]; exact j_!
   retains those bounds. A flat-term K-flat resolution of either bounded complex
   computes its derived tensor with that model: the acyclic cone remains acyclic
   under tensor with a K-flat complex. Site-derived-tensor descent identifies this
   with the signed total tensor. It vanishes outside [a+v,b+w]. Exact evaluation and
   levelwise tower kernels and cokernels give both asserted lower bounds. These
   independent flat models test bounds and need not assemble to a strict tower.
3. On simultaneous section models form properMap by the counit transpose and
   openMap by applying Rp_* to the open-unit transpose. Evaluation preserves tensor,
   adjunctions, transposes and composition by semilinear-derived-sections, so these
   evaluate to the specified finite maps. Tower-shriek-levels identifies evaluation
   of F with Rp_*j_! on the bounded-below inputs just obtained. Naturality already
   holds before evaluation by maps_natural.
4. Exact open extension preserves the finite Dctf category. Apply finite proper
   projection to p, j_!C_n and B_n. It makes the evaluated properMap invertible.
   These finite-coefficient results require no algebraic closure or finiteness of k.
5. The finite open projection isomorphism has inverse the open-unit transpose:
   the unit/counit triangle identities identify its adjunct with unit tensor one.
   Its inverse is therefore the evaluated pi_j. Rp_* preserves this isomorphism,
   proving levelwise invertibility of openMap.
6. Joint conservativity in the ordinary unbounded tower derived category makes
   both actual maps invertible. Compose properMap with the inverse of openMap and
   the recorded pullback-composition identification. This is the recorded projection
   arrow, hence invertible. The inverse of a natural isomorphism is natural, giving
   canonicalIso and canonicalIso_natural below. No normalization, compatible finite
   flat resolutions or faithfulness of evaluation is used. -/
theorem tower_compact_support_projection_formula
    (b : Base l E) (o : Operations l E b)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hlp : l ≠ p)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (AX : SpCoefficientTowersAbelian l E X.left)
    (AY : SpCoefficientTowersAbelian l E Y.left)
    (C : D l E X.left) (B : D l E Y.left)
    (_hC : constructibleTor l E b X.left AX C)
    (_hB : constructibleTor l E b Y.left AY B) :
    (∃ m : ℤ, ((tensor l E b X.left).obj
      (C, (pull l E b (o.geometry f.left)).obj B)).IsGE m) ∧
    (∃ m : ℤ, ((tensor l E b c.Z).obj
      ((openD l E b (o.openOp c.i)).obj C,
        (pull l E b (o.geometry c.g)).obj B)).IsGE m) ∧
    IsIso (properMap l E b o c C B) ∧
    IsIso (openMap l E b o c C B) ∧
    IsIso (projection l E b o c C B) := by
  obtain ⟨h₁, h₂⟩ := tower_compact_support_projection_bounds
    l E b o k p _hlp X Y f c AX AY C B _hC _hB
  have hp : IsIso (properMap l E b o c C B) :=
    tower_compact_support_proper_projection_isIso
      l E b o k p _hlp X Y f c AX AY C B _hC _hB
  have ho : IsIso (openMap l E b o c C B) := by
    dsimp only [openMap]
    infer_instance
  refine ⟨h₁, h₂, hp, ho, ?_⟩
  unfold SpTowerShriek.projection
  change IsIso (properMap l E b o c C B ≫ _)
  have : IsIso ((o.openTensor c.i C ((pull l E b (o.geometry c.g)).obj B)).hom) := by
    infer_instance
  have : IsIso ((o.comp c.i c.g).hom.app B) := by
    infer_instance
  have : IsIso ((eqToIso (congrArg (fun h ↦ pull l E b (o.geometry h))
      c.comm.symm)).hom.app B) := by
    infer_instance
  have : IsIso (Prod.mkHom (𝟙 C) ((o.comp c.i c.g).hom.app B ≫
      (eqToIso (congrArg (fun h ↦ pull l E b (o.geometry h)) c.comm.symm)).hom.app B)) := by
    apply (CategoryTheory.isIso_prod_iff _ _).2
    exact ⟨inferInstance, inferInstance⟩
  have : IsIso ((tensor l E b X.left).map
      (Prod.mkHom (𝟙 C) ((o.comp c.i c.g).hom.app B ≫
        (eqToIso (congrArg (fun h ↦ pull l E b (o.geometry h)) c.comm.symm)).hom.app B))) := by
    infer_instance
  have : IsIso ((openD l E b (o.openOp c.i)).map
      ((tensor l E b X.left).map (Prod.mkHom (𝟙 C) ((o.comp c.i c.g).hom.app B ≫
        (eqToIso (congrArg (fun h ↦ pull l E b (o.geometry h)) c.comm.symm)).hom.app B)))) := by
    infer_instance
  have : IsIso ((o.openTensor c.i C ((pull l E b (o.geometry c.g)).obj B)).hom ≫
      (openD l E b (o.openOp c.i)).map ((tensor l E b X.left).map
        (Prod.mkHom (𝟙 C) ((o.comp c.i c.g).hom.app B ≫
          (eqToIso (congrArg (fun h ↦ pull l E b (o.geometry h)) c.comm.symm)).hom.app B)))) := by
    infer_instance
  have : IsIso ((push l E b (o.geometry c.g)).map
      ((o.openTensor c.i C ((pull l E b (o.geometry c.g)).obj B)).hom ≫
        (openD l E b (o.openOp c.i)).map ((tensor l E b X.left).map
          (Prod.mkHom (𝟙 C) ((o.comp c.i c.g).hom.app B ≫
            (eqToIso (congrArg (fun h ↦ pull l E b (o.geometry h))
              c.comm.symm)).hom.app B))))) := by
    infer_instance
  infer_instance

/-- The right side of the projection formula as a bifunctor, with f^{-1} explicit.
Source: blueprint paragraph (3), canonical natural isomorphism
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def target (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ((𝟭 (D l E X)).prod (pull l E b (o.geometry f))) ⋙
    tensor l E b X ⋙ F l E b o c

/-- The canonical projection isomorphism, whose forward map is the specified mate
composite, not an independently selected isomorphism of evaluated towers.
Source: blueprint paragraph (3), final sentence
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def canonicalIso (b : Base l E) (o : Operations l E b)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hlp : l ≠ p)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (AX : SpCoefficientTowersAbelian l E X.left)
    (AY : SpCoefficientTowersAbelian l E Y.left)
    (C : D l E X.left) (B : D l E Y.left)
    (hC : constructibleTor l E b X.left AX C)
    (hB : constructibleTor l E b Y.left AY B) :
    (source l E b o c).obj (C, B) ≅ (target l E b o c).obj (C, B) :=
  letI := (tower_compact_support_projection_formula l E b o k p hlp X Y f c
    AX AY C B hC hB).2.2.2.2
  asIso (projection l E b o c C B)

/-- Naturality of the canonical isomorphism on the two full Dctf subcategories.
Source: blueprint paragraph (3), final sentence
(blueprint: lem-sp-tower-compact-support-projection-formula).
Proof: properMap and openMap are natural by maps_natural. Invert the latter natural
isomorphism, compose, and use naturality of the recorded pullback-composition map.
This identifies the composite with the forward map of canonicalIso, which is
projection by construction. Fullness means the input maps are arbitrary ambient
derived-tower morphisms. -/
theorem canonicalIso_natural (b : Base l E) (o : Operations l E b)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hlp : l ≠ p)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (AX : SpCoefficientTowersAbelian l E X.left)
    (AY : SpCoefficientTowersAbelian l E Y.left)
    {C C' : D l E X.left} {B B' : D l E Y.left}
    (hC : constructibleTor l E b X.left AX C)
    (hB : constructibleTor l E b Y.left AY B)
    (hC' : constructibleTor l E b X.left AX C')
    (hB' : constructibleTor l E b Y.left AY B')
    (a : C ⟶ C') (d : B ⟶ B') :
    (source l E b o c).map (Prod.mkHom a d) ≫
        (canonicalIso l E b o k p hlp X Y f c AX AY C' B' hC' hB').hom =
      (canonicalIso l E b o k p hlp X Y f c AX AY C B hC hB).hom ≫
        (target l E b o c).map (Prod.mkHom a d) := by
  let eta : pull l E b (o.geometry c.g) ⋙ pull l E b (o.geometry c.i) ⟶
      pull l E b (o.geometry f.left) :=
    (o.comp c.i c.g).hom ≫
      (eqToIso (congrArg (fun h ↦ pull l E b (o.geometry h)) c.comm.symm)).hom
  let correction (K : D l E X.left) (L : D l E Y.left) :=
    (F l E b o c).map ((tensor l E b X.left).map (Prod.mkHom (𝟙 K) (eta.app L)))
  have hcor :
      (openSource l E b o c).map (Prod.mkHom a d) ≫ correction C' B' =
        correction C B ≫ (target l E b o c).map (Prod.mkHom a d) := by
    change (F l E b o c).map ((tensor l E b X.left).map
        (Prod.mkHom a ((pull l E b (o.geometry c.i)).map
          ((pull l E b (o.geometry c.g)).map d)))) ≫
        (F l E b o c).map ((tensor l E b X.left).map (Prod.mkHom (𝟙 C') (eta.app B'))) =
      (F l E b o c).map ((tensor l E b X.left).map (Prod.mkHom (𝟙 C) (eta.app B))) ≫
        (F l E b o c).map ((tensor l E b X.left).map
          (Prod.mkHom a ((pull l E b (o.geometry f.left)).map d)))
    simp only [← Functor.map_comp]
    apply congrArg (F l E b o c).map
    apply congrArg (tensor l E b X.left).map
    ext
    · simp
    · simpa using eta.naturality d
  have hn := maps_natural l E b o c a d
  have : IsIso (openMap l E b o c C B) := by
    dsimp only [openMap]
    infer_instance
  have hopen :
      (middle l E b o c).map (Prod.mkHom a d) ≫
          (push l E b (o.geometry c.g)).map
            (o.openTensor c.i C' ((pull l E b (o.geometry c.g)).obj B')).hom =
        (push l E b (o.geometry c.g)).map
            (o.openTensor c.i C ((pull l E b (o.geometry c.g)).obj B)).hom ≫
          (openSource l E b o c).map (Prod.mkHom a d) := by
    apply (cancel_epi (openMap l E b o c C B)).1
    rw [← Category.assoc, ← hn.2, Category.assoc]
    simp only [openMap, Functor.prod_obj, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Iso.map_inv_hom_id_assoc]
    exact Category.comp_id _
  change (source l E b o c).map (Prod.mkHom a d) ≫
      projection l E b o c C' B' =
    projection l E b o c C B ≫ (target l E b o c).map (Prod.mkHom a d)
  simp only [projection, Functor.map_comp]
  change (source l E b o c).map (Prod.mkHom a d) ≫
      (properMap l E b o c C' B' ≫
        ((push l E b (o.geometry c.g)).map
          (o.openTensor c.i C' ((pull l E b (o.geometry c.g)).obj B')).hom ≫
          correction C' B')) =
    (properMap l E b o c C B ≫
        ((push l E b (o.geometry c.g)).map
          (o.openTensor c.i C ((pull l E b (o.geometry c.g)).obj B)).hom ≫
          correction C B)) ≫ (target l E b o c).map (Prod.mkHom a d)
  rw [← Category.assoc, hn.1]
  simp only [Category.assoc]
  rw [← Category.assoc ((middle l E b o c).map (Prod.mkHom a d)), hopen,
    Category.assoc, hcor]

end AlgebraicGeometry.ProEtale.SpTowerProjection
