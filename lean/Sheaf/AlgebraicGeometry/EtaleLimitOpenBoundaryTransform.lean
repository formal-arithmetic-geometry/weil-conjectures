/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCoconeDegree
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Exact.Basic
import Sheaf.AlgebraicGeometry.EtaleMayerVietoris
import Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial

/-! # Difference and boundary maps on canonical open diagrams

Source: Stacks Project, Tags 0A50 and 09YQ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
set_option linter.unusedVariables false in
/-- Construct the difference and boundary maps, leaving the restriction row supplied.

Source: Stacks Project, Tag 0A50, coefficient-natural long exact sequence;
Tag 09YQ, coherent-system maps.
(blueprint: lem-weil-pbc-etale-limit-open-boundary-transform).

Proof: Use the supplied covering equations at each tail stage and at c.pt.
Inverse image preserves intersections, identifying the intersection with the
supplied intersection open.
Use the
functorial Mayer--Vietoris connecting transformation before evaluating at the
coefficient sheaves, so the same boundary is natural for all transitions and
cone legs. Transport the difference and boundary by eKU, eKV, eKI and eH;
at the bottom transport the boundary by eB.inv. More explicitly, identify the
stage biproduct with the ordinary product by evaluation's biproduct comparison
and biprodIsoProd, then apply the two object isomorphisms. The map a_j is this
identification followed by restriction from U_j to the intersection minus
restriction from V_j, followed by eKI_j.inv. The map b_j is eKI_j.hom followed
by the canonical boundary delta_j followed by eH_j.inv. The bottom a' is the
actual difference of intersection restrictions, and b' is delta_L followed by
eB.inv. The comparisons are all isomorphisms, so images and kernels of these
maps are the images and kernels in the original long exact sequence.
Coefficient naturality and
pullback naturality prove that the stage maps are natural transformations.
The long exact sequence gives exactness of (a,b). For (b,r), the supplied
component formulas hrU and hrV identify the kernel of r with the kernel of
the actual pair of restrictions: the biproduct projections are jointly monic
and eKU,eKV are isomorphisms. The long exact sequence gives that kernel as
the image of b. Transport also gives bottom exactness. Naturality under the
restricted cone projections followed by the coefficient legs proves the two
left squares. For the difference square, postcompose the two factors with
intersection restriction and subtract; h₁U and h₁V replace the product leg by the
two supplied legs. Pullback/coefficient naturality identifies each resulting term
with the intersection leg after the corresponding stage restriction. For the
boundary square, substitute hB and hιI, cancel eH and eKI, and apply the naturality
of the same connecting transformation under the cone projection followed by
(eG_j).inv;L_j. These equations are exactly the two asserted left squares.
This theorem constructs neither r nor a product cocone map and
asserts no right square. The argument also applies to empty or coincident
opens. -/
theorem etale_limit_open_boundary_transform
    (X : Scheme.{u}) (U V : X.Opens)
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (L : Cocone G) (q : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) (q + 1)))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) (q + 1)) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) (q + 1)) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt (q + 1)))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) (q + 1)) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) (q + 1)))
    (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X)
    (hstageCover : ∀ j : Set.Ici i₀,
      tailStageOpen D g₀ U j ⊔ tailStageOpen D g₀ V j = ⊤)
    (hlimitCover : ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U) ⊔
      ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V) = ⊤)
    (KU : ℕ → Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
    (eKU : ∀ n j, (KU n).obj j ≅ AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ U j).ι).obj (F j.val)) n))
    (hKU : ∀ n j k (f : j ⟶ k), (KU n).map f =
      (eKU n j).hom ≫ tailOpenCohomologyMapDegree D g₀ U F φ n f ≫ (eKU n k).inv)
    (ιU : ∀ n, KU n ⟶ (Functor.const (Set.Ici i₀)).obj (AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U).ι).obj L.pt) n)))
    (hιU : ∀ n j, (ιU n).app j =
      (eKU n j).hom ≫ tailOpenCohomologyLegDegree D c g₀ U F G eG L n j)
    (KV : ℕ → Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
    (eKV : ∀ n j, (KV n).obj j ≅ AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ V j).ι).obj (F j.val)) n))
    (hKV : ∀ n j k (f : j ⟶ k), (KV n).map f =
      (eKV n j).hom ≫ tailOpenCohomologyMapDegree D g₀ V F φ n f ≫ (eKV n k).inv)
    (ιV : ∀ n, KV n ⟶ (Functor.const (Set.Ici i₀)).obj (AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V).ι).obj L.pt) n)))
    (hιV : ∀ n j, (ιV n).app j =
      (eKV n j).hom ≫ tailOpenCohomologyLegDegree D c g₀ V F G eG L n j)
    (KI : ℕ → Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
    (eKI : ∀ n j, (KI n).obj j ≅ AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ (U ⊓ V) j).ι).obj (F j.val)) n))
    (hKI : ∀ n j k (f : j ⟶ k), (KI n).map f =
      (eKI n j).hom ≫ tailOpenCohomologyMapDegree D g₀ (U ⊓ V) F φ n f ≫ (eKI n k).inv)
    (ιI : ∀ n, KI n ⟶ (Functor.const (Set.Ici i₀)).obj (AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V)).ι).obj L.pt) n)))
    (hιI : ∀ n j, (ιI n).app j =
      (eKI n j).hom ≫ tailOpenCohomologyLegDegree D c g₀ (U ⊓ V) F G eG L n j)
    (ι₁ : KU q ⊞ KV q ⟶ (Functor.const (Set.Ici i₀)).obj
      (AddCommGrpCat.of
        (Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
          ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U).ι).obj L.pt) q ×
         Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
          ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V).ι).obj L.pt) q)))
    (h₁U : ∀ j, ι₁.app j ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      (biprod.fst : KU q ⊞ KV q ⟶ KU q).app j ≫ (ιU q).app j)
    (h₁V : ∀ j, ι₁.app j ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      (biprod.snd : KU q ⊞ KV q ⟶ KV q).app j ≫ (ιV q).app j)
    (r : ((show Monotone (fun j : Set.Ici i₀ ↦ j.val) from
      fun _ _ h ↦ h).functor) ⋙ H ⟶ KU (q + 1) ⊞ KV (q + 1))
    (hrU : ∀ j, r.app j ≫ (biprod.fst : KU (q + 1) ⊞ KV (q + 1) ⟶
      KU (q + 1)).app j ≫ (eKU (q + 1) j).hom =
      (eH j.val).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap (tailStageOpen D g₀ U j).ι (F j.val) (q + 1)))
    (hrV : ∀ j, r.app j ≫ (biprod.snd : KU (q + 1) ⊞ KV (q + 1) ⟶
      KV (q + 1)).app j ≫ (eKV (q + 1) j).hom =
      (eH j.val).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap (tailStageOpen D g₀ V j).ι (F j.val) (q + 1)))
 :
    let t : Set.Ici i₀ ⥤ I :=
      (show Monotone (fun j : Set.Ici i₀ ↦ j.val) from fun _ _ h ↦ h).functor
    let WU := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U
    let WV := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V
    let WI := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V)
    let BI := AddCommGrpCat.of
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WI.ι).obj L.pt) q)
    let BP := fun n ↦ AddCommGrpCat.of
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WU.ι).obj L.pt) n ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WV.ι).obj L.pt) n)
    ∃ (a : KU q ⊞ KV q ⟶ KI q) (b : KI q ⟶ t ⋙ H)
      (a' : BP q ⟶ BI) (b' : BI ⟶ B.pt),
      (∀ j, Function.Exact (a.app j) (b.app j)) ∧
      (∀ j, Function.Exact (b.app j) (r.app j)) ∧ Function.Exact a' b' ∧
      (∀ j, a.app j ≫ (ιI q).app j = ι₁.app j ≫ a') ∧
      (∀ j, b.app j ≫ B.ι.app j.val = (ιI q).app j ≫ b') := by sorry

end AlgebraicGeometry.Etale
