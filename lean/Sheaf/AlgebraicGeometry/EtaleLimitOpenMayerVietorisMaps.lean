/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCoconeDegree
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Exact.Basic
import Sheaf.AlgebraicGeometry.EtaleMayerVietoris
import Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback

/-! # Compatible Mayer--Vietoris maps on canonical open diagrams

Source: Stacks Project, Tags 0A50 and 09YQ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
/-- Canonical restricted diagrams admit the compatible exact successor segment.

Source: Stacks Project, Tag 0A50 (lemma-mayer-vietoris), its coefficient-natural
long exact sequence; Tag 09YQ (theorem-colimit), canonical coherent-system maps.
(blueprint: lem-weil-pbc-etale-limit-open-mayer-vietoris-maps).

Proof: The inverse images of U,V cover each tail stage and the limit, by hcover
and the cone equations. Choose the functorial Mayer--Vietoris sequence, as natural
transformations of derived section functors, before evaluating on coefficients.
Transport its restriction and difference maps to Sheaf.H, and its boundary to
Sheaf.H in the next degree, using the restriction-to-derived-sections comparisons.
Resolution independence identifies the transported pullbacks with cohomologyMap.
Coefficient naturality and pullback naturality of this same sequence make the
stage difference, boundary, and restriction maps natural in the tail index.
Conjugate them by eKU,eKV,eKI and eH. Evaluation of a biproduct is a biproduct;
its identification with the ordinary product transports the two exact stage pairs.
At the limit take the same difference and boundary, conjugating the boundary by
eB.inv. This gives the exact bottom pair. Pair the two supplied canonical cocone
legs to construct ι₁ and ι₄; their two projection equations follow from the
biproduct universal property. Naturality for the restricted projection followed
by the coefficient leg gives the three stage-leg squares. In the middle and
right squares use hB to replace the middle leg by its actual canonical formula.
This uses no compactness, scheme limit, sheaf colimit, certificate, finality,
or equality of maps out of a group colimit. For empty opens zero factors remain;
for coincident opens the sequence has diagonal and difference maps and zero
boundary. The statement concerns existential maps only, not a definition choosing
an arbitrary boundary from an unproved existence assertion. -/
theorem etale_limit_open_mayerVietoris_maps
    (X : Scheme.{u}) (U V : X.Opens)
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
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
    (hcover : g₀ ⁻¹ᵁ (U ⊔ V) = ⊤)
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
    let r' : B.pt ⟶ BP (q + 1) := AddCommGrpCat.ofHom
      (((cohomologyMap WU.ι L.pt (q + 1)).prod
        (cohomologyMap WV.ι L.pt (q + 1))).comp eB.hom.hom)
    ∃ (a : KU q ⊞ KV q ⟶ KI q) (b : KI q ⟶ t ⋙ H)
      (r : t ⋙ H ⟶ KU (q + 1) ⊞ KV (q + 1))
      (a' : BP q ⟶ BI) (b' : BI ⟶ B.pt)
      (ι₁ : KU q ⊞ KV q ⟶ (Functor.const (Set.Ici i₀)).obj (BP q))
      (ι₄ : KU (q + 1) ⊞ KV (q + 1) ⟶
        (Functor.const (Set.Ici i₀)).obj (BP (q + 1))),
      (∀ j, Function.Exact (a.app j) (b.app j)) ∧
      (∀ j, Function.Exact (b.app j) (r.app j)) ∧ Function.Exact a' b' ∧
      (∀ j, a.app j ≫ (ιI q).app j = ι₁.app j ≫ a') ∧
      (∀ j, b.app j ≫ B.ι.app j.val = (ιI q).app j ≫ b') ∧
      (∀ j, r.app j ≫ ι₄.app j = B.ι.app j.val ≫ r') ∧
      (∀ j, ι₁.app j ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
        (biprod.fst : KU q ⊞ KV q ⟶ KU q).app j ≫ (ιU q).app j) ∧
      (∀ j, ι₁.app j ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
        (biprod.snd : KU q ⊞ KV q ⟶ KV q).app j ≫ (ιV q).app j) ∧
      (∀ j, ι₄.app j ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
        (biprod.fst : KU (q + 1) ⊞ KV (q + 1) ⟶ KU (q + 1)).app j ≫ (ιU (q + 1)).app j) ∧
      (∀ j, ι₄.app j ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
        (biprod.snd : KU (q + 1) ⊞ KV (q + 1) ⟶ KV (q + 1)).app j ≫ (ιV (q + 1)).app j) := by sorry

end AlgebraicGeometry.Etale
