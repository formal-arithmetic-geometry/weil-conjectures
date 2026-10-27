/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.Sites.FreeModuleSheafConstruction
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal

import Sheaf.CategoryTheory.Sites.FreeModuleUniversalProperty

/-!
# A cokernel of differential relations represents sheaf derivations

Source: Stacks Project, Modules on Sites, Tags 04BL and 04BN,
`equation-define-module-differentials`
(blueprint: lem-trf-sheaf-derivation-relation-representability).

The free sheaves and their generators are the published module-sheafification construction.
The finite direct sum of the three relation modules is realized by their finite product,
with the canonical additive inclusions. Derivations use Mathlib's `Derivation'` on the
underlying module presheaf; its restriction-compatibility is precisely a sheaf map here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe w uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.SheafFreeModule

namespace CategoryTheory.SheafDerivationRelations

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}

/-- The underlying set sheaf of a commutative ring sheaf, without a universe lift.
Source: Stacks 04BL
(blueprint: lem-trf-sheaf-derivation-relation-representability). -/
abbrev ringSets (B : Sheaf J CommRingCat.{w}) : Sheaf J (Type w) :=
  (sheafCompose J (forget CommRingCat.{w})).obj B

/-- The generator section in the existing sheafified free module on `T`.
Source: Stacks 04BL, the notation `[t]`
(blueprint: lem-trf-sheaf-derivation-relation-representability). -/
def bracket (B : Sheaf J CommRingCat.{w}) (T : Sheaf J (Type w))
    (U : Cᵒᵖ) (t : T.obj.obj U) : ((free B).obj T).val.obj U :=
  (generatorRaw B T).hom.app U t

/-- The free module sheaf on the symbols `[b]`.
Source: Stacks 04BL, `equation-define-module-differentials`
(blueprint: lem-trf-sheaf-derivation-relation-representability). -/
abbrev symbols (B : Sheaf J CommRingCat.{w}) := (free B).obj (ringSets B)

/-- The free module sheaf on pairs of local sections of `B`.
Source: Stacks 04BL, `equation-define-module-differentials`
(blueprint: lem-trf-sheaf-derivation-relation-representability). -/
abbrev pairSymbols (B : Sheaf J CommRingCat.{w}) :=
  (free B).obj (ringSets B ⊗ ringSets B)

/-- The three relation summands. In this additive category the finite product, with
inclusions `(id,0)`, `(0,(id,0))`, `(0,(0,id))`, is their finite direct sum.
Source: Stacks 04BL, `equation-define-module-differentials`
(blueprint: lem-trf-sheaf-derivation-relation-representability). -/
abbrev relations (A B : Sheaf J CommRingCat.{w}) :=
  pairSymbols B ⨯ (pairSymbols B ⨯ (free B).obj (ringSets A))

/-- A generator in the additivity summand of the relation source.
Source: Stacks 04BL, first summand of `equation-define-module-differentials`
(blueprint: lem-trf-sheaf-derivation-relation-representability). -/
def addGenerator (A B : Sheaf J CommRingCat.{w}) (U : Cᵒᵖ)
    (a b : B.obj.obj U) : (relations A B).val.obj U :=
  (prod.lift (𝟙 _) 0 : pairSymbols B ⟶ relations A B).val.app U
    (bracket B (ringSets B ⊗ ringSets B) U (a, b))

/-- A generator in the Leibniz summand of the relation source.
Source: Stacks 04BL, second summand of `equation-define-module-differentials`
(blueprint: lem-trf-sheaf-derivation-relation-representability). -/
def mulGenerator (A B : Sheaf J CommRingCat.{w}) (U : Cᵒᵖ)
    (f g : B.obj.obj U) : (relations A B).val.obj U :=
  (prod.lift 0 (prod.lift (𝟙 _) 0) : pairSymbols B ⟶ relations A B).val.app U
    (bracket B (ringSets B ⊗ ringSets B) U (f, g))

/-- A generator in the base-annihilation summand of the relation source.
Source: Stacks 04BL, third summand of `equation-define-module-differentials`
(blueprint: lem-trf-sheaf-derivation-relation-representability). -/
def baseGenerator (A B : Sheaf J CommRingCat.{w}) (U : Cᵒᵖ)
    (h : A.obj.obj U) : (relations A B).val.obj U :=
  (prod.lift 0 (prod.lift 0 (𝟙 _)) :
    (free B).obj (ringSets A) ⟶ relations A B).val.app U
      (bracket B (ringSets A) U h)

/-- Exactly the three generator equations defining the differential relation map.
Source: Stacks 04BL, `equation-define-module-differentials`
(blueprint: lem-trf-sheaf-derivation-relation-representability). -/
def IsRelationMap {A B : Sheaf J CommRingCat.{w}} (ψ : A ⟶ B)
    (r : relations A B ⟶ symbols B) : Prop :=
  (∀ (U : Cᵒᵖ) (a b : B.obj.obj U),
    r.val.app U (addGenerator A B U a b) =
      bracket B (ringSets B) U (a + b) -
        bracket B (ringSets B) U a - bracket B (ringSets B) U b) ∧
  (∀ (U : Cᵒᵖ) (f g : B.obj.obj U),
    r.val.app U (mulGenerator A B U f g) =
      bracket B (ringSets B) U (f * g) -
        g • bracket B (ringSets B) U f - f • bracket B (ringSets B) U g) ∧
  (∀ (U : Cᵒᵖ) (h : A.obj.obj U),
    r.val.app U (baseGenerator A B U h) = bracket B (ringSets B) U (ψ.hom.app U h))

private lemma free_ext (B : Sheaf J CommRingCat.{w}) (T : Sheaf J (Type w))
    {N : ringedSiteModules.{w, w, vC, uC} (ring B)}
    {f g : (free B).obj T ⟶ N}
    (h : ∀ U t, f.val.app U (bracket B T U t) = g.val.app U (bracket B T U t)) :
    f = g := by
  apply (freeModule_restrict_bijective B T N).injective
  apply Sheaf.hom_ext
  ext U t
  exact h U t

private lemma bracket_map (B : Sheaf J CommRingCat.{w}) (T : Sheaf J (Type w))
    {U V : Cᵒᵖ} (f : U ⟶ V) (t : T.obj.obj U) :
    ((free B).obj T).val.map f (bracket B T U t) =
      bracket B T V (T.obj.map f t) := by
  exact (CategoryTheory.congr_fun ((generatorRaw B T).hom.naturality f) t).symm

private lemma extend_bracket (B : Sheaf J CommRingCat.{w}) (T : Sheaf J (Type w))
    (N : ringedSiteModules.{w, w, vC, uC} (ring B))
    (a : T ⟶ (underlyingRaw B).obj N) (U : Cᵒᵖ) (t : T.obj.obj U) :
    (extendGenerators B T N a).val.app U (bracket B T U t) = a.hom.app U t := by
  exact CategoryTheory.congr_fun (NatTrans.congr_app
    (congrArg (fun a ↦ a.hom) ((freeModule_extend_inverse B T N).1 a)) U) t

private lemma product_ext {D : Type*} [Category D] [Preadditive D]
    {X Y Z : D} [HasBinaryProduct X Y] {f g : X ⨯ Y ⟶ Z}
    (h₁ : prod.lift (𝟙 X) 0 ≫ f = prod.lift (𝟙 X) 0 ≫ g)
    (h₂ : prod.lift 0 (𝟙 Y) ≫ f = prod.lift 0 (𝟙 Y) ≫ g) : f = g := by
  have total : prod.fst ≫ prod.lift (𝟙 X) 0 +
      prod.snd ≫ prod.lift 0 (𝟙 Y) = 𝟙 (X ⨯ Y) := by
    apply prod.hom_ext <;> simp [Preadditive.add_comp]
  rw [← Category.id_comp f, ← Category.id_comp g, ← total]
  simp only [Preadditive.add_comp, Category.assoc, h₁, h₂]

private def addAssignment (B : Sheaf J CommRingCat.{w}) :
    ringSets B ⊗ ringSets B ⟶ (underlyingRaw B).obj (symbols B) where
  hom :=
    { app := fun U ↦ ↾fun (p : B.obj.obj U × B.obj.obj U) ↦ bracket B (ringSets B) U (p.1 + p.2) -
        bracket B (ringSets B) U p.1 - bracket B (ringSets B) U p.2
      naturality := by
        intro U V f
        ext p
        change B.obj.obj U × B.obj.obj U at p
        change bracket B (ringSets B) V (B.obj.map f p.1 + B.obj.map f p.2) -
          bracket B (ringSets B) V (B.obj.map f p.1) -
          bracket B (ringSets B) V (B.obj.map f p.2) =
          (symbols B).val.map f (bracket B (ringSets B) U (p.1 + p.2) -
            bracket B (ringSets B) U p.1 - bracket B (ringSets B) U p.2)
        simp only [map_sub, bracket_map]
        exact congrArg (fun (x : B.obj.obj V) ↦ bracket B (ringSets B) V x -
          bracket B (ringSets B) V (B.obj.map f p.1) -
          bracket B (ringSets B) V (B.obj.map f p.2)) (map_add (B.obj.map f).hom p.1 p.2).symm }

private def mulAssignment (B : Sheaf J CommRingCat.{w}) :
    ringSets B ⊗ ringSets B ⟶ (underlyingRaw B).obj (symbols B) where
  hom :=
    { app := fun U ↦ ↾fun (p : B.obj.obj U × B.obj.obj U) ↦ bracket B (ringSets B) U (p.1 * p.2) -
        p.2 • bracket B (ringSets B) U p.1 - p.1 • bracket B (ringSets B) U p.2
      naturality := by
        intro U V f
        ext p
        change B.obj.obj U × B.obj.obj U at p
        change bracket B (ringSets B) V (B.obj.map f p.1 * B.obj.map f p.2) -
          B.obj.map f p.2 • bracket B (ringSets B) V (B.obj.map f p.1) -
          B.obj.map f p.1 • bracket B (ringSets B) V (B.obj.map f p.2) =
          (symbols B).val.map f (bracket B (ringSets B) U (p.1 * p.2) -
            p.2 • bracket B (ringSets B) U p.1 - p.1 • bracket B (ringSets B) U p.2)
        have hs (a b : B.obj.obj U) :
            (symbols B).val.map f (a • bracket B (ringSets B) U b) =
              B.obj.map f a • bracket B (ringSets B) V (B.obj.map f b) := by
          exact ((symbols B).val.map_smul f a _).trans
            (congrArg (fun (x : (symbols B).val.obj V) ↦ B.obj.map f a • x)
              (bracket_map B (ringSets B) f b))
        simp only [map_sub]
        rw [hs, hs]
        simp only [bracket_map]
        exact congrArg (fun (x : B.obj.obj V) ↦ bracket B (ringSets B) V x -
          B.obj.map f p.2 • bracket B (ringSets B) V (B.obj.map f p.1) -
          B.obj.map f p.1 • bracket B (ringSets B) V (B.obj.map f p.2))
          (map_mul (B.obj.map f).hom p.1 p.2).symm }

private def baseAssignment {A B : Sheaf J CommRingCat.{w}} (ψ : A ⟶ B) :
    ringSets A ⟶ (underlyingRaw B).obj (symbols B) where
  hom :=
    { app := fun U ↦ ↾fun a ↦ bracket B (ringSets B) U (ψ.hom.app U a)
      naturality := by
        intro U V f
        ext a
        change bracket B (ringSets B) V (ψ.hom.app V (A.obj.map f a)) =
          (symbols B).val.map f (bracket B (ringSets B) U (ψ.hom.app U a))
        erw [bracket_map]
        exact congrArg (bracket B (ringSets B) V)
          (CategoryTheory.congr_fun (ψ.hom.naturality f) a) }

private lemma relation_ext {A B : Sheaf J CommRingCat.{w}}
    {N : ringedSiteModules.{w, w, vC, uC} (ring B)}
    {f g : relations A B ⟶ N}
    (h₁ : ∀ U a b, f.val.app U (addGenerator A B U a b) =
      g.val.app U (addGenerator A B U a b))
    (h₂ : ∀ U a b, f.val.app U (mulGenerator A B U a b) =
      g.val.app U (mulGenerator A B U a b))
    (h₃ : ∀ U a, f.val.app U (baseGenerator A B U a) =
      g.val.app U (baseGenerator A B U a)) : f = g := by
  apply product_ext
  · apply free_ext B (ringSets B ⊗ ringSets B)
    intro U p
    exact h₁ U p.1 p.2
  · apply product_ext
    · apply free_ext B (ringSets B ⊗ ringSets B)
      intro U p
      have hi : (prod.lift (𝟙 _) 0 : pairSymbols B ⟶
          pairSymbols B ⨯ (free B).obj (ringSets A)) ≫
          (prod.lift 0 (𝟙 _) : _ ⟶ relations A B) =
          prod.lift 0 (prod.lift (𝟙 _) 0) := by
        simp [prod.comp_lift]
      change ((prod.lift (𝟙 _) 0 ≫ prod.lift 0 (𝟙 _)) ≫ f).val.app U _ =
        ((prod.lift (𝟙 _) 0 ≫ prod.lift 0 (𝟙 _)) ≫ g).val.app U _
      rw [hi]
      exact h₂ U p.1 p.2
    · apply free_ext B (ringSets A)
      intro U a
      have hi : (prod.lift 0 (𝟙 _) : (free B).obj (ringSets A) ⟶
          pairSymbols B ⨯ (free B).obj (ringSets A)) ≫
          (prod.lift 0 (𝟙 _) : _ ⟶ relations A B) =
          prod.lift 0 (prod.lift 0 (𝟙 _)) := by
        simp [prod.comp_lift]
      change ((prod.lift 0 (𝟙 _) ≫ prod.lift 0 (𝟙 _)) ≫ f).val.app U _ =
        ((prod.lift 0 (𝟙 _) ≫ prod.lift 0 (𝟙 _)) ≫ g).val.app U _
      rw [hi]
      exact h₃ U a

private lemma relation_exists {A B : Sheaf J CommRingCat.{w}} (ψ : A ⟶ B) :
    ∃! r : relations A B ⟶ symbols B, IsRelationMap ψ r := by
  let a := extendGenerators B _ _ (addAssignment B)
  let m := extendGenerators B _ _ (mulAssignment B)
  let b := extendGenerators B _ _ (baseAssignment ψ)
  let r : relations A B ⟶ symbols B :=
    prod.fst ≫ a + prod.snd ≫ (prod.fst ≫ m + prod.snd ≫ b)
  have ha : prod.lift (𝟙 _) 0 ≫ r = a := by
    simp [r, Preadditive.comp_add]
  have hm : prod.lift 0 (prod.lift (𝟙 _) 0) ≫ r = m := by
    simp [r, Preadditive.comp_add, ← Category.assoc]
  have hb : prod.lift 0 (prod.lift 0 (𝟙 _)) ≫ r = b := by
    simp [r, Preadditive.comp_add, ← Category.assoc]
  have hr : IsRelationMap ψ r := by
    refine ⟨?_, ?_, ?_⟩
    · intro U x y
      change (prod.lift (𝟙 _) 0 ≫ r).val.app U _ = _
      rw [ha]
      exact extend_bracket B _ _ (addAssignment B) U (x, y)
    · intro U x y
      change (prod.lift 0 (prod.lift (𝟙 _) 0) ≫ r).val.app U _ = _
      rw [hm]
      exact extend_bracket B _ _ (mulAssignment B) U (x, y)
    · intro U x
      change (prod.lift 0 (prod.lift 0 (𝟙 _)) ≫ r).val.app U _ = _
      rw [hb]
      exact extend_bracket B _ _ (baseAssignment ψ) U x
  refine ⟨r, hr, ?_⟩
  intro s hs
  exact relation_ext (fun U x y ↦ (hs.1 U x y).trans (hr.1 U x y).symm)
    (fun U x y ↦ (hs.2.1 U x y).trans (hr.2.1 U x y).symm)
    (fun U x ↦ (hs.2.2 U x).trans (hr.2.2 U x).symm)

private lemma kill_apply {A B : Sheaf J CommRingCat.{w}}
    {N : ringedSiteModules.{w, w, vC, uC} (ring B)}
    {r : relations A B ⟶ symbols B} {t : symbols B ⟶ N}
    (ht : r ≫ t = 0) (U : Cᵒᵖ) (x : (relations A B).val.obj U) :
    t.val.app U (r.val.app U x) = 0 := by
  exact congrArg (fun f : relations A B ⟶ N ↦ f.val.app U x) ht

private lemma induced_add {A B : Sheaf J CommRingCat.{w}} {ψ : A ⟶ B}
    {r : relations A B ⟶ symbols B} (hr : IsRelationMap ψ r)
    {N : ringedSiteModules.{w, w, vC, uC} (ring B)}
    (t : symbols B ⟶ N) (ht : r ≫ t = 0) (U : Cᵒᵖ) (a b : B.obj.obj U) :
    t.val.app U (bracket B (ringSets B) U (a + b)) =
      t.val.app U (bracket B (ringSets B) U a) +
      t.val.app U (bracket B (ringSets B) U b) := by
  have h := kill_apply ht U (addGenerator A B U a b)
  rw [hr.1 U a b, map_sub, map_sub] at h
  exact sub_eq_zero.mp ((sub_sub _ _ _).symm.trans h)

private def inducedDerivation {A B : Sheaf J CommRingCat.{w}} {ψ : A ⟶ B}
    {r : relations A B ⟶ symbols B} (hr : IsRelationMap ψ r)
    {N : ringedSiteModules.{w, w, vC, uC} (ring B)}
    (t : symbols B ⟶ N) (ht : r ≫ t = 0) : N.val.Derivation' ψ.hom where
  d := AddMonoidHom.mk' (fun b ↦ t.val.app _ (bracket B (ringSets B) _ b))
    (induced_add hr t ht _)
  d_mul {U} a b := by
    have h := kill_apply ht U (mulGenerator A B U a b)
    rw [hr.2.1 U a b, map_sub, map_sub, map_smul, map_smul] at h
    dsimp only [AddMonoidHom.mk'_apply]
    rw [add_comm]
    exact sub_eq_zero.mp ((sub_sub _ _ _).symm.trans h)
  d_map {U V} f b := by
    change t.val.app V (bracket B (ringSets B) V (B.obj.map f b)) =
      N.val.map f (t.val.app U (bracket B (ringSets B) U b))
    erw [← bracket_map]
    exact PresheafOfModules.naturality_apply t.val f _
  d_app {U} a := by
    change t.val.app U (bracket B (ringSets B) U (ψ.hom.app U a)) = 0
    rw [← hr.2.2 U a]
    exact kill_apply ht U (baseGenerator A B U a)

private def derivationAssignment {A B : Sheaf J CommRingCat.{w}} {ψ : A ⟶ B}
    {N : ringedSiteModules.{w, w, vC, uC} (ring B)} (D : N.val.Derivation' ψ.hom) :
    ringSets B ⟶ (underlyingRaw B).obj N where
  hom :=
    { app := fun _ ↦ ↾fun b ↦ D.d b
      naturality := by
        intro U V f
        ext b
        exact D.d_map f b }

private lemma derivation_extension_kills {A B : Sheaf J CommRingCat.{w}} {ψ : A ⟶ B}
    {r : relations A B ⟶ symbols B} (hr : IsRelationMap ψ r)
    {N : ringedSiteModules.{w, w, vC, uC} (ring B)} (D : N.val.Derivation' ψ.hom) :
    r ≫ extendGenerators B _ N (derivationAssignment D) = 0 := by
  apply relation_ext
  · intro U a b
    change (extendGenerators B _ N (derivationAssignment D)).val.app U
      (r.val.app U _) = 0
    rw [hr.1 U a b, map_sub, map_sub]
    simp only [extend_bracket]
    change D.d (a + b) - D.d a - D.d b = 0
    rw [map_add, add_sub_cancel_left, sub_self]
  · intro U a b
    change (extendGenerators B _ N (derivationAssignment D)).val.app U
      (r.val.app U _) = 0
    rw [hr.2.1 U a b, map_sub, map_sub, map_smul, map_smul]
    simp only [extend_bracket]
    change D.d (a * b) - b • D.d a - a • D.d b = 0
    rw [D.d_mul, add_sub_cancel_right, sub_self]
  · intro U a
    change (extendGenerators B _ N (derivationAssignment D)).val.app U
      (r.val.app U _) = 0
    rw [hr.2.2 U a, extend_bracket]
    exact D.d_app a

private lemma postcomp_comp {A B : Sheaf J CommRingCat.{w}} {ψ : A ⟶ B}
    {M N P : ringedSiteModules.{w, w, vC, uC} (ring B)}
    (d : M.val.Derivation' ψ.hom) (f : M ⟶ N) (g : N ⟶ P) :
    d.postcomp (f ≫ g).val = (d.postcomp f.val).postcomp g.val := by
  rfl

private lemma postcomp_id {A B : Sheaf J CommRingCat.{w}} {ψ : A ⟶ B}
    {M : ringedSiteModules.{w, w, vC, uC} (ring B)} (d : M.val.Derivation' ψ.hom) :
    d.postcomp (𝟙 M : M ⟶ M).val = d := by
  ext U b
  rfl

/-- The relation map exists uniquely, and every one of its cokernels universally
represents sheaf derivations, naturally and with the specified inverse and unique
normalized comparison with every other representing pair.
Source: Stacks 04BL, `equation-define-module-differentials`, and 04BN
(blueprint: lem-trf-sheaf-derivation-relation-representability).

Proof (the node's seven steps):
1. By lem-trf-free-module-sheaf-universal-property, extend the additive, Leibniz
   and base assignments uniquely from their sheaves of generators. Their restrictions
   commute with the formulas by semilinearity and naturality of the generator map.
   Combine the three extensions using the finite direct sum to obtain the unique r.
2. A cokernel q satisfies rq = 0 and uniquely factors every map killing r. Evaluating
   rq on the three generators proves additivity, Leibniz and base-annihilation for
   d(b) = q([b]). Its restriction compatibility follows from that of q and the generators.
3. Extend a derivation D uniquely from the free symbols. Its composite with r kills
   all three sorts of generators, hence is zero by the free-module universal property
   and the direct-sum property. No global generation on sections is asserted.
4. Descend this extension uniquely through q. Its values on [b] are D(b). Conversely,
   the extension of the values of any map out of Q is its composite with q. Cokernel
   uniqueness gives both inverse identities and uniqueness in the displayed formula.
5. Postcomposition by a module map preserves derivations. Associativity proves forward
   naturality, and injectivity of the bijections proves inverse naturality.
6. For another representing pair (M,dM), use the two bijections to obtain maps in both
   directions preserving the derivations. Their composites fix d and dM and are identities
   by injectivity. This gives the unique normalized isomorphism and its generator formula.
7. Transport q across this isomorphism. Maps killing r factor through q and then the
   inverse isomorphism, uniquely; hence q followed by the isomorphism is again a cokernel.
-/
theorem relation_cokernel_represents {A B : Sheaf J CommRingCat.{w}} (ψ : A ⟶ B) :
    (∃! r : relations A B ⟶ symbols B, IsRelationMap ψ r) ∧
    ∀ (r : relations A B ⟶ symbols B), IsRelationMap ψ r →
      ∀ (Q : ringedSiteModules.{w, w, vC, uC} (ring B))
        (q : symbols B ⟶ Q) (hq : r ≫ q = 0),
        IsColimit (CokernelCofork.ofπ q hq) →
        ∃ (d : Q.val.Derivation' ψ.hom)
          (e : ∀ N : ringedSiteModules.{w, w, vC, uC} (ring B),
            (Q ⟶ N) ≃ N.val.Derivation' ψ.hom),
          (∀ (U : Cᵒᵖ) (b : B.obj.obj U),
            d.d b = q.val.app U (bracket B (ringSets B) U b)) ∧
          (∀ (N : ringedSiteModules.{w, w, vC, uC} (ring B)) (α : Q ⟶ N),
            e N α = d.postcomp α.val) ∧
          (∀ (N : ringedSiteModules.{w, w, vC, uC} (ring B))
            (D : N.val.Derivation' ψ.hom),
            (∀ (U : Cᵒᵖ) (b : B.obj.obj U),
              (q ≫ (e N).symm D).val.app U (bracket B (ringSets B) U b) = D.d b) ∧
            ∀ α : Q ⟶ N,
              (∀ (U : Cᵒᵖ) (b : B.obj.obj U),
                (q ≫ α).val.app U (bracket B (ringSets B) U b) = D.d b) →
              α = (e N).symm D) ∧
          (∀ (N N' : ringedSiteModules.{w, w, vC, uC} (ring B))
            (v : N ⟶ N') (α : Q ⟶ N),
            e N' (α ≫ v) = (e N α).postcomp v.val) ∧
          (∀ (N N' : ringedSiteModules.{w, w, vC, uC} (ring B))
            (v : N ⟶ N') (D : N.val.Derivation' ψ.hom),
            (e N).symm D ≫ v = (e N').symm (D.postcomp v.val)) ∧
          (∀ (M : ringedSiteModules.{w, w, vC, uC} (ring B))
            (dM : M.val.Derivation' ψ.hom),
            (∀ N : ringedSiteModules.{w, w, vC, uC} (ring B),
              Function.Bijective (fun α : M ⟶ N ↦ dM.postcomp α.val)) →
            ∃ ε : Q ≅ M,
              d.postcomp ε.hom.val = dM ∧
              (∀ ε' : Q ≅ M, d.postcomp ε'.hom.val = dM → ε' = ε) ∧
              (∀ (U : Cᵒᵖ) (b : B.obj.obj U),
                (q ≫ ε.hom).val.app U (bracket B (ringSets B) U b) = dM.d b) ∧
              ∃ h : r ≫ (q ≫ ε.hom) = 0,
                Nonempty (IsColimit (CokernelCofork.ofπ (q ≫ ε.hom) h))) := by
  classical
  refine ⟨relation_exists ψ, ?_⟩
  intro r hr Q q hq hQ
  let d : Q.val.Derivation' ψ.hom := inducedDerivation hr q hq
  have hd (U : Cᵒᵖ) (b : B.obj.obj U) :
      d.d b = q.val.app U (bracket B (ringSets B) U b) := rfl
  have bij (N : ringedSiteModules.{w, w, vC, uC} (ring B)) :
      Function.Bijective (fun α : Q ⟶ N ↦ d.postcomp α.val) := by
    constructor
    · intro α β h
      apply Cofork.IsColimit.hom_ext hQ
      apply free_ext B (ringSets B)
      intro U b
      exact PresheafOfModules.Derivation.congr_d h b
    · intro D
      let t := extendGenerators B _ N (derivationAssignment D)
      have ht : r ≫ t = 0 := derivation_extension_kills hr D
      obtain ⟨α, hα⟩ := CokernelCofork.IsColimit.desc' hQ t ht
      refine ⟨α, ?_⟩
      ext U b
      change (q ≫ α).val.app U (bracket B (ringSets B) U b) = D.d b
      change q ≫ α = t at hα
      rw [hα]
      exact extend_bracket B _ N (derivationAssignment D) U b
  let e (N : ringedSiteModules.{w, w, vC, uC} (ring B)) :
      (Q ⟶ N) ≃ N.val.Derivation' ψ.hom := Equiv.ofBijective _ (bij N)
  have he (N : ringedSiteModules.{w, w, vC, uC} (ring B)) (α : Q ⟶ N) :
      e N α = d.postcomp α.val := rfl
  have inv_formula (N : ringedSiteModules.{w, w, vC, uC} (ring B))
      (D : N.val.Derivation' ψ.hom) (U : Cᵒᵖ) (b : B.obj.obj U) :
      (q ≫ (e N).symm D).val.app U (bracket B (ringSets B) U b) = D.d b :=
    PresheafOfModules.Derivation.congr_d ((e N).apply_symm_apply D) b
  refine ⟨d, e, hd, he, ?_, ?_, ?_, ?_⟩
  · intro N D
    refine ⟨inv_formula N D, ?_⟩
    intro α hα
    apply (e N).injective
    rw [(e N).apply_symm_apply]
    ext U b
    exact hα U b
  · intro N N' v α
    exact postcomp_comp d α v
  · intro N N' v D
    apply (e N').injective
    rw [(e N').apply_symm_apply, he, postcomp_comp, ← he,
      (e N).apply_symm_apply]
  · intro M dM hM
    let a : Q ⟶ M := (e M).symm dM
    obtain ⟨b, hb⟩ := (hM Q).surjective d
    change dM.postcomp b.val = d at hb
    have ha : d.postcomp a.val = dM := (e M).apply_symm_apply dM
    have hab : a ≫ b = 𝟙 Q := by
      apply (bij Q).injective
      change d.postcomp (a ≫ b).val = d.postcomp (𝟙 Q : Q ⟶ Q).val
      calc
        _ = (d.postcomp a.val).postcomp b.val := postcomp_comp d a b
        _ = d := by rw [ha]; exact hb
        _ = _ := (postcomp_id d).symm
    have hba : b ≫ a = 𝟙 M := by
      apply (hM M).injective
      change dM.postcomp (b ≫ a).val = dM.postcomp (𝟙 M : M ⟶ M).val
      calc
        _ = (dM.postcomp b.val).postcomp a.val := postcomp_comp dM b a
        _ = dM := by rw [hb]; exact ha
        _ = _ := (postcomp_id dM).symm
    let ε : Q ≅ M := ⟨a, b, hab, hba⟩
    refine ⟨ε, ha, ?_, ?_, ?_⟩
    · intro ε' hε'
      apply Iso.ext
      exact (bij M).injective (hε'.trans ha.symm)
    · exact inv_formula M dM
    · have h : r ≫ (q ≫ ε.hom) = 0 := by rw [← Category.assoc, hq, zero_comp]
      refine ⟨h, ⟨?_⟩⟩
      let desc : ∀ {N : ringedSiteModules.{w, w, vC, uC} (ring B)}
          (t : symbols B ⟶ N), r ≫ t = 0 → (M ⟶ N) :=
        fun {_} t ht ↦ ε.inv ≫ (CokernelCofork.IsColimit.desc' hQ t ht).val
      have fac {N : ringedSiteModules.{w, w, vC, uC} (ring B)}
          (t : symbols B ⟶ N) (ht : r ≫ t = 0) :
          (q ≫ ε.hom) ≫ desc t ht = t := by
        simp only [desc, Category.assoc, Iso.hom_inv_id_assoc]
        exact (CokernelCofork.IsColimit.desc' hQ t ht).property
      refine CokernelCofork.IsColimit.ofπ (q ≫ ε.hom) h
        (fun t ht ↦ desc t ht) (fun t ht ↦ fac t ht) ?_
      intro N t ht m hm
      have hm' : ε.hom ≫ m = (CokernelCofork.IsColimit.desc' hQ t ht).val := by
        apply Cofork.IsColimit.hom_ext hQ
        exact (Category.assoc _ _ _).symm.trans
          (hm.trans (CokernelCofork.IsColimit.desc' hQ t ht).property.symm)
      change m = ε.inv ≫ _
      rw [← hm', Iso.inv_hom_id_assoc]

#print axioms relation_cokernel_represents

end CategoryTheory.SheafDerivationRelations
