/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap
import Sheaf.Algebra.Homology.RingExtensionFiniteSupportProduct
import Sheaf.Algebra.Homology.RingExtensionInternalHomExt
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit

/-! # Finite-support assembly of normalized tensor-Hom comparisons

Source: Stacks Project, more-algebra.tex, Lemma 0A6A, clause (1),
bounded finite-projective computation.
(blueprint: lem-pc-bounded-ring-hom-extension-degree)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem ringHomComplex_isLimit {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    Nonempty (IsLimit (Fan.mk ((homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n)
      (ringHomComplexProjection P Q n))) :=
  (homComplex_exists (R := CochainComplex.onePointRingSheaf A)).choose_spec.choose_spec.1
    P Q n

set_option backward.isDefEq.respectTransparency true in
/-- In one degree, a normalized Hom comparison is invertible if the source complex has
finite support and the individual module Hom comparisons are invertible. No projectivity
hypothesis or chain-map equation is needed for this finite-product assembly step.

Source: Stacks Project, more-algebra.tex, Lemma 0A6A, clause (1), finite-product
computation (blueprint: lem-pc-bounded-ring-hom-extension-degree).

Proof: choose a,b bounding P. The shared Hom-complex projections are a limiting fan
by homComplex_exists. For p outside [a,b], P^p is zero, hence its internal Hom to
Q^(p+n) is zero; scalar extension preserves zero objects. The infinite product is
therefore canonically the finite product indexed by integers in [a,b]. The same holds
after extension. Scalar extension on this site is ordinary tensor product; it preserves
finite direct sums, and hence finite products, without any flatness assumption. Apply
this finite-product comparison, followed by the product of the given g_p isomorphisms.
The result is an isomorphism k with the displayed source and target. Each projection
of k sends b tensor f, evaluated on c tensor x, to bc tensor f_p(x), by the supplied
normalization of g_p and naturality of the scalar-extension unit. The assumed equation
for t gives the same values. Pure tensors generate scalar extension, pure tensors in
P^p generate its extension, and evaluation on the unique-object slice detects internal
Hom sections. Thus each product projection of t equals that of k. The product universal
property implies t=k, proving its invertibility. If a>b, both products are products of
zero objects and the same argument applies to the empty finite product. The argument
works for arbitrary Q, including unbounded Q, and for non-flat B. -/
theorem boundedRingHom_extension_degree_isIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (hadd : F.Additive) (P Q : CochainComplex (RingSiteModules A) ℤ) (n : ℤ)
    (hb : ∃ a b : ℤ, ∀ p : ℤ, p < a ∨ b < p → IsZero (P.X p))
    (hterms : ∀ p : ℤ,
      ∃ g : F.obj (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
          (P.X p) (Q.X (p + n))) ⟶
        SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf B)
          (F.obj (P.X p)) (F.obj (Q.X (p + n))),
        IsIso g ∧ ∀ (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
          (f : (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
            (P.X p) (Q.X (p + n))).val.obj U) (x : (P.X p).val.obj U),
          ((g.val.app U (ringExtensionPure φ F hF _ U b f)).app
            (op (Over.mk (𝟙 U.unop)))) (ringExtensionPure φ F hF (P.X p) U c x) =
          ringExtensionPure φ F hF (Q.X (p + n)) U (b * c)
            ((f.app (op (Over.mk (𝟙 U.unop)))) x))
    (t : F.obj ((homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n) ⟶
      (homComplex (R := CochainComplex.onePointRingSheaf B)
        ((ringExtensionComplex F hadd).obj P) ((ringExtensionComplex F hadd).obj Q)).X n)
    (ht : ∀ (p : ℤ) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
      (f : (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n |>.val.obj U)
      (x : (P.X p).val.obj U),
      ringHomEvaluate ((ringExtensionComplex F hadd).obj P)
        ((ringExtensionComplex F hadd).obj Q) n p U
        (t.val.app U (ringExtensionPure φ F hF _ U b f))
        (ringExtensionPure φ F hF (P.X p) U c x) =
      ringExtensionPure φ F hF (Q.X (p + n)) U (b * c)
        (ringHomEvaluate P Q n p U f x)) : IsIso t := by
  classical
  let MA (p : ℤ) := SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
    (P.X p) (Q.X (p + n))
  let PA := (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n
  let FP := (ringExtensionComplex F hadd).obj P
  let FQ := (ringExtensionComplex F hadd).obj Q
  let PB := (homComplex (R := CochainComplex.onePointRingSheaf B) FP FQ).X n
  let πA := ringHomComplexProjection P Q n
  let πB : ∀ p : ℤ, PB ⟶ SheafOfModules.homObj
      (R := CochainComplex.onePointRingSheaf B)
      (F.obj (P.X p)) (F.obj (Q.X (p + n))) := ringHomComplexProjection FP FQ n
  obtain ⟨hA⟩ := ringHomComplex_isLimit P Q n
  obtain ⟨hB⟩ := ringHomComplex_isLimit FP FQ n
  have hMA : ∃ a b : ℤ, ∀ p : ℤ, p < a ∨ b < p → IsZero (MA p) := by
    obtain ⟨a, b, hab⟩ := hb
    refine ⟨a, b, fun p hp ↦ ?_⟩
    rw [IsZero.iff_id_eq_zero]
    rw [← SheafOfModules.homObjMap_id (R := CochainComplex.onePointRingSheaf A)]
    rw [(hab p hp).eq_of_src (𝟙 (P.X p)) 0]
    exact SheafOfModules.hom_ext (PresheafOfModules.homObjMap_zero_left (𝟙 _))
  obtain ⟨ρ, ⟨hρ⟩, hρpure⟩ :=
    ringExtension_finiteSupport_product φ F hF MA PA πA hA hMA
  choose g hg hgpure using hterms
  let e (p : ℤ) := by
    have : IsIso (g p) := hg p
    exact asIso (g p)
  let k : F.obj PA ⟶ PB := Fan.IsLimit.lift hB (fun p ↦ ρ p ≫ g p)
  let l : PB ⟶ F.obj PA := Fan.IsLimit.lift hρ (fun p ↦ πB p ≫ (e p).inv)
  have hk (p : ℤ) : k ≫ πB p = ρ p ≫ g p := Fan.IsLimit.fac hB _ p
  have hl (p : ℤ) : l ≫ ρ p = πB p ≫ (e p).inv := Fan.IsLimit.fac hρ _ p
  have hkl : k ≫ l = 𝟙 _ := by
    apply Fan.IsLimit.hom_ext hρ
    intro p
    change (k ≫ l) ≫ ρ p = 𝟙 _ ≫ ρ p
    rw [Category.assoc, hl, ← Category.assoc, hk, Category.assoc]
    change ρ p ≫ (e p).hom ≫ (e p).inv = _
    simp
  have hlk : l ≫ k = 𝟙 _ := by
    apply Fan.IsLimit.hom_ext hB
    intro p
    change (l ≫ k) ≫ πB p = 𝟙 _ ≫ πB p
    rw [Category.assoc, hk, ← Category.assoc, hl, Category.assoc]
    change πB p ≫ (e p).inv ≫ (e p).hom = _
    simp
  have : IsIso k := ⟨⟨l, hkl, hlk⟩⟩
  have htk : t = k := by
    apply Fan.IsLimit.hom_ext hB
    intro p
    apply ringExtension_internalHom_ext φ F hF PA (P.X p) (F.obj (Q.X (p + n)))
    intro U b c f x
    change ringHomEvaluate FP FQ n p U
      (t.val.app U (ringExtensionPure φ F hF PA U b f))
      (ringExtensionPure φ F hF (P.X p) U c x) = _
    rw [ht]
    change _ = (((k ≫ πB p).val.app U
      (ringExtensionPure φ F hF PA U b f)).app
      (op (Over.mk (𝟙 U.unop)))) (ringExtensionPure φ F hF (P.X p) U c x)
    rw [hk]
    change _ = ((g p).val.app U
      ((ρ p).val.app U (ringExtensionPure φ F hF PA U b f))).app
      (op (Over.mk (𝟙 U.unop))) (ringExtensionPure φ F hF (P.X p) U c x)
    rw [hρpure, hgpure]
    rfl
  rw [htk]
  infer_instance

end CategoryTheory
