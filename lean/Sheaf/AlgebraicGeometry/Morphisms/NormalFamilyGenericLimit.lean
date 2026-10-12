/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# A normal Noetherian family system and its pointed generic fibres

Source: Stacks Project, Tag 0EZJ, limit reduction before descent of the cover.
(blueprint: lem-sbc-normal-family-generic-limit)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Approximate a smooth pointed family, retaining the inverse systems of its generic
fibres and generic base points. No finite cover or group action is involved.

Source: Stacks Project, Tag 0EZJ, proof of Lemma 58.31.9, paragraphs from absolute
Noetherian approximation through the assertion that the generic fibre is a limit.
(blueprint: lem-sbc-normal-family-generic-limit)

Proof:
1. Apply absolute Noetherian approximation to S. Replace each stage by the normalization
   of its integral scheme-theoretic image in that image's own fraction field, embedded
   in the function field of S. This normalization is finite because the image is
   excellent and of finite type over the integers.
   Normality of S factors the projection through this normalization. The resulting
   stages are normal integral finite type integer schemes, the projections are dominant,
   and transition maps exist by the universal property of normalization. They are affine:
   their composites with the finite normalization maps are affine, and an S-morphism
   between affine S-schemes is affine. On affine charts the new coordinate rings lie in
   the corresponding rings of S, contain the old images, and their union is that ring.
   Thus the new system still has limit S.
2. Descend the finitely presented smooth family and its section to a stage. Smoothness
   holds after increasing the stage. Restrict to the open relative component through
   the descended section, whose fibres are geometrically irreducible. The section lies
   in this open. The projection from C factors through it: each geometric fibre of C
   is connected and meets that component at the section point, so its image lies in
   the component. Thus the pullback is all of C. Pass to the cofiltered tail of this
   stage. Descend the inverse of n in the
   global section rings (on a finite affine cover, including agreement on overlaps).
   Every later family is its base change, so the section, smoothness, geometric
   connectedness, and invertibility persist.
3. Dominance embeds each stage function field into the function field of S. On affine
   charts each fraction in the latter uses two elements from a common stage and a
   nonzero denominator. Hence these function fields have filtered colimit S.functionField.
   Their spectra form the inverse system K with the stated limit cone b. Form D from
   the generic fibres of the descended families; cartesian base change commutes with
   limits, so Cη is its limit, using the supplied generic-fibre pullback square.
4. Let e identify K at each stage with the spectrum of the stage function field. Base
   change the descended sections to obtain the natural transformation s. The universal
   properties of these pullbacks give both section equalities and the compatibility
   of the given generic section with the two limit cones. The family projections give
   a, and the generic-fibre projections give κ; their composites with j₀ and j agree.
   Generic fibres are qcqs, being base changes of finitely presented families to fields;
   their transition maps are affine base changes. The spectra of fields are qcqs and
   have affine transition maps. Retain these data as existential witnesses. -/
theorem exists_normal_family_generic_limit {S C : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S) (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ) :
    ∃ (I : Type u) (hcat : SmallCategory I),
      letI : SmallCategory I := hcat
      ∃ (hco : IsCofiltered I) (D K : I ⥤ Scheme.{u})
        (κ : (Functor.const I).obj Cη ⟶ D)
        (b : (Functor.const I).obj (Spec S.functionField) ⟶ K) (s : K ⟶ D),
        ∃ (hκ : IsLimit (Cone.mk Cη κ))
          (hb : IsLimit (Cone.mk (Spec S.functionField) b)),
        (∀ i, CompactSpace (D.obj i)) ∧ (∀ i, QuasiSeparatedSpace (D.obj i)) ∧
        (∀ i, CompactSpace (K.obj i)) ∧ (∀ i, QuasiSeparatedSpace (K.obj i)) ∧
        (∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)) ∧
        (∀ {i j : I} (f : i ⟶ j), IsAffineHom (K.map f)) ∧
        (∀ i, sη ≫ κ.app i = b.app i ≫ s.app i) ∧
        ∃ (S₀ C₀ : I → Scheme.{u}) (hI₀ : ∀ i, IsIntegral (S₀ i)),
          letI : ∀ i, IsIntegral (S₀ i) := hI₀
          ∃ (c₀ : ∀ i, C₀ i ⟶ S₀ i) (σ₀ : ∀ i, S₀ i ⟶ C₀ i)
            (q₀ : ∀ i, D.obj i ⟶ Spec (S₀ i).functionField)
            (j₀ : ∀ i, D.obj i ⟶ C₀ i)
            (e : ∀ i, K.obj i ≅ Spec (S₀ i).functionField) (a : ∀ i, C ⟶ C₀ i),
            ∀ i, IsNoetherian (S₀ i) ∧ QuasiSeparatedSpace (S₀ i) ∧
              (∀ x : S₀ i, IsIntegrallyClosed ((S₀ i).presheaf.stalk x)) ∧
              QuasiCompact (c₀ i) ∧ QuasiSeparated (c₀ i) ∧ Smooth (c₀ i) ∧
              GeometricallyConnected (c₀ i) ∧ σ₀ i ≫ c₀ i = 𝟙 (S₀ i) ∧
              IsUnit (n : Γ(S₀ i, ⊤)) ∧
              IsPullback (q₀ i) (j₀ i) ((S₀ i).fromSpecStalk (genericPoint (S₀ i)))
                (c₀ i) ∧
              (e i).inv ≫ s.app i ≫ q₀ i = 𝟙 _ ∧
              (e i).inv ≫ s.app i ≫ j₀ i =
                (S₀ i).fromSpecStalk (genericPoint (S₀ i)) ≫ σ₀ i ∧
              κ.app i ≫ j₀ i = j ≫ a i := by sorry

end AlgebraicGeometry.Scheme
