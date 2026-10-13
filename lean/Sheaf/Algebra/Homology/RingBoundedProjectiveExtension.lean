/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Module.Projective

/-! # Scalar extension of bounded projective complexes on the one-object site

Source: Stacks Project, more-algebra.tex, Tag 0A6A, proof of
lemma-base-change-RHom; Tag 064K, lemma-derived-tor-quasi-isomorphism.
(blueprint: lem-pc-ring-bounded-projective-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex

/-- A bounded projective complex is K-flat, and scalar extension preserves its
projective terms. There is no finite-generation or flat-ring-map hypothesis.
Source: Stacks Project, more-algebra.tex, proof of lemma-base-change-RHom (Tag 0A6A),
and lemma-derived-tor-quasi-isomorphism (Tag 064K).
(blueprint: lem-pc-ring-bounded-projective-extension).

Proof: on the one-object bottom-topology site, evaluation identifies modules and
internal tensor with ordinary modules and tensor over the constant ring. Every
projective A-module is a retract of a free module and hence flat. The bounded-above
flat-complex theorem, applied through this identification, says that P is K-flat.
For each term choose a free-module retraction. Tensoring its two splitting maps with B
preserves their composite, so the extended term is a retract of a free B-module and
is projective. The specified object equalities identify this tensor extension with F.
These arguments work for infinite-rank projectives, the zero ring, zero terms and an empty
interval; no representative in a derived category is chosen here. -/
theorem ringBoundedProjectiveExtension {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B)
    (F : SheafOfModules.{u} ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (onePointRingSheaf A)) ⥤
      SheafOfModules.{u} ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (onePointRingSheaf B))) [F.Additive]
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings
      (⟨(Functor.const _).map (CommRingCat.ofHom φ)⟩ :
        onePointRingSheaf A ⟶ onePointRingSheaf B) M)
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (onePointRingSheaf A))) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hp : ∀ n : ℤ, Module.Projective A ((P.X n).val.obj (op ⟨PUnit.unit⟩))) :
    P.IsKFlat ∧
      (∀ n : ℤ, Module.Projective B
        ((((F.mapHomologicalComplex (.up ℤ)).obj P).X n).val.obj
          (op ⟨PUnit.unit⟩))) := by
  sorry

end CochainComplex
