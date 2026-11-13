/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import WeilConjectures.AlgebraicGeometry.EtaleSubsheafSupportStalk

/-!
# Subsheaves of the final étale sheaf are open subfunctors

Source: Stacks Project, Étale Cohomology, Tag 04HV, used in Tag 09XM.
-/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Testing the factorization property on the two open immersions proves equality. -/
private theorem unique_open_etale_subsheaf_final_factorization (S : Scheme.{u})
    (H : Sheaf S.smallEtaleTopology (Type (max u v)))
    [Mono (terminal.from H)] {W W' : S.Opens}
    (hW : etaleSubsheafFactorization S H W)
    (hW' : etaleSubsheafFactorization S H W') : W = W' := by
  have hle (A B : S.Opens) (hA : etaleSubsheafFactorization S H A)
      (hB : etaleSubsheafFactorization S H B) : A ≤ B := by
    let U : S.Etale := Etale.mk A.ι
    have hsec : Nonempty (Unique (H.obj.obj (op U))) :=
      (hA U).1.mpr ⟨𝟙 A.toScheme, Category.id_comp _⟩
    obtain ⟨f, hf⟩ := (hB U).1.mp hsec
    intro x hx
    have he := congrArg (fun g : A.toScheme ⟶ S ↦ g ⟨x, hx⟩) hf
    change B.ι (f ⟨x, hx⟩) = x at he
    rw [← he]
    exact (f ⟨x, hx⟩).property
  exact le_antisymm (hle W W' hW hW') (hle W' W hW' hW)

/-- A subsheaf of the final small étale sheaf is represented by a unique open subscheme.
`H` is a subsheaf of the final sheaf `⊤_ _`: the unique morphism `terminal.from H` is a
monomorphism. `Nonempty (Unique A)` means that the set `A` is a singleton.
Source: Stacks Project, Étale Cohomology, Tag 04HV, statement and proof. -/
theorem existsUnique_open_of_etale_subsheaf_final (S : Scheme.{u})
    (H : Sheaf S.smallEtaleTopology (Type (max u v)))
    [Mono (terminal.from H)] :
    ∃! W : S.Opens,
      (∀ U : S.Etale,
        (Nonempty (Unique (H.obj.obj (op U))) ↔
          ∃ f : U.left ⟶ W.toScheme, f ≫ W.ι = U.hom) ∧
        ((¬ ∃ f : U.left ⟶ W.toScheme, f ≫ W.ι = U.hom) →
          IsEmpty (H.obj.obj (op U)))) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S),
        (x default ∈ W ↔ Nonempty ((pointSmallEtale x).sheafFiber.obj H)) ∧
        (Nonempty ((pointSmallEtale x).sheafFiber.obj H) ↔
          Nonempty (Unique ((pointSmallEtale x).sheafFiber.obj H)))) := by
  change ∃! W : S.Opens,
    etaleSubsheafFactorization S H W ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S),
        (x default ∈ W ↔ Nonempty ((pointSmallEtale x).sheafFiber.obj H)) ∧
        (Nonempty ((pointSmallEtale x).sheafFiber.obj H) ↔
          Nonempty (Unique ((pointSmallEtale x).sheafFiber.obj H))))
  obtain ⟨W, hW⟩ := exists_open_etale_subsheaf_final_factorization S H
  refine ⟨W, ⟨hW, etale_subsheaf_final_stalk_criterion S H W hW⟩, ?_⟩
  intro W' hW'
  exact unique_open_etale_subsheaf_final_factorization S H hW'.1 hW


end AlgebraicGeometry.Scheme
