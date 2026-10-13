/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap

/-! # Termwise finite-projective tensor-Hom comparison

Source: Stacks Project, more-algebra.tex, Lemma 0A6A, clause (1),
bounded finite-projective computation.
(blueprint: lem-pc-finite-projective-ring-hom-extension)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Scalar extension of internal Hom from one finite projective module has a normalized
isomorphism. This is a statement about modules, with no complex or boundedness hypothesis.

Source: Stacks Project, more-algebra.tex, Lemma 0A6A, clause (1), finite-projective
computation (blueprint: lem-pc-finite-projective-ring-hom-extension).

Proof: on the bottom-topology one-object site, every presheaf is a sheaf, so the
sheafification unit is an isomorphism. The slice over the unique object has a unique
object and arrow; restriction and evaluation identify its module morphisms with ordinary
A-linear maps. Under these identifications scalar extension is B tensor_A -, and
internal Hom is ordinary module Hom. First take M=A^r, with r finite. Hom(A^r,N)=N^r,
and scalar extension commutes with this finite product (a finite direct sum), so the
comparison is invertible. Its coordinate formula is b tensor f, applied to c tensor x,
equal to bc tensor f(x). For general finite projective M, take a finite generating
surjection A^r -> M and split it by projectivity. Applying scalar extension and the
contravariant Hom functors preserves the retraction. Naturality of the free comparison
restricts it and its inverse to the retracts. This gives the required isomorphism and
the same pure-tensor formula. Transport it along F's given object equalities and the
bottom-topology sheafification units. Every object U of this site is the unique object,
so the transported formula holds for every U. Neither B-flatness nor any finiteness of
N is used. The zero module and the zero ring give the corresponding zero-object
isomorphisms by the same construction. -/
theorem finiteProjectiveRingHom_extension_exists
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M N : RingSiteModules A)
    (hp : Module.Projective A (M.val.obj (op ⟨PUnit.unit⟩)))
    (hf : Module.Finite A (M.val.obj (op ⟨PUnit.unit⟩))) :
    ∃ g : F.obj (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N) ⟶
        SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf B) (F.obj M) (F.obj N),
      IsIso g ∧ ∀ (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
        (f : (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N).val.obj U)
        (x : M.val.obj U),
        ((g.val.app U (ringExtensionPure φ F hF _ U b f)).app
          (op (Over.mk (𝟙 U.unop)))) (ringExtensionPure φ F hF M U c x) =
        ringExtensionPure φ F hF N U (b * c) ((f.app (op (Over.mk (𝟙 U.unop)))) x) := by
  sorry

end CategoryTheory
