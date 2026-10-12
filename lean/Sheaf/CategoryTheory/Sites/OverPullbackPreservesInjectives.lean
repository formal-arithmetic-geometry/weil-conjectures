module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.CategoryTheory.Sites.OverPullbackAdjunctionMono

@[expose] public section

universe u

namespace CategoryTheory

/-- Restriction of abelian sheaves to the localized site preserves injective objects.
Source: Stacks Project, Lemma 03F3 (1), using Lemmas 03DI and 03DJ.
(blueprint: new-over-pullback-preserves-injectives)

Proof: For a sheaf G on the slice, form the presheaf whose sections at V are the
direct sum of G(V → W) over all arrows V → W. A restriction along a : V' → V
sends the summand indexed by φ through G's restriction into the summand a ≫ φ.
Sheafify this presheaf. A morphism from it to a sheaf F amounts, by sheafification
adjunction and the direct-sum universal property, to a compatible family of maps
G(V → W) → F(V), hence to a map G → F restricted to the slice. This constructs
an extension-by-zero left adjoint to overPullback. A monomorphism of slice sheaves
is injective on every section group; direct sums preserve these injections,
including empty sums, and exact abelian sheafification preserves monomorphisms.
Thus this left adjoint preserves monomorphisms. If I is injective and A → B is
a monomorphism on the slice, extend the adjoint of A → I|W across the induced
monomorphism of extensions by zero, using injectivity of I. Taking adjoints back
extends A → I|W across A → B, proving injectivity of I|W. No pullbacks in C or
subcanonical topology are required. -/
theorem overPullback_preservesInjectiveObjects
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    (W : C) [HasSheafify (J.over W) AddCommGrpCat.{u}] :
    (J.overPullback AddCommGrpCat.{u} W).PreservesInjectiveObjects := by
  obtain ⟨L, ⟨hL⟩, hmono⟩ := overPullback_extensionByZero J W
  let _ : L.PreservesMonomorphisms := hmono
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms hL

end CategoryTheory
