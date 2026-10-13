module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Every positive-degree cocycle on an open of U_i has a sectionwise boundary.

Source: blueprint `lem-pc-cech-resolution`, proof paragraph 1 (insertion homotopy).
(blueprint: lem-pc-cech-local-positive-section-boundary)

Proof: An open W of U_i identifies with an open V of X contained in U_i.
Evaluate the isomorphisms e and their differential compatibility hd on V.
For a Cech cocycle, insert i as the first index to construct its primitive:
the extra intersection with U_i is V itself. The alternating differential
of this primitive is the cocycle, because deletion of the inserted index
contributes the cocycle and all other terms cancel by its cocycle equation.
Transport the primitive back through e in degree p and the restriction
isomorphism on sections. These are additive isomorphisms, so hd transports
the boundary equation. This is an assertion on every open, requiring no
sheafification or reflection of exactness. Empty opens and zero modules
satisfy the same insertion formula.
-/
theorem cech_sheaf_restrict_positive_section_boundary
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (F : X.Modules)
    (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor U).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor U).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).d p (p + 1))
    (i : ι) (p : ℕ) :
    let K := ((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D
    ∀ (W : (U i).toScheme.Opens) (x : Γ((K.sc (p + 1)).X₂, W)),
      (K.sc (p + 1)).g.app W x = 0 →
        ∃ z : Γ((K.sc (p + 1)).X₁, W), (K.sc (p + 1)).f.app W z = x := by
  sorry

end AlgebraicGeometry
