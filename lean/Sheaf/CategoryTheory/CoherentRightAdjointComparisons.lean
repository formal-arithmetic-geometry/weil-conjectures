module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Coherent comparisons of chosen right adjoints

Source: blueprint main-20261015, det-sf-existence-brown, proof (3), final sentence;
Stacks Project, Tags 0037 and 0B65.
(blueprint: lem-sfb-coherent-right-adjoint-comparisons)
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

/-- Chosen adjunctions and coherent left-adjoint comparisons have unique counit-normalized
right-adjoint comparisons, including uniqueness among arbitrary component morphisms.

Source: blueprint main-20261015, det-sf-existence-brown, proof (3), final sentence;
Stacks Project, Tags 0037 and 0B65.
(blueprint: lem-sfb-coherent-right-adjoint-comparisons)

Proof: (1) The natural Hom bijections give the specified adjunctions by
`Adjunction.mkOfHomEquiv` (lem-weil-pbc-adjunction-of-natural-bijection). Their forward
formula is unit followed by the right functor on a morphism; their inverse formula is
the left functor on a morphism followed by the counit. Thus the supplied bijections,
and not arbitrary alternative adjunctions, are used throughout.
(2) Define gamma j i by `conjugateIsoEquiv (a i) (a j) (phi j i).symm`
(def-weil-pbc-adjunction-conjugate). Its component is the j-th Hom transpose of
`(phi j i).inv.app ((G i).obj N)` followed by the i-th counit.
(3) Applying the inverse j-th Hom bijection gives the normalization equation.
Any component morphism satisfying this equation has the same inverse transpose,
so injectivity gives componentwise uniqueness. Extensionality then gives uniqueness
of every normalized family of natural isomorphisms.
(4) Conjugation preserves identities and reverses composition. The assumed identity
and cocycle laws for phi therefore give the identity and cocycle laws for gamma.
The cocycle with first and last indices equal gives the inverse law in both orders.
(5) For h, put b = (a i).homEquiv M N h. The inverse j-th transpose of
`b` followed by gamma is the j-th left functor on that composite followed by its
counit. Use the normalization equation and naturality of the inverse of phi to
rewrite this as the inverse i-th transpose of b preceded by the inverse of phi
at M. This is h preceded by that inverse. Applying the j-th Hom bijection proves
the final compatibility equation. No triangulated or size-generation argument is used.
-/
theorem exists_unique_coherent_right_adjoint_comparisons
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {I : Type w} (F : I → C ⥤ D) (G : I → D ⥤ C)
    (a : ∀ i : I, F i ⊣ G i) (phi : ∀ j i : I, F i ≅ F j)
    (hphi_id : ∀ i : I, phi i i = Iso.refl (F i))
    (hphi_comp : ∀ i j k : I, phi j i ≪≫ phi k j = phi k i) :
    ∃ gamma : ∀ j i : I, G i ≅ G j,
      (∀ (i j : I) (N : D),
        (F j).map ((gamma j i).hom.app N) ≫ (a j).counit.app N =
          (phi j i).inv.app ((G i).obj N) ≫ (a i).counit.app N) ∧
      (∀ gamma' : ∀ j i : I, G i ≅ G j,
        (∀ (i j : I) (N : D),
          (F j).map ((gamma' j i).hom.app N) ≫ (a j).counit.app N =
            (phi j i).inv.app ((G i).obj N) ≫ (a i).counit.app N) →
        gamma' = gamma) ∧
      (∀ (i j : I) (N : D) (b : (G i).obj N ⟶ (G j).obj N),
        (F j).map b ≫ (a j).counit.app N =
            (phi j i).inv.app ((G i).obj N) ≫ (a i).counit.app N →
          b = (gamma j i).hom.app N) ∧
      (∀ i j : I, (gamma j i).hom = conjugateEquiv (a i) (a j) (phi j i).inv) ∧
      (∀ i : I, gamma i i = Iso.refl (G i)) ∧
      (∀ i j k : I, gamma j i ≪≫ gamma k j = gamma k i) ∧
      (∀ i j : I, gamma i j = (gamma j i).symm) ∧
      (∀ (i j : I) (M : C) (N : D) (h : (F i).obj M ⟶ N),
        (a j).homEquiv M N ((phi j i).inv.app M ≫ h) =
          (a i).homEquiv M N h ≫ (gamma j i).hom.app N) := by
  sorry

end CategoryTheory
