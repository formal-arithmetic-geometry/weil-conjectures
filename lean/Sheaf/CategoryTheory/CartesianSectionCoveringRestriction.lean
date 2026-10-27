module

public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Groupoid

/-! # Restriction of cartesian sections to a locally covering subsieve

Source: Stacks Project, stacks.tex, Tag 02ZN (lemma-stackify), naive proof,
final checks (4) and (8), and less naive proof, morphisms on refinements
(blueprint: lem-sfb-cartesian-section-covering-restriction).

A fibred groupoid with coherent choices of pullback is represented by a pseudofunctor.
We use Mathlib's descent data on the family of all arrows of a sieve to present its
cartesian sections. The comparison between two pullbacks is the composite of their
section comparisons through the object on their common composite arrow. Conversely,
the comparison for an arrow of the section category is obtained by setting one leg
to the identity. The identity, pullback and cocycle laws give the section coherences.
This presentation requires no fibre products and does not require the sieve to cover.
-/

@[expose] public section

set_option autoImplicit false

universe w

open CategoryTheory Opposite

namespace CategoryTheory.Pseudofunctor

/-- The canonical restriction of cartesian sections along an inclusion of sieves,
using the descent-data presentation on all arrows of each sieve. Objects, their
comparison maps and morphisms are restricted by the inclusion of indexing families;
there is no choice of an inverse or of a glued object.

Source: Stacks Project, stacks.tex, Tag 02ZN (lemma-stackify), morphisms on refinements
(blueprint: lem-sfb-cartesian-section-covering-restriction). -/
def sieveSectionRestriction
    {C : Type w} [SmallCategory C]
    (Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w})
    {T : C} {S K : Sieve T} (hKS : K ≤ S) :
    Q.DescentData (fun f : S.arrows.category ↦ f.obj.hom) ⥤
      Q.DescentData (fun f : K.arrows.category ↦ f.obj.hom) where
  obj D :=
    { obj i := D.obj ⟨i.obj, hKS _ i.property⟩
      hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
        D.hom q (i₁ := ⟨i₁.obj, hKS _ i₁.property⟩)
          (i₂ := ⟨i₂.obj, hKS _ i₂.property⟩) f₁ f₂ hf₁ hf₂
      pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
        D.pullHom_hom g q q' hq
          (i₁ := ⟨i₁.obj, hKS _ i₁.property⟩) (i₂ := ⟨i₂.obj, hKS _ i₂.property⟩)
          f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
      hom_self Y q i g hg := D.hom_self q (i := ⟨i.obj, hKS _ i.property⟩) g hg
      hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
        D.hom_comp q (i₁ := ⟨i₁.obj, hKS _ i₁.property⟩)
          (i₂ := ⟨i₂.obj, hKS _ i₂.property⟩) (i₃ := ⟨i₃.obj, hKS _ i₃.property⟩)
          f₁ f₂ f₃ hf₁ hf₂ hf₃ }
  map φ :=
    { hom i := φ.hom ⟨i.obj, hKS _ i.property⟩
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
        φ.comm q (i₁ := ⟨i₁.obj, hKS _ i₁.property⟩)
          (i₂ := ⟨i₂.obj, hKS _ i₂.property⟩) f₁ f₂ hf₁ hf₂ }

/-- Restriction to a subsieve which covers locally over every arrow of the larger
sieve induces a bijection on isomorphisms between cartesian sections of a prestack.
The larger sieve and the subsieve need not cover the base object.

Source: Stacks Project, stacks.tex, Tag 02ZN (lemma-stackify), naive proof,
final checks (4) and (8), and less naive proof, morphisms on refinements
(blueprint: lem-sfb-cartesian-section-covering-restriction).

Proof: (1) Given an isomorphism on K, for f in S conjugate its components on fh in K
by the section comparisons. Section coherence makes these a matching family in the
isomorphism presheaf of x_f and y_f on the sieve f^*K; pseudofunctor comparison
isomorphisms account for the parenthesization of iterated pullbacks.
(2) Since f^*K covers and Q is a prestack, unique amalgamation on the slice over
its domain glues this family to an isomorphism beta_f. The fibre groupoid hypothesis
identifies the morphism presheaf with the isomorphism presheaf.
(3) For h with f in S, beta_f pulled back along h and beta_fh have equal restrictions
on (fh)^*K by the section cocycle identities. Separatedness of the same isomorphism
sheaf makes them equal. Hence the beta_f form a section morphism; their inverses
form its inverse, so it is a section isomorphism.
(4) For f in K, the gluing equation at the identity gives beta_f equal to the given
component, proving surjectivity. Two extensions agree after every h in f^*K, and
sheaf uniqueness makes their f-components equal for every f in S, proving injectivity.
All uses of unique amalgamation are those in def-weil-pbc-topos. -/
theorem bijective_sieveSectionRestriction_mapIso
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    (Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w})
    (hQ : ∀ V : C, IsGroupoid (Q.obj (.mk (op V)))) [Q.IsPrestack J]
    {T : C} (S K : Sieve T) (hKS : K ≤ S)
    (hcover : ∀ (V : C) (f : V ⟶ T), S f → K.pullback f ∈ J V)
    (x y : Q.DescentData (fun f : S.arrows.category ↦ f.obj.hom)) :
    Function.Bijective
      ((sieveSectionRestriction Q hKS).mapIso :
        (x ≅ y) →
          ((sieveSectionRestriction Q hKS).obj x ≅ (sieveSectionRestriction Q hKS).obj y)) := by
  sorry

end CategoryTheory.Pseudofunctor
