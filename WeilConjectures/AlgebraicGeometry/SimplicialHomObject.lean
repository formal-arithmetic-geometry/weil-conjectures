/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SimplicialHomObjectExists
public import Mathlib.CategoryTheory.RepresentedBy

/-!
# Degree-zero Hom objects for finite simplicial sets

## References

* [Stacks Project, Tag 017I](https://stacks.math.columbia.edu/tag/017I)
* [Stacks Project, Tag 017J](https://stacks.math.columbia.edu/tag/017J)
* [Stacks Project, Tag 017K](https://stacks.math.columbia.edu/tag/017K)
* [Stacks Project, Tag 001Q](https://stacks.math.columbia.edu/tag/001Q)
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.Scheme

/-- Compatible maps indexed by all simplices. -/
def SimplicialHomFamily {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (S : SSet.{t})
    (W : FormalCoproduct.{w} X.Etale) :=
  {f : ∀ n : ℕ, S.obj (op ⦋n⦌) → (W ⟶ K.obj (op ⦋n⦌)) //
    ∀ (m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) (s : S.obj (op ⦋n⦌)),
      f n s ≫ K.map φ.op = f m (S.map φ.op s)}

/-- Precomposition preserves the compatibility equations. -/
theorem SimplicialHomFamily.precomp_compatible {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S : SSet.{t}}
    {W W' : FormalCoproduct.{w} X.Etale} (f : SimplicialHomFamily K S W) (g : W' ⟶ W) :
    ∀ (m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) (s : S.obj (op ⦋n⦌)),
      (g ≫ f.val n s) ≫ K.map φ.op = g ≫ f.val m (S.map φ.op s) := by
  intro m n φ s
  rw [Category.assoc, f.property m n φ s]

/-- Precomposition of compatible families. -/
def SimplicialHomFamily.precomp {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S : SSet.{t}}
    {W W' : FormalCoproduct.{w} X.Etale} (f : SimplicialHomFamily K S W) (g : W' ⟶ W) :
    SimplicialHomFamily K S W' :=
  ⟨fun n s => g ≫ f.val n s, f.precomp_compatible g⟩

/-- The presheaf `W ↦ {S-families in K over W}` of compatible families, functorial by
precomposition. An object `Hom(S,K)_0` with universal family `u` is a pair `(H, u)` with
`(simplicialHomFamilyFunctor K S).IsRepresentedBy u`;
for `S` with finite nonempty degrees and finitely many nondegenerate simplices such a pair
exists by `exists_simplicial_hom_object`. -/
def simplicialHomFamilyFunctor {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (S : SSet.{t}) :
    (FormalCoproduct.{w} X.Etale)ᵒᵖ ⥤ Type (max u w t) where
  obj W := SimplicialHomFamily K S W.unop
  map g := TypeCat.ofHom (fun f => SimplicialHomFamily.precomp f g.unop)
  map_id W := by
    rfl
  map_comp g h := by
    rfl

/-- Restriction of a family to a simplicial subset. -/
def SimplicialHomFamily.restrict {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S : SSet.{t}}
    {W : FormalCoproduct.{w} X.Etale} (f : SimplicialHomFamily K S W)
    (A : S.Subcomplex) : SimplicialHomFamily K A.toSSet W :=
  ⟨fun n s => f.val n s.val, fun m n φ s => f.property m n φ s.val⟩

/-- The restriction morphism `Hom(S,K)_0 ⟶ Hom(A,K)_0` along a simplicial subset `A ⊆ S`:
for a family `u` over `H` (the universal family of a representing pair for `S`) and a pair
`(H', u')` representing the functor of `A`-families, the unique morphism `ρ : H ⟶ H'` with
`u'_s ∘ ρ = u_s` for all simplices `s` of `A`, i.e. the preimage of `u.restrict A` under the
bijection `g ↦ (u'_s ∘ g)_s` of `Functor.IsRepresentedBy`. -/
noncomputable def simplicialHomRestriction {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S : SSet.{t}}
    (A : S.Subcomplex) {H H' : FormalCoproduct.{w} X.Etale}
    (u : SimplicialHomFamily K S H) {u' : SimplicialHomFamily K A.toSSet H'}
    (hu' : (simplicialHomFamilyFunctor K A.toSSet).IsRepresentedBy u') : H ⟶ H' :=
  (Equiv.ofBijective _ hu'.map_bijective).symm (u.restrict A)

end AlgebraicGeometry.Scheme
