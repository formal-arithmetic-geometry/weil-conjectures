/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleHypercover
public import WeilConjectures.AlgebraicGeometry.SemiRepresentableObject
public import Sheaf.Paper.SiteHypercoverFiniteExtensionBase

/-! # Split affine-component presentations of étale hypercovers

Source: Stacks Project, Hypercoverings, Tags 0DAU, 0DAV and 0DB2
(blueprint: def-sfb-affine-etale-hypercover-presentation).

Formal families retain the component-index maps. The cofans realize them as
coproduct schemes, and their naturality identifies the actual simplicial operators.
The existing splitness predicate on every finite truncation supplies the canonical
epi-label decomposition and the invertible component degeneracy maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A split affine-component presentation with its actual coproduct realization.
No quasi-compactness, quasi-separatedness or finiteness of the index sets is required.
The splitness condition uses the already defined nondegenerate indices and canonical
label-to-index map, rather than a second notion of splitting.
Source: Stacks, Tags 0DAU, 0DAV and 0DB2
(blueprint: def-sfb-affine-etale-hypercover-presentation). -/
structure AffineEtaleHypercoverPresentation (T : Scheme.{u}) where
  /-- The formal simplicial family, including all compatible component maps. -/
  components : SimplicialObject (FormalCoproduct.{u} T.Etale)
  /-- Its augmented simplicial scheme, viewed in the small étale site. -/
  simplicial : SimplicialObject T.Etale
  /-- The specified component inclusions over T. -/
  inclusion : ∀ (n : SimplexCategoryᵒᵖ) (i : (components.obj n).I),
    (Scheme.Etale.forget T).obj ((components.obj n).obj i) ⟶
      (Scheme.Etale.forget T).obj (simplicial.obj n)
  /-- These are actual coproducts in schemes over T. -/
  coproduct : ∀ n : SimplexCategoryᵒᵖ, IsColimit (Cofan.mk
    ((Scheme.Etale.forget T).obj (simplicial.obj n)) (inclusion n))
  /-- Every component is affine. -/
  affine : ∀ (n : SimplexCategoryᵒᵖ) (i : (components.obj n).I),
    IsAffine ((components.obj n).obj i).left
  /-- Simplicial operators agree with the prescribed component maps and indices. -/
  naturality : ∀ (n m : SimplexCategoryᵒᵖ) (α : n ⟶ m) (i : (components.obj n).I),
    inclusion n i ≫ (Scheme.Etale.forget T).map (simplicial.map α) =
      (Scheme.Etale.forget T).map ((components.map α).φ i) ≫
        inclusion m ((components.map α).f i)
  /-- In every degree the canonical epi-label normalization is bijective and
  its degeneracy component maps are isomorphisms. -/
  split : ∀ n : ℕ, CategoryTheory.FormalSplitAttachment.IsSplit
    ((SimplicialObject.truncation (C := FormalCoproduct.{u} T.Etale) n).obj components)
  /-- The realized matching morphisms are surjective étale. -/
  hypercover : IsEtaleHypercover simplicial

end AlgebraicGeometry
