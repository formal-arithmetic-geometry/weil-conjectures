/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.OrientedAffineNeighbourhoodLimit
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Localization of an oriented product at a representable triple

Source: Illusie--Laszlo--Orgogozo, Exposé XI 1.10(b), equivalence (1.b) and
localization morphism (1.c), printed pp. 175--176
(blueprint: lem-trf-oriented-slice-localization).
-/

@[expose] public noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
  AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.OrientedProduct

/-- The canonical comparison of the two iterated etale base changes in the left
commuting square of `Z`. Source: ILO XI 1.9 and 1.10(b), diagram (1.a)
(blueprint: lem-trf-oriented-slice-localization). -/
def orientedSliceLeftBaseChangeIso {X S Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (Z : OrientedEtaleTriples f g) :
    f.Etale ⋙ Z.left.1.hom.Etale ≅
      Z.right.hom.Etale ⋙ (orientedTripleLeft Z).Etale :=
  (MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale) (Q := ⊤)
      Z.left.1.hom f).symm ≪≫
    MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale) (Q := ⊤)
      (orientedTripleLeft Z) Z.right.hom (Z.left.1.hom ≫ f) (by
        have hz : Z.hom.1.left ≫ pullback.snd Z.right.hom f = Z.left.1.hom :=
          MorphismProperty.Over.w Z.hom.1
        dsimp only [orientedTripleLeft]
        rw [Category.assoc, pullback.condition, ← Category.assoc, hz])

/-- The canonical comparison of the two iterated etale base changes in the right
commuting square of `Z`. Source: ILO XI 1.9 and 1.10(b), diagram (1.a)
(blueprint: lem-trf-oriented-slice-localization). -/
def orientedSliceRightBaseChangeIso {X S Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (Z : OrientedEtaleTriples f g) :
    g.Etale ⋙ Z.left.2.hom.Etale ≅
      Z.right.hom.Etale ⋙ (orientedTripleRight Z).Etale :=
  (MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale) (Q := ⊤)
      Z.left.2.hom g).symm ≪≫
    MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale) (Q := ⊤)
      (orientedTripleRight Z) Z.right.hom (Z.left.2.hom ≫ g) (by
        have hz : Z.hom.2.left ≫ pullback.snd Z.right.hom g = Z.left.2.hom :=
          MorphismProperty.Over.w Z.hom.2
        dsimp only [orientedTripleRight]
        rw [Category.assoc, pullback.condition, ← Category.assoc, hz])

/-- The componentwise base-change site functor. On `T=(A,B,D)` its components are
`A ×_X U`, `B ×_S V`, `D ×_Y W`, with structural maps obtained by pulling back
those of `T` and applying the canonical iterated-pullback comparisons for `Z`.
Equivalently this is `T ↦ T × Z → Z`, read on the relative triple site.
Source: ILO XI 1.9 and 1.10(b), map (1.c)
(blueprint: lem-trf-oriented-slice-localization). -/
def orientedSliceBaseChange {X S Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (Z : OrientedEtaleTriples f g) :
    OrientedEtaleTriples f g ⥤
      OrientedEtaleTriples (orientedTripleLeft Z) (orientedTripleRight Z) :=
  Comma.map
    ((Z.left.1.hom.Etale.prod Z.left.2.hom.Etale).rightUnitor.hom ≫
      (Z.left.1.hom.Etale.prod Z.left.2.hom.Etale).leftUnitor.inv)
    ((orientedSliceLeftBaseChangeIso Z).hom.prod'
      (orientedSliceRightBaseChangeIso Z).hom)

/-- The slice equivalence intertwines the slice projection with the geometric morphism
induced by the three scheme maps: its direct image is restriction along the explicitly
constructed componentwise base-change site functor.

Source: ILO XI 1.10(b), (1.b)--(1.c), printed pp. 175--176; Stacks 00Y1
(blueprint: lem-trf-oriented-slice-localization).

Proof, following the seven steps of the DAG node:
1. Identify triples over `Z` with relative triples using the componentwise small etale
site localization equivalences (lem-weil-pbc-etale-site-localization-open). Objects and
arrows retain their underlying schemes and commuting diagrams. The two structural
maps of `Z` need not be etale.
2. Identify all three covering generators: the outside etale covers are unchanged,
and a middle refinement pulls back the last component in both presentations.
Saturating the generators gives the same topology, by
lem-weil-pbc-pretopology-sheaf-condition and def-pur-localized-ringed-site.
3. Reindex sheaves through this site equivalence. Apply
lem-weil-pbc-localized-sheaves-over-representable to obtain the slice equivalence,
using sheafified representables without a subcanonicity assumption.
4. Its fibre quasi-inverse sends `(F × H_Z → H_Z)` over `(T,a)` to `F(T)` by
`s ↦ (s,η(a))`. Hence it intertwines the slice inverse image with restriction
along the forgetful localized-site functor (def-pur-localized-ringed-site).
5. The functor orientedSliceBaseChange preserves finite limits and the three types
of covers, componentwise. The left exact site inverse image construction
(lem-weil-pbc-left-exact-site-inverse-image-tensor) gives `t` with the displayed
direct-image formula, including its naturality in both triples and sheaves.
6. On first, second, and middle triples this functor is the respective base change
along `U → X`, `W → Y`, and `V → S`. The structural arrows defining the orientation
are preserved. The inverse-image formula and uniqueness in
lem-trf-oriented-product-universal identify `t` with the morphism induced by these
three maps and their commuting squares (ILO XI 1.9).
7. Restriction along the localized-site forgetful functor is left adjoint to this
direct image: restrict sections to `T × Z` in one direction, and use the graph
`(id_T,a)` in the other. Projection and graph identities verify both round trips.
Combine this adjunction with step 4 to obtain the asserted isomorphism over `P`.
-/
theorem oriented_slice_localization
    (X S Y : Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S)
    (U : X.Etale) (V : S.Etale) (W : Y.Etale)
    (a : U ⟶ f.Etale.obj V) (b : W ⟶ g.Etale.obj V) :
    ∃ (t : GeometricMorphism
        (Sheaf (orientedEtaleTopology (orientedTripleLeft
          (⟨(U, W), V, (a, b)⟩ : OrientedEtaleTriples f g))
          (orientedTripleRight (⟨(U, W), V, (a, b)⟩ : OrientedEtaleTriples f g)))
          (Type (u + 1)))
        (Sheaf (orientedEtaleTopology f g) (Type (u + 1)))),
      Nonempty (t.direct ⋙ sheafToPresheaf (orientedEtaleTopology f g) (Type (u + 1)) ≅
        sheafToPresheaf (orientedEtaleTopology
          (orientedTripleLeft (⟨(U, W), V, (a, b)⟩ : OrientedEtaleTriples f g))
          (orientedTripleRight (⟨(U, W), V, (a, b)⟩ : OrientedEtaleTriples f g)))
          (Type (u + 1)) ⋙
        (whiskeringLeft _ _ (Type (u + 1))).obj
          (orientedSliceBaseChange (⟨(U, W), V, (a, b)⟩ : OrientedEtaleTriples f g)).op) ∧
      ∃ e : Over ((orientedEtaleAssociated f g).obj
          (⟨(U, W), V, (a, b)⟩ : OrientedEtaleTriples f g)) ≌
        Sheaf (orientedEtaleTopology
          (orientedTripleLeft (⟨(U, W), V, (a, b)⟩ : OrientedEtaleTriples f g))
          (orientedTripleRight (⟨(U, W), V, (a, b)⟩ : OrientedEtaleTriples f g)))
          (Type (u + 1)),
        Nonempty (Over.star ((orientedEtaleAssociated f g).obj
          (⟨(U, W), V, (a, b)⟩ : OrientedEtaleTriples f g)) ⋙ e.functor ≅ t.inverse) := by
  sorry

end CategoryTheory.OrientedProduct
