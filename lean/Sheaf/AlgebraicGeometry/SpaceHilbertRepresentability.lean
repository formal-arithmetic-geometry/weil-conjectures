/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite

/-! # Representability of the Hilbert functor of algebraic spaces

Source: Stacks Project, quot.tex, Situation 0CZY and Proposition 0D01
(blueprint: lem-sfb-space-hilbert-representability).

The values are closed subobjects of the actual sheaf fibre product. Naturality is
expressed by pullback squares of their inclusions, so it specifies inverse image
under every scheme base change, including nonflat base changes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The projection from the sheaf fibre product to the test scheme.
Source: Stacks, quot.tex, Situation 0CZY
(blueprint: lem-sfb-space-hilbert-representability). -/
def hilbertAmbientProjection {S : Scheme.{u}} {A B : AlgebraicSpace S}
    (a : A ⟶ B) {T : Over S} (t : schemeSpace T ⟶ B) :
    enlargedFibreProduct a t ⟶ schemeSpace T :=
  ObjectProperty.homMk (pullback.snd a.hom t.hom)

/-- The Hilbert functor's value: closed subspaces with proper, flat, finitely
presented structure map to the test scheme. Finite presentation is local finite
presentation, quasi-compactness and quasi-compactness of the diagonal.
Subobjects identify isomorphic closed immersions over the ambient space.
Source: Stacks, quot.tex, Situation 0CZY
(blueprint: lem-sfb-space-hilbert-representability). -/
def hilbertFamilies {S : Scheme.{u}} {A B : AlgebraicSpace S}
    (a : A ⟶ B) {T : Over S} (t : schemeSpace T ⟶ B) :=
  {C : ClosedSubspace (enlargedFibreProduct a t) //
    MapIsProper (C.val.arrow ≫ hilbertAmbientProjection a t) ∧
    MapIsFlat (C.val.arrow ≫ hilbertAmbientProjection a t) ∧
    MapIsLocallyOfFinitePresentation (C.val.arrow ≫ hilbertAmbientProjection a t) ∧
    MapIsQuasiCompact (C.val.arrow ≫ hilbertAmbientProjection a t).hom.hom ∧
    MapIsQuasiCompact
      (pullback.diagonal (C.val.arrow ≫ hilbertAmbientProjection a t).hom.hom)}

/-- The canonical map of ambient fibre products induced by a scheme base change.
Its two components are the identity on `A` and the given map of test schemes.
Source: Stacks, quot.tex, Situation 0CZY
(blueprint: lem-sfb-space-hilbert-representability). -/
def hilbertAmbientBaseChange {S : Scheme.{u}} {A B : AlgebraicSpace S}
    (a : A ⟶ B) {T T' : Over S} (t : schemeSpace T ⟶ B) (g : T' ⟶ T) :
    (enlargedFibreProduct a
      ((ObjectProperty.homMk ⟨yoneda.map g⟩ : schemeSpace T' ⟶ schemeSpace T) ≫ t)).obj ⟶
      (enlargedFibreProduct a t).obj :=
  let gSpace : schemeSpace T' ⟶ schemeSpace T := ObjectProperty.homMk ⟨yoneda.map g⟩
  pullback.lift (pullback.fst a.hom (gSpace ≫ t).hom)
    (pullback.snd a.hom (gSpace ≫ t).hom ≫ gSpace.hom)
    ((pullback.condition (f := a.hom) (g := (gSpace ≫ t).hom)).trans
      (Category.assoc (pullback.snd a.hom (gSpace ≫ t).hom) gSpace.hom t.hom).symm)

/-- A separated finitely presented map of algebraic spaces has a Hilbert algebraic
space locally of finite presentation. The equivalences identify maps over `B`
with all proper flat finitely presented closed families. The final clause says
that the corresponding closed immersions form a sheaf pullback square under
any scheme base change; this is precisely naturality for inverse image.
Source: Stacks, quot.tex, Proposition 0D01 and Situation 0CZY
(blueprint: lem-sfb-space-hilbert-representability).

Proof: apply lem-sfb-space-hilbert-is-quot (Stacks 0D00) to identify each family
with the quotient of the structure sheaf by its defining ideal. This identification
commutes with arbitrary base change, since tensoring a cyclic quotient gives the
quotient by the extended ideal. The structure sheaf is quasi-coherent and finitely
presented: on each etale chart it is free on one generator, with presentation
O^0 -> O -> O -> 0. Apply lem-sfb-space-quot-representability (Stacks 09TU) to
this sheaf and the separated finitely presented map `a`. It gives an algebraic
space locally of finite presentation over `B` representing Quot. Compose its
representing bijections with the inverse Hilbert--Quot identification. Both
identifications commute with every base change, so the resulting bijections
satisfy the displayed pullback-square condition. -/
theorem hilbert_representability {S : Scheme.{u}} {A B : AlgebraicSpace S}
    (a : A ⟶ B) (hsep : MapIsSeparated a)
    (hlfp : MapIsLocallyOfFinitePresentation a)
    (hqc : MapIsQuasiCompact a.hom.hom)
    (hqs : MapIsQuasiCompact (pullback.diagonal a.hom.hom)) :
    ∃ (H : AlgebraicSpace S) (p : H ⟶ B), MapIsLocallyOfFinitePresentation p ∧
      ∃ e : ∀ (T : Over S) (t : schemeSpace T ⟶ B),
        {h : schemeSpace T ⟶ H // h ≫ p = t} ≃ hilbertFamilies a t,
        ∀ (T T' : Over S) (t : schemeSpace T ⟶ B) (g : T' ⟶ T)
          (h : {h : schemeSpace T ⟶ H // h ≫ p = t})
          (h' : {h : schemeSpace T' ⟶ H // h ≫ p =
            (ObjectProperty.homMk ⟨yoneda.map g⟩ : schemeSpace T' ⟶ schemeSpace T) ≫ t}),
          h'.val = (ObjectProperty.homMk ⟨yoneda.map g⟩ :
            schemeSpace T' ⟶ schemeSpace T) ≫ h.val →
          ∃ d : ((e T' ((ObjectProperty.homMk ⟨yoneda.map g⟩ :
              schemeSpace T' ⟶ schemeSpace T) ≫ t) h').val.val : AlgebraicSpace S).obj ⟶
                ((e T t h).val.val : AlgebraicSpace S).obj,
            IsPullback d
              (e T' ((ObjectProperty.homMk ⟨yoneda.map g⟩ :
                schemeSpace T' ⟶ schemeSpace T) ≫ t) h').val.val.arrow.hom
              (e T t h).val.val.arrow.hom (hilbertAmbientBaseChange a t g) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
