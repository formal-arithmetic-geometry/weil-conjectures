/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AbelianSpacePoincareData
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality

/-! # Pointed rigidity for relative abelian algebraic spaces

Source: Milne, Abelian Varieties, I Theorem 1.1 and Corollary 1.2, printed pp.8--9;
relative assembly using Stacks Tags 0E0S, 0AEJ and 05Z1
(blueprint: lem-sfb-relative-abelian-pointed-rigidity).

The maps are arbitrary natural transformations. The abelian-family hypotheses include
properness, smoothness, finite presentation and scheme-representable abelian geometric
fibres. Equalities are equalities of morphisms, including their nilpotent information.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

open Poincare

/-- The actual pullback of a space morphism along a scheme parameter, with its unchanged
parameter coordinate and its source coordinate mapped by `f`.
Source: Stacks, Spaces, Tag 02X2; Milne I Section 1, base change of the rigidity identity
(blueprint: lem-sfb-relative-abelian-pointed-rigidity). -/
def relativeAbelianBaseChangeMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (T : Over S) :
    product (groupSpaceProjection X) (groupSchemeMap (Over.homMk T.hom (by simp))) ⟶
      product (groupSpaceProjection Y) (groupSchemeMap (Over.homMk T.hom (by simp))) :=
  pair (fst (groupSpaceProjection X) (groupSchemeMap (Over.homMk T.hom (by simp))) ≫ f)
    (snd (groupSpaceProjection X) (groupSchemeMap (Over.homMk T.hom (by simp))))
    (baseMap_eq _ _)

/-- A morphism from a product of relative abelian spaces vanishes if it vanishes on
both identity axes. The resulting equality pulls back along every locally Noetherian
scheme base change; no reducedness hypothesis is imposed.
Source: Milne, Abelian Varieties, I Theorem 1.1, printed pp.8--9; Stacks 0E0S, 0AEJ,
05Z1 (blueprint: lem-sfb-relative-abelian-pointed-rigidity).

Proof:
1. For arbitrary abelian families P,Q,R, smoothness gives flatness on etale charts by
   lem-pc-smooth-flat. By lem-sc-abelian-variety-characterization their geometric fibres
   are geometrically integral. For a residue field and any extension K, the geometric
   fibre over an algebraic closure of K maps surjectively and faithfully flat on charts
   to the K-fibre. Reducedness descends faithfully flat, and irreducibility descends
   under this surjection; the K-fibre is separated. Thus the residue-field fibres are
   geometrically integral. With the identity section, lem-sfb-rigidified-space-picard
   gives the canonical isomorphism O_T → (p_T)_* O_{P_T} for every scheme T. Only this
   universal functions assertion is used here.
2. On each geometric fibre the spaces are schemes. Apply lem-sc-rigidity to the map
   P × Q → R: P is proper, geometrically connected and reduced, Q is connected, R is
   separated and locally of finite type. The axis at e_Q is the constant e_R. Rigidity
   factors the map through Q, and the other zero axis makes that factor zero.
3. Take a surjective etale scheme atlas of Q and cover it by affine schemes T. View
   the pulled-back map as P_T → R_T. Properness is preserved by base change by
   lem-sfb-space-flat-proper-fp-locality. Its geometric fibre images are singletons.
   By lem-sfb-proper-space-finite-image-neighbourhood, T is covered by affine opens V
   on which this map factors as P_V → Z → R_V, with Z affine finite over V.
4. Write a : P_V → Z, p : P_V → V, and s for the identity section. Step 1 identifies
   p^sharp as an isomorphism of full rings of functions, so s^sharp is its inverse.
   With b = a s, the ring maps of a and b p agree. Injectivity in
   lem-sfb-space-affine-target-global-functions gives a = b p. The remaining axis
   says that Z → R_V composed with b is the identity section, hence the map is zero.
   This argument retains nilpotents in the rings of functions.
5. Equality descends from these atlas opens: every test scheme lifts etale locally to
   the atlas, and R is a sheaf. Therefore the original map is zero as a natural
   transformation. Finally pull back this equality using the actual fibre-product
   pairing map; this proves the base-change assertion, including nonreduced bases.
-/
theorem relativeAbelian_two_axis_vanishing
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (A B C : AlgebraicSpace S)
    (g : CommutativeSpaceGroup A) (h : CommutativeSpaceGroup B)
    (k : CommutativeSpaceGroup C)
    (hA : IsAbelianFamily (groupSpaceProjection A))
    (hB : IsAbelianFamily (groupSpaceProjection B))
    (hC : IsAbelianFamily (groupSpaceProjection C))
    (v : product (groupSpaceProjection A) (groupSpaceProjection B) ⟶ C)
    (hvA : rightAxis (pointedGroup A g) (pointedGroup B h) ≫ v =
      groupSpaceProjection A ≫ k.identity)
    (hvB : leftAxis (pointedGroup A g) (pointedGroup B h) ≫ v =
      groupSpaceProjection B ≫ k.identity) :
    v = (fst (groupSpaceProjection A) (groupSpaceProjection B) ≫
      groupSpaceProjection A) ≫ k.identity ∧
    ∀ (T : Over S) [IsLocallyNoetherian T.left],
      relativeAbelianBaseChangeMap v T =
        relativeAbelianBaseChangeMap
          ((fst (groupSpaceProjection A) (groupSpaceProjection B) ≫
            groupSpaceProjection A) ≫ k.identity) T := by
  sorry

/-- Every identity-preserving morphism of relative abelian spaces is a homomorphism.
The displayed multiplication identity and its actual pullback along every locally
Noetherian base change hold as morphism equalities over possibly nonreduced bases.
Source: Milne, Abelian Varieties, I Corollary 1.2, printed p.9; relative rigidity as in
Stacks 0E0S, 0AEJ and 05Z1 (blueprint: lem-sfb-relative-abelian-pointed-rigidity).

Proof: first prove the two-axis assertion by steps 1--5 of
relativeAbelian_two_axis_vanishing (the first five steps of this node). Then form the
additivity defect d(x,y) = a(x+y) - a(x) - a(y), using the specified group operations.
The pointed hypothesis makes both axes zero. The two-axis assertion for P = Q = A
and R = B makes d = 0, which is precisely the displayed multiplication identity.
Identity preservation is given, so this is IsHom for the given group laws. Pulling
back the equality along any scheme base change pulls back its actual composites,
projections and group operations. This gives the asserted equality after every locally
Noetherian base change, with nilpotents retained. This is step 6 of the node's proof.
-/
theorem relativeAbelian_pointed_rigidity
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (A B : AlgebraicSpace S) (g : CommutativeSpaceGroup A) (h : CommutativeSpaceGroup B)
    (hA : IsAbelianFamily (groupSpaceProjection A))
    (hB : IsAbelianFamily (groupSpaceProjection B))
    (a : A ⟶ B) (ha : g.identity ≫ a = h.identity) :
    IsHom g h a ∧
    addition A g ≫ a =
      productMap (pointedGroup A g) (pointedGroup A g)
        (pointedGroup B h) (pointedGroup B h) a a ≫ addition B h ∧
    ∀ (T : Over S) [IsLocallyNoetherian T.left],
      relativeAbelianBaseChangeMap (addition A g ≫ a) T =
        relativeAbelianBaseChangeMap
          (productMap (pointedGroup A g) (pointedGroup A g)
            (pointedGroup B h) (pointedGroup B h) a a ≫ addition B h) T := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
