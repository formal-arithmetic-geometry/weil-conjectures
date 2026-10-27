/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Sheaf.AlgebraicGeometry.SpaceSeparatedLqfPermanence
import Sheaf.AlgebraicGeometry.QuasiAffineBaseChange
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite

/-!
# The quasi-affine saturated pullback in the off-diagonal induction

Source: Stacks Project, Morphisms of Spaces, Tag 03XW (lemma-neighbourhood-scheme),
third and fourth proof paragraphs
(blueprint: lem-a1-etale-saturation-quasi-affine-pullback).

`X'` and `Xstar` are arbitrary presentations of the specified fibre products, with
`IsPullback` witnesses. The equations for `d₁` characterize its canonical map uniquely.
`i` identifies `Tstar` with the clopen complement of the diagonal in `T' ×_T T'`.
The open union is expressed by its least-upper-bound property in `OpenSubspace`;
pointwise union of subfunctors would fail the sheaf condition on disconnected tests.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The off-diagonal open is a quasi-affine scheme, and a quasi-compact schematic
image of it makes the saturated pullback a quasi-compact quasi-affine scheme.
The first two conclusion clauses give separatedness and chartwise local quasi-finiteness
of `X' → T'`. The next clauses identify `Xstar` using the second projection and identify
`Z = d₀⁻¹(V)` with the scheme base change of `V` using the first projection.
The final clauses say that the preimage of `W` is the open union of `V` and `H`, is also
`W ×_T T'`, and has a quasi-compact scheme representative quasi-affine over `T'`.
Source: Stacks Project, Morphisms of Spaces, Tag 03XW, proof paragraphs 3--4
(blueprint: lem-a1-etale-saturation-quasi-affine-pullback).

Proof:
1. Apply lem-a1-space-separated-lqf-permanence to `f` and `a`. The fibre-product
   universal property identifies `Xstar` with the base change of `X'` along π₁,
   because `a π₀ = a π₁`. Pulling back `V` along `d₀` is open by
   lem-a1-space-open-factor-scheme-tests; its sections identify it with
   `Vscheme ×_(T',π₀) Tstar`. Its map to `Tstar` is quasi-affine by
   lem-trf-quasi-affine-base-change.
2. The scheme-test comparison of lem-a1-space-open-factor-scheme-tests identifies
   `V ×_X X'` with the inverse image of `V` in `X ×_T (T' ×_T T')`.
   Its image in `X'` is the inverse image of `W`. The clopen decomposition of the
   double base change splits this image into `V` over the diagonal and `H` off it.
   The inclusion-preserving open-subspace correspondence in
   lem-a1-space-etale-open-image gives the least-upper-bound identity.
3. Scheme tests pull back these two opens to an open cover. The algebraic-space
   fppf sheaf is a Zariski sheaf by lem-pc-zariski-coverings-are-fppf. Apply
   lem-pc-schemes-criterion to the two representable opens to represent their union.
4. Quasi-affineness over affine `T'` makes `Vscheme` quasi-compact. The hypothesis
   makes `Hscheme` quasi-compact. Restrict an open cover to these two opens, take
   finite subcovers, and unite them to prove quasi-compactness of the union.
5. By lem-a1-space-separated-lqf-permanence its scheme structure map is separated
   and locally quasi-finite. The affine target is quasi-separated by
   lem-weil-pbc-affine-scheme-qcqs, so lem-weil-pbc-qcqs-morphism-permanence(1)
   makes the map quasi-compact. Apply lem-weil-pbc-lqf-locally-finite-type and then
   lemma-nagata-quasi-affine-morphism-of-quasi-finite to obtain quasi-affineness.
-/
theorem etale_saturation_quasi_affine_pullback
    {S : Scheme.{u}} (T T' : Over S) [IsAffine T.left] [IsAffine T'.left]
    (a : T' ⟶ T) [Etale a.left] (X : AlgebraicSpace S)
    (f : X.obj.obj ⟶ yoneda.obj T)
    (hqf : ∀ (U : Over S) (v : yoneda.obj U ⟶ X.obj.obj), IsEtale v →
      Scheme.Hom.IsLocallyQuasiFinite (yoneda.preimage (v ≫ f)).left)
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (Limits.pullback.diagonal f))
    (X' : AlgebraicSpace S) (r : X'.obj.obj ⟶ X.obj.obj)
    (t : X'.obj.obj ⟶ yoneda.obj T') (hX' : IsPullback r t f (yoneda.map a))
    (V : OpenSubspace X') (Vscheme : Over S) (eV : yoneda.obj Vscheme ≅ V.val.toFunctor)
    (hV : IsQuasiAffineHom (yoneda.preimage (eV.hom ≫ V.val.ι ≫ t)).left)
    (W : OpenSubspace X) (hW : pointImage W.val.ι = pointImage (V.val.ι ≫ r))
    (Tstar : Over S) [IsAffine Tstar.left] (i : Tstar ⟶ Limits.pullback a a)
    [IsOpenImmersion i.left] [IsClosedImmersion i.left]
    (hi : Set.range i.left = (Set.range (Limits.pullback.diagonal a).left)ᶜ)
    (hb : Etale (i ≫ Limits.pullback.snd a a).left)
    (Xstar : AlgebraicSpace S) (d₀ d₁ : Xstar.obj.obj ⟶ X'.obj.obj)
    (s : Xstar.obj.obj ⟶ yoneda.obj Tstar)
    (hstar : IsPullback d₀ s t (yoneda.map (i ≫ Limits.pullback.fst a a)))
    (hd₁r : d₁ ≫ r = d₀ ≫ r)
    (hd₁t : d₁ ≫ t = s ≫ yoneda.map (i ≫ Limits.pullback.snd a a)) :
    (∀ (U : Over S) (v : yoneda.obj U ⟶ X'.obj.obj), IsEtale v →
      Scheme.Hom.IsLocallyQuasiFinite (yoneda.preimage (v ≫ t)).left) ∧
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (Limits.pullback.diagonal t) ∧
    IsPullback d₁ s t (yoneda.map (i ≫ Limits.pullback.snd a a)) ∧
    IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (V.val.preimage d₀).ι ∧
    (∃ eZ : yoneda.obj (Limits.pullback
        (yoneda.preimage (eV.hom ≫ V.val.ι ≫ t)) (i ≫ Limits.pullback.fst a a)) ≅
          (V.val.preimage d₀).toFunctor,
      eZ.hom ≫ (V.val.preimage d₀).ι ≫ d₀ =
        yoneda.map (Limits.pullback.fst _ _) ≫ eV.hom ≫ V.val.ι ∧
      eZ.hom ≫ (V.val.preimage d₀).ι ≫ s = yoneda.map (Limits.pullback.snd _ _)) ∧
    IsQuasiAffineHom (Limits.pullback.snd
      (yoneda.preimage (eV.hom ≫ V.val.ι ≫ t)) (i ≫ Limits.pullback.fst a a)).left ∧
    ∀ (H : OpenSubspace X')
      (hH : pointImage H.val.ι = pointImage ((V.val.preimage d₀).ι ≫ d₁))
      (Hscheme : Over S) (eH : yoneda.obj Hscheme ≅ H.val.toFunctor)
      (hHqc : CompactSpace Hscheme.left),
    ∃ P : OpenSubspace X',
      P.val = W.val.preimage r ∧ IsLUB ({V, H} : Set (OpenSubspace X')) P ∧
      (∃ k : P.val.toFunctor ⟶ W.val.toFunctor,
        k ≫ W.val.ι = P.val.ι ≫ r ∧
        IsPullback k (P.val.ι ≫ t) (W.val.ι ≫ f) (yoneda.map a)) ∧
      ∃ (Pscheme : Over S) (eP : yoneda.obj Pscheme ≅ P.val.toFunctor),
        CompactSpace Pscheme.left ∧
        IsQuasiAffineHom (yoneda.preimage (eP.hom ≫ P.val.ι ≫ t)).left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
