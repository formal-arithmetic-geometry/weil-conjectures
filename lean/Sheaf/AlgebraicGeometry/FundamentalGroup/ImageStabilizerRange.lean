/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
/-!
# Image of the finite étale fundamental-group map

Source: SGA 1, Exposé V, Proposition 6.13 and §7
(blueprint: lem-galois-pi1-finite-etale-image-stabilizer-range).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.PreGaloisCategory
namespace AlgebraicGeometry.Scheme.FiniteEtale
/-- The image of the induced fundamental-group homomorphism is the marked-point stabilizer.
Source: SGA 1, Exposé V, Proposition 6.13, pp. 114–115, and §7, p. 116
(blueprint: lem-galois-pi1-finite-etale-image-stabilizer-range).

Proof (Proposition 6.13 leaves this argument to the reader):
1. Let `P` be the cover `f` and `a` its point `s`. The diagonal section
   `X ⟶ X ×[Y] X` carries the unique point of the terminal fibre to a point over `a`.
   Naturality of the `GX` action fixes this point, and `fundamentalGroupMap_smul`
   carries this equality to `f_*(h) • a = a`. Thus the image lies in the stabilizer.
2. For `g` fixing `a` and a finite étale cover `q : Z ⟶ X`, regard `Z` as a cover
   of `Y` by composition with `f`, using composition of finite and étale morphisms.
   Its fibre over `s` identifies with the subset of its fibre over `s ≫ f` whose
   image under `q` is `a`: both descriptions are morphisms `Spec Ω ⟶ Z` whose
   composite with `q` equals `s`. Naturality along `q` shows that `g` preserves
   this subset. Its inverse fixes `a` too, so the restriction is a bijection.
3. A morphism of covers over `X` is also one over `Y`; naturality over `Y` therefore
   makes the restricted bijections a natural automorphism of `fiber s`. The
   inverse restrictions are its inverse. The equivalence `toAutMulEquiv` produces
   an element `h` of `GX` with precisely these actions.
4. Apply these restrictions to a pullback cover `R ×[Y] X`. Its projection to `R`
   is a morphism over `Y`, and the induced map on the marked subset is exactly
   `pullbackFiberIso f s`. Naturality of `g` along this projection and
   `fundamentalGroupMap_smul` show that `f_*(h)` and `g` act identically on every
   fibre of `Y`. Faithfulness (`toAut_bijective`) gives `f_*(h) = g`, proving the
   reverse inclusion. No passage to locally constant sheaves is needed. -/
theorem fundamentalGroupMap_range_eq_stabilizer_range
    {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (GX GY : Type u) [Group GX] [TopologicalSpace GX] [IsTopologicalGroup GX]
    [CompactSpace GX] [∀ Q, MulAction GX ((fiber s).obj Q)]
    [IsFundamentalGroup (fiber s) GX]
    [Group GY] [TopologicalSpace GY] [IsTopologicalGroup GY] [CompactSpace GY]
    [∀ P, MulAction GY ((fiber (s ≫ f)).obj P)]
    [IsFundamentalGroup (fiber (s ≫ f)) GY] :
    let P : Y.FiniteEtale := ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩
    let a : (fiber (s ≫ f)).obj P := fiberMk (s ≫ f) P s rfl
    let U := MulAction.stabilizer GY a
    (fundamentalGroupMap (pullbackFiberIso f s) GX GY).range = U := by
  sorry
end AlgebraicGeometry.Scheme.FiniteEtale
