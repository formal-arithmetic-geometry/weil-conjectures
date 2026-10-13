/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Sheaf.AlgebraicGeometry.InverseImageModuleFunctor

/-! # Naturality of the ordinary balanced tensor comparison

Source: Stacks Project, Cohomology, Lemma 20.27.4 (Tag 08DE), proof.
(blueprint: lem-pc-relative-tensor-pullback-balanced-naturality)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- The balanced tensor identity for ordinary module sheaves is natural in both variables.
Source: Stacks Project, Cohomology, Lemma 20.27.4 (Tag 08DE), proof.

Proof: write R = f-inverse O_S and B = O_X. On sections, the balanced map
M tensor_B (B tensor_R N) -> M restricted to R tensor_R N sends
m tensor (b tensor n) to (b*m) tensor n. Its inverse sends m tensor n to
m tensor (1 tensor n). Additivity and the B- and R-balancing relations make
both maps well defined. Their composites are the identity on pure tensors,
and pure tensors generate the section tensor products. Both maps commute
with restrictions. Tensoring with module sheafification agrees with
sheafifying the tensor presheaf, so replacing the scalar-extension presheaf
by its sheafification preserves this comparison. Underlying module
sheafification is abelian sheafification, independent of the coefficient ring.
The sheafification universal property therefore gives inverse maps of
abelian sheaves. The construction is natural in each variable:
a B-linear map commutes with multiplication by b, and an R-linear map
commutes with forming b tensor n. Transport the second factor along hG;
hGmap identifies its morphisms with the tensor pullback morphisms. Thus the
two displayed naturality equalities hold. This works for arbitrary modules,
including zero modules, zero coefficient rings, and the empty scheme. No
complex, differential, coproduct, flatness or derived category is involved.
(blueprint: lem-pc-relative-tensor-pullback-balanced-naturality) -/
theorem exists_relativeTensorPullback_balanced_natural
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hG : ∀ M, G.obj M = Modules.tensorPullbackObj f M)
    (hGmap : ∀ {M N} (a : M ⟶ N),
      G.map a = eqToHom (hG M) ≫ Modules.tensorPullbackMap f a ≫ eqToHom (hG N).symm) :
    let R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (TopCat.Sheaf.inverseImageRing f.base S.sheaf))
    let U := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
    let V := SheafOfModules.toSheaf R
    let H := SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map (Modules.tensorPullbackRingMap f))
    let I := TopCat.Sheaf.inverseImageModuleFunctor f.base S.sheaf
    let T := @curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)
    let T' := @curriedTensor _ _ (SheafOfModules.monoidalCategory
      (TopCat.Sheaf.inverseImageRing f.base S.sheaf))
    ∃ e : ∀ M N, U.obj ((T.obj M).obj (G.obj N)) ≅
        V.obj ((T'.obj (H.obj M)).obj (I.obj N)),
      (∀ M M' (a : M ⟶ M') N,
        U.map ((T.map a).app (G.obj N)) ≫ (e M' N).hom =
          (e M N).hom ≫ V.map ((T'.map (H.map a)).app (I.obj N))) ∧
      (∀ M N N' (b : N ⟶ N'),
        U.map ((T.obj M).map (G.map b)) ≫ (e M N').hom =
          (e M N).hom ≫ V.map ((T'.obj (H.obj M)).map (I.map b))) := by sorry

end AlgebraicGeometry.Scheme
