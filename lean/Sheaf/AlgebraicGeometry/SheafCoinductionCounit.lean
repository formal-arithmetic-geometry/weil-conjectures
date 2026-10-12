/-
Copyright (c) 2026 M1. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: M1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# The coinduction evaluation Hom-bijections

Source: Stacks Project, Tag 0A6F and Tag 0BUZ.
(blueprint: lem-sc-sheaf-coinduction-counit).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- The evaluation Hom-bijections are natural, with an explicit inverse formula.
The functor and isomorphism are arbitrary provided their multiplication action agrees
with the internal-Hom multiplication action; the adjunction is constructed afterwards.

Source: Stacks Project, Modules, Tag 0A6F, lemma-adjoint-tensor-restrict;
Duality, Tag 0BUZ, lemma-compute-sheafhom-affine.
(blueprint: lem-sc-sheaf-coinduction-counit).

Proof: Given g : T(G) -> F, on U send m in G(U) to the local O_X-linear
map whose component on W sends b in A(W) to g_W(b * m|W). This is O_X-linear
in b because g_W is O_X-linear. It commutes with restrictions by naturality
of g and semilinearity of the restriction maps of G. Transport this section
through i.inv to obtain a section of H(F). The resulting map is additive and
A-linear: the given action formula identifies both the image of a*m and the
a-multiple of the image of m with b -> g_W((a|W*b)*m|W), using commutativity.
Thus these section maps define a morphism G -> H(F). Conversely, for
psi : G -> H(F), restrict scalars and evaluate i(psi(m)) on the identity open
at 1. This is O_X-linear since i and psi are O_X-linear, and evaluation at
1 of an O_X-linear local morphism is O_X-linear in that morphism. Naturality
of i and psi and restriction of 1 ensure compatibility with restriction.
Evaluation of the transpose gives g because 1*m=m. For the other inverse,
A-linearity of psi, the specified action, and naturality give
 i(psi(m))_W(b) = i(psi(b*m|W))_W(1).
Consequently the two assignments are inverse by internal-Hom extensionality
and injectivity of i. Both assignments commute with precomposition in G and
postcomposition in F; the latter uses naturality of i. These two naturality
identities give Adjunction.CoreHomEquiv. Its inverse is the evaluation map
just constructed, which proves the displayed formula. The argument needs no
nonempty open or nonzero ring hypothesis. -/
theorem sheafHom_restrictScalars_counit
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    let A := ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj Y.ringCatSheaf
    let T := SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom
    let M := T.obj (SheafOfModules.unit A)
    let K := (SheafOfModules.homFunctor X.sheaf).obj (op M)
    ∀ (H : SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} A)
      (i : H ⋙ T ≅ K),
      (∀ (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
        (a : A.obj.obj (op U)) (φ : (H.obj F).val.obj (op U))
        (W : Over U) (b : A.obj.obj (op W.left)),
        (((i.hom.app F).val.app (op U)).hom (a • φ)).app (op W) b =
          (((i.hom.app F).val.app (op U)).hom φ).app (op W)
            (A.obj.map W.hom.op a * b)) →
      ∃ e : Adjunction.CoreHomEquiv T H,
        ∀ (G : SheafOfModules.{u} A) (F : SheafOfModules.{u} X.ringCatSheaf)
          (ψ : G ⟶ H.obj F) (U : X.Opens) (m : G.val.obj (op U)),
          (((e.homEquiv G F).symm ψ).val.app (op U)).hom m =
            ((((i.hom.app F).val.app (op U)).hom
              (((ψ.val.app (op U)).hom) m)).app
              (op (Over.mk (𝟙 U)))) (1 : A.obj.obj (op U)) := by
  sorry

end AlgebraicGeometry
