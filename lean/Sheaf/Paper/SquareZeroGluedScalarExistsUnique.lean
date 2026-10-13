/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.CategoryTheory.CommAlgebraSheafModule
public import Sheaf.Paper.DerivedHomMayerVietoris




/-! # The quotient action on a square-zero ideal

Source: Stacks Project, Cohomology, Lemma 0B8S, first paragraph of the proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by local lifts gives a uniquely determined section of the kernel.
Source: Stacks Project, Cohomology, Lemma 0B8S, first paragraph of its proof.
(blueprint: lem-sc-square-zero-glued-scalar-exists-unique)

Proof: Choose an open covering of U on which f lifts to b_a, using local
surjectivity of p. Each product b_a*i(x|V_a) is killed by p. Exactness and the
injectivity of i give its unique preimage y_a in I(V_a). On overlaps the two
lifts differ by a kernel section. Its product with i(x) is zero by square-zero,
so the products and their preimages agree. Glue y_a in the sheaf I.
To check the displayed formula for any other local lift b on V, intersect V
with the chosen cover, apply the same difference-of-lifts calculation, and
use separatedness and injectivity. Any two sections with the displayed
property agree on the lifting cover, hence are equal. The empty open is
handled by sheaf separatedness on the empty cover, and I=0 gives its unique
section. This assertion constructs one section only; it asserts neither
linearity nor ring laws nor restriction compatibility of an operator family. -/
theorem square_zero_glued_scalar_exists_unique (X : Scheme.{u})
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C)
    (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (i : I ⟶ commAlgebraSheafModule X.sheaf B)
    (hw : i ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
    (hS : (ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p) hw).ShortExact)
    (hsq : ∀ (U : X.Opens) (x y : B.right.obj.obj (op U)),
      p.right.hom.app (op U) x = 0 → p.right.hom.app (op U) y = 0 → x * y = 0) :
    ∀ (U : X.Opens) (f : C.right.obj.obj (op U)) (x : I.val.obj (op U)),
      ∃! y : I.val.obj (op U),
        ∀ (V : X.Opens) (j : V ⟶ U) (b : B.right.obj.obj (op V)),
          p.right.hom.app (op V) b = C.right.obj.map j.op f →
            @id (B.right.obj.obj (op V))
              (i.val.app (op V) (I.val.map j.op y)) =
                b * @id (B.right.obj.obj (op V))
                  (i.val.app (op V) (I.val.map j.op x)) := by sorry

end AlgebraicGeometry
