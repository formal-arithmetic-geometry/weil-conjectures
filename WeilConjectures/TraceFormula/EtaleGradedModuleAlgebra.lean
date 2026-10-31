/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Homogeneous commutative algebra operations on small étale module sheaves

Source: Stacks Project, spaces-descent.tex, Tag 0D3C, the graded algebra preceding psi_d;
sites-modules.tex, Section 03EK (blueprint: def-trf-etale-graded-module-algebra).

The homogeneous bilinear maps are compatible with all chart restrictions. They extend
by sheafification and the sheaf coproduct universal property, with ordinary commutativity.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A commutative unital homogeneous algebra on the small étale site.
The scalar rings are the actual regular functions of the chart schemes.
Source: Stacks, Tag 0D3C (blueprint: def-trf-etale-graded-module-algebra). -/
structure EtaleGradedModuleAlgebra (B : ℕ → X.Modules) where
  mul (m n : ℕ) (V : X.EtaleSite) :
    (B m).val.obj (op V) →+ (B n).val.obj (op V) →+ (B (m + n)).val.obj (op V)
  smul_left (m n : ℕ) (V : X.EtaleSite) (r : X.structureSheaf.obj.obj (op V))
      (s : (B m).val.obj (op V)) (t : (B n).val.obj (op V)) :
    mul m n V (r • s) t = r • mul m n V s t
  smul_right (m n : ℕ) (V : X.EtaleSite) (r : X.structureSheaf.obj.obj (op V))
      (s : (B m).val.obj (op V)) (t : (B n).val.obj (op V)) :
    mul m n V s (r • t) = r • mul m n V s t
  unit : SheafOfModules.unit X.structureSheaf ⟶ B 0
  naturality (m n : ℕ) {V W : X.EtaleSite} (f : V ⟶ W)
      (s : (B m).val.obj (op W)) (t : (B n).val.obj (op W)) :
    (B (m + n)).val.map f.op (mul m n W s t) =
      mul m n V ((B m).val.map f.op s) ((B n).val.map f.op t)
  assoc (l m n : ℕ) (V : X.EtaleSite) (a : (B l).val.obj (op V))
      (b : (B m).val.obj (op V)) (c : (B n).val.obj (op V)) :
    HEq (mul (l + m) n V (mul l m V a b) c)
      (mul l (m + n) V a (mul m n V b c))
  comm (m n : ℕ) (V : X.EtaleSite) (a : (B m).val.obj (op V))
      (b : (B n).val.obj (op V)) : HEq (mul m n V a b) (mul n m V b a)
  one_mul (n : ℕ) (V : X.EtaleSite) (a : (B n).val.obj (op V)) :
    HEq (mul 0 n V (unit.val.app (op V) (1 : X.structureSheaf.obj.obj (op V))) a) a
  mul_one (n : ℕ) (V : X.EtaleSite) (a : (B n).val.obj (op V)) :
    HEq (mul n 0 V a (unit.val.app (op V) (1 : X.structureSheaf.obj.obj (op V)))) a

/-- A homogeneous algebra homomorphism, including the degree-zero unit law.
Source: Stacks, Tag 0D3C, psi (blueprint: def-trf-etale-graded-module-algebra). -/
structure EtaleGradedModuleAlgebra.Hom {B C : ℕ → X.Modules}
    (A : EtaleGradedModuleAlgebra B) (D : EtaleGradedModuleAlgebra C) where
  degree (d : ℕ) : B d ⟶ C d
  mul (m n : ℕ) (V : X.EtaleSite)
      (s : (B m).val.obj (op V)) (t : (B n).val.obj (op V)) :
    (degree (m + n)).val.app (op V) (A.mul m n V s t) =
      D.mul m n V ((degree m).val.app (op V) s) ((degree n).val.app (op V) t)
  unit : A.unit ≫ degree 0 = D.unit

/-- The total object is the coproduct in sheaves of modules.
No assertion about infinite sums of sections on individual charts is included.
Source: Stacks, Tag 0D3C (blueprint: def-trf-etale-graded-module-algebra). -/
def EtaleGradedModuleAlgebra.total {B : ℕ → X.Modules}
    (_A : EtaleGradedModuleAlgebra B) [HasCoproduct B] : X.Modules := ∐ B

end AlgebraicGeometry.AlgebraicSpace
