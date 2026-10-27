/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.SeparatedAlgebraicModuliMap
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Separation permanence for arbitrary algebraic stacks

Source: Stacks Project, stacks-morphisms.tex, Tags 050F, 050K and 04YS
(blueprint: lem-sfb-stack-separation-compactness-permanence).

Separatedness is properness of the relative diagonal on algebraic-space scheme tests.
The three statements apply to arbitrary algebraic stacks over a field; the last statement
assumes representability by algebraic spaces, and uses closed-immersion scheme tests.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry

namespace CategoryTheory

/-- Arbitrary algebraic-stack base change preserves separatedness.
Source: Stacks Project, stacks-morphisms.tex, Tag 050F
(blueprint: lem-sfb-stack-separation-compactness-permanence).
Proof: Step 1 identifies every diagonal test with the fibre product of the two Isom
spaces, using lem-sfb-stack-isom-space-locally-finite-type,
lem-trf-space-fibre-products-etale-covers and lem-sfb-algebraic-stack-fibre-products.
Step 2 extends proper scheme tests of representable maps to algebraic-space tests by
lem-sfb-representable-pullback-over-space and lem-sfb-space-proper-arbitrary-scheme-tests.
Associativity of triples and lem-sfb-fibred-groupoid-representable-smooth-calculus give
base-change stability of representability and properness; corresponding tests are
isomorphic under the canonical equivalences. Step 3 uses identity (1) of
lem-sfb-groupoid-diagonal-two-pullback-identities: the new diagonal is a base change of
the old one, so Step 2 makes its tests proper. -/
theorem separatedAlgebraicModuliMap_baseChange (k : Type u) [Field k]
    {A : BasedCategory.{v₁, w₁} (Over (Spec (.of k)))}
    {B : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))}
    {B' : BasedCategory.{v₃, w₃} (Over (Spec (.of k)))}
    (f : BasedFunctor A B) (b : BasedFunctor B' B)
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (hB' : IsAlgebraicModuliStack B') (hf : IsSeparatedAlgebraicModuliMap f) :
    IsSeparatedAlgebraicModuliMap (moduliTwoFiberFst b f) := by
  sorry

/-- Composition preserves separatedness for arbitrary algebraic stacks.
Source: Stacks Project, stacks-morphisms.tex, Tag 050K
(blueprint: lem-sfb-stack-separation-compactness-permanence).
Proof: Steps 1--2 of the node give algebraic-space diagonal tests and properness
calculus for representable maps. In particular composition of proper representable
maps follows from lem-sfb-space-proper-composition by testing the second map first
and then the first map over that algebraic space. Step 4 factors the composite
diagonal as Delta_f followed by A x_B A -> A x_C A. Identity (2) of
lem-sfb-groupoid-diagonal-two-pullback-identities, with u = v = f and h = g,
identifies the second arrow as a base change of Delta_g. Both factors are therefore
proper and representable by Step 2. Their composite is Delta_(g f) on objects and arrows,
so the composite is separated. -/
theorem separatedAlgebraicModuliMap_comp (k : Type u) [Field k]
    {A : BasedCategory.{v₁, w₁} (Over (Spec (.of k)))}
    {B : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))}
    {C : BasedCategory.{v₃, w₃} (Over (Spec (.of k)))}
    (f : BasedFunctor A B) (g : BasedFunctor B C)
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (hC : IsAlgebraicModuliStack C)
    (hf : IsSeparatedAlgebraicModuliMap f) (hg : IsSeparatedAlgebraicModuliMap g) :
    IsSeparatedAlgebraicModuliMap (f.comp g) := by
  sorry

/-- For representable morphisms, proper and closed-immersion relative diagonals agree.
Source: Stacks Project, stacks-morphisms.tex, Tag 04YS
(blueprint: lem-sfb-stack-separation-compactness-permanence).
Proof: Step 5 writes a diagonal test (x1,x2,alpha) as the equalizer of the two sections
(x1,id) and (x2,alpha inverse) of A x_B T. By lem-sfb-space-diagonal-scheme-tests this
is a scheme monomorphism; no atlas for A or B is needed. In Step 6 properness as a space
implies properness as a scheme by lem-sfb-space-representable-proper-tests at the
identity test. The criterion lem-pc-proper-monomorphism-closed gives a closed immersion.
Conversely every scheme test is a closed immersion and therefore proper by clause (a)
of lem-weil-pbc-closed-immersion-proper. Its further scheme tests are again tests of the
same diagonal. Applying lem-sfb-space-representable-proper-tests in reverse makes the
algebraic-space projections intrinsically proper, which is separatedness. -/
theorem separatedAlgebraicModuliMap_iff_closedDiagonal (k : Type u) [Field k]
    {A : BasedCategory.{v₁, w₁} (Over (Spec (.of k)))}
    {B : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))}
    (f : BasedFunctor A B)
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (hf : IsRepresentableByAlgebraicSpaces f) :
    IsSeparatedAlgebraicModuliMap f ↔
      ModuliSchemeTest @IsClosedImmersion (moduliRelativeDiagonal f) := by
  sorry

end CategoryTheory
