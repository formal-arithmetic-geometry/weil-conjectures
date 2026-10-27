/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.SixFunctors.IntegralOperationShiftData
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.NormalizedDVRTower
import Sheaf.SixFunctors.OpenSystemTensorShift
import Mathlib.CategoryTheory.Shift.CommShift

/-! # Shifts of the strict-system compactification projection

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, Step 2;
Stacks Project, sites-cohomology.tex, Tags 0B56, 0GL1, 0D6D and 07A4
(blueprint: lem-pur-strict-compactification-projection-shift).

The maps are the existing proper counit mate, normalized open tensor comparison,
and pullback compositor on the ordinary unbounded derived category of strict systems.
The shifts below use the published cochain and signed total-tensor comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The second-variable shift through exact pullback and signed system tensor.
On a total summand of first degree a the tensor comparison is (-1)^(r*a).
Source: Stacks 07A4 and the blueprint adic Step 2
(blueprint: lem-pur-strict-compactification-projection-shift). -/
def strictTensorPullShift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : System l E X) (N : System l E Y) (r : ℤ) :
    (calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj (N⟦r⟧)) ≅
      ((calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj N))⟦r⟧ :=
  (calculus l E X).systemClosed.tensor.mapIso
      (Iso.prod (Iso.refl M)
        ((Functor.commShiftIso (pull l E f) (self := systemPullShift l E f) r).app N)) ≪≫
    ((tensorShifts l E).systemRight X r).app (M, (pull l E f).obj N)

/-- The target shift of the proper projection mate, with the adjunction-mate shift
on total right-derived direct image.
Source: Stacks 0B56 and the blueprint adic Step 2
(blueprint: lem-pur-strict-compactification-projection-shift). -/
def strictProperTargetShift (o : Operations l E) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : System l E X) (N : System l E Y) (r : ℤ) :
    (Operations.push l E o f).obj
        ((calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj (N⟦r⟧))) ≅
      ((Operations.push l E o f).obj
        ((calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj N)))⟦r⟧ :=
  (Operations.push l E o f).mapIso (strictTensorPullShift l E f M N r) ≪≫
    (Functor.commShiftIso (Operations.push l E o f)
      (self := systemPushShift l E o f) r).app
        ((calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj N))

/-- The target shift of the normalized open tensor comparison uses exact termwise
extension by zero after the pullback and tensor comparisons.
Source: Stacks 0GL1 and the blueprint adic Step 2
(blueprint: lem-pur-strict-compactification-projection-shift). -/
def strictOpenTargetShift (o : Operations l E) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (M : System l E U) (N : System l E X) (r : ℤ) :
    (Operations.shriek l E o j).obj
        ((calculus l E U).systemClosed.tensor.obj (M, (pull l E j).obj (N⟦r⟧))) ≅
      ((Operations.shriek l E o j).obj
        ((calculus l E U).systemClosed.tensor.obj (M, (pull l E j).obj N)))⟦r⟧ :=
  (Operations.shriek l E o j).mapIso (strictTensorPullShift l E j M N r) ≪≫
    (Functor.commShiftIso (Operations.shriek l E o j)
      (self := systemOpenShift l E o j) r).app
        ((calculus l E U).systemClosed.tensor.obj (M, (pull l E j).obj N))

/-- The actual inverse-image compositor, including the compactification equation.
Source: Stacks 0D6D and the blueprint adic Step 2
(blueprint: lem-pur-strict-compactification-projection-shift). -/
def strictCompactificationPullComp (o : Operations l E) (c : Compositors l E o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f) :
    pull l E d.g ⋙ pull l E d.i ≅ pull l E f :=
  (c.pullComp d.i d.g).symm ≪≫ eqToIso (congrArg (pull l E) d.comm.symm)

/-- The target shift of the specified three-factor compactification projection.
It is exactly the composite comparison of H_M, with no evaluation or reconstruction.
Source: blueprint adic Step 2 and Stacks 0B56, 0GL1
(blueprint: lem-pur-strict-compactification-projection-shift). -/
def strictCompactificationTargetShift (o : Operations l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f)
    (M : System l E X) (N : System l E Y) (r : ℤ) :
    (Operations.shriek l E o d.i ⋙ Operations.push l E o d.g).obj
        ((calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj (N⟦r⟧))) ≅
      ((Operations.shriek l E o d.i ⋙ Operations.push l E o d.g).obj
        ((calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj N)))⟦r⟧ :=
  (Operations.shriek l E o d.i ⋙ Operations.push l E o d.g).mapIso
      (strictTensorPullShift l E f M N r) ≪≫
    (Functor.commShiftIso (Operations.shriek l E o d.i ⋙ Operations.push l E o d.g)
      (self := (systemShifts l E o).compactSupport f d) r).app
        ((calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj N))

/-- The proper/open compactification projection commutes with every integer shift
in its second variable, as a map of derived strict systems. The next two clauses
are the separate proper and open squares; the last is the pullback compositor square.
All input objects are arbitrary in the ordinary unbounded derived categories.
Consequently the equations include normalized bounded constructible finite-Tor systems;
no invertibility of the proper mate or of the whole projection is asserted.

The supplied Operations, Compositors and OpenComparisons are exactly the simultaneous
models of lem-sf-integral-compactification-system-realization. Their defining adjunction,
cochain and open-unit equations fix the maps; no shift-compatibility premise is supplied.

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, Step 2;
Stacks 0B56 (equation-projection-formula-map), 0GL1 (lemma-j-shriek-and-tensor),
0D6D (lemma-derived-pullback-composition), 07A4 (lemma-pullback-tensor-product)
(blueprint: lem-pur-strict-compactification-projection-shift).

Proof:
1. By lem-coef-semilinear-derived-sections, whole systems are modules on the
ringed sequence site. The simultaneous models identify P, S, J and tensor with
actual derived operations there. Apply lem-weil-pbc-ringed-projection-mate-exact
at p_c and J_j M: its counit-defined mate is precisely properProjection.
The constant-system structural ring map is an isomorphism, so no transition
flatness is required.
2. The proper mate theorem gives the [1] square. Paste it to get positive
integer shifts. Apply it at N[-1], shift by [-1] and cancel the invertible
comparisons for the [-1] square; iterate for negative shifts. The r=0 equation
is the identity. Signed tensor coherence uses (-1)^((r+s)*a)=(-1)^(r*a)(-1)^(s*a).
3. Apply lem-pur-open-system-tensor-shift to M and P_p N. Its open-unit
normalization is that of a.projection. Precompose by P_p and apply S_p;
lem-weil-pbc-commshift-nattrans-comp-whisker gives the middle factor's square.
4. The pullback compositor of lem-sf-integral-compactification-system-realization
is the class of the degreewise inverse-image compositor. On N[r] it is the
same component on N^(b+r), with differential multiplier (-1)^r on both routes.
Tensor by M gives the same (-1)^(r*a) on both routes. Apply J and S.
5. Write the three factors a_N,b_N,c_N. Substitute their squares successively
in s_3 c_(N[r]) b_(N[r]) a_(N[r]); this is c_N[r] b_N[r] a_N[r] s_0.
Composition and whiskering use lem-weil-pbc-commshift-nattrans-comp-whisker.
Every equality is on the actual system site before evaluation, scalar
restriction or total inverse limit. Restricting inputs gives the normalized
finite-Tor special case without any claim that evaluation detects morphisms. -/
theorem strictCompactificationProjectionShift
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : Compactification f) (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) :
    (∀ (M : System l E X) (N : System l E Y) (r : ℤ),
      compactificationProjection l E o c a d M (N⟦r⟧) ≫
          (strictCompactificationTargetShift l E o d M N r).hom =
        ((tensorShifts l E).systemRight Y r).hom.app
            ((Operations.push l E o d.g).obj ((Operations.shriek l E o d.i).obj M), N) ≫
          (compactificationProjection l E o c a d M N)⟦r⟧') ∧
    (∀ (Q : System l E d.Z) (N : System l E Y) (r : ℤ),
      ((properProjection l E o d.g).app Q).app (N⟦r⟧) ≫
          (strictProperTargetShift l E o d.g Q N r).hom =
        ((tensorShifts l E).systemRight Y r).hom.app
            ((Operations.push l E o d.g).obj Q, N) ≫
          (((properProjection l E o d.g).app Q).app N)⟦r⟧') ∧
    (∀ (M : System l E X) (Q : System l E d.Z) (r : ℤ),
      (a.projection d.i).hom.app (M, Q⟦r⟧) ≫
          (strictOpenTargetShift l E o d.i M Q r).hom =
        ((tensorShifts l E).systemRight d.Z r).hom.app
            ((Operations.shriek l E o d.i).obj M, Q) ≫
          ((a.projection d.i).hom.app (M, Q))⟦r⟧') ∧
    (∀ (N : System l E Y) (r : ℤ),
      (strictCompactificationPullComp l E o c d).hom.app (N⟦r⟧) ≫
          (Functor.commShiftIso (pull l E f) (self := systemPullShift l E f) r).hom.app N =
        (pull l E d.i).map
            ((Functor.commShiftIso (pull l E d.g)
              (self := systemPullShift l E d.g) r).hom.app N) ≫
          (Functor.commShiftIso (pull l E d.i)
            (self := systemPullShift l E d.i) r).hom.app ((pull l E d.g).obj N) ≫
          ((strictCompactificationPullComp l E o c d).hom.app N)⟦r⟧') := by
  sorry

end WeilConjectures.IntegralSystemRealization
