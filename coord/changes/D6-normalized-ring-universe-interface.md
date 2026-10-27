# WeilConjectures.NormalizedRingCompactScalar

## Reason

The source coefficient data was generalized to independent site and algebraic-closure universes, while this auxiliary module retained the old single-universe specialization. Generalize its records and theorem uniformly to Ω : Type v and schemes in Type (max u v), using the current C.{u,v} and inclusion interfaces. Every old equal-universe instance is retained. No conclusion is weakened and the existing theorem hole is unchanged.

## Old

```lean
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.Paper.RingedCoefficientPullbackCoherence
import Sheaf.Paper.RingedCoefficientProjectionCocycle
import Sheaf.SixFunctors.OpenTensorNormalization

/-! # Normalized compact-support scalar cocycles at ring stages

Source: current Weil blueprint, exceptional inverse image coefficient normalization;
Stacks Project, Tags 0GL1, 0D6D and 0E47
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle).

The input records below package only the realizations stipulated in the statement.
The categories, full inclusions, scalar associators, multiplication units and proper/open
comparison are the existing constructions. In particular no preservation or invertibility
of an ambient proper mate is built into these records.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures WeilConjectures.ConstructibleExceptionalCoefficients
open WeilConjectures.PurCompactSupport

namespace WeilConjectures.NormalizedRingCompactScalar

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- A supplied compact-support functor and its specified ambient realization.
Source: blueprint exceptional coefficient normalization, realization paragraph
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
structure Support (s : RingStage.{u} l) where
  functor : C l Ω X (s.stage l) ⥤ C l Ω Y (s.stage l)
  realization : functor ⋙ RingStage.inclusion l Ω Y s ≅
    RingStage.inclusion l Ω X s ⋙ image (s.coefficients l) c

/-- A supplied scalar functor with its actual ordinary derived scalar realization.
No exactness or shift structure is an additional input.
Source: blueprint exceptional coefficient normalization, sigma paragraph
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
structure Scalar {s t : RingStage.{u} l}
    (a : Change (s.coefficients l) (t.coefficients l)) (T : Scheme.{u}) where
  functor : C l Ω T (s.stage l) ⥤ C l Ω T (t.stage l)
  realization : functor ⋙ RingStage.inclusion l Ω T t ≅
    RingStage.inclusion l Ω T s ⋙ pbcDerivedExtend (a.map T)

/-- The written normalization of the supplied restricted comparison, component by component.
Source: blueprint exceptional coefficient normalization, displayed realization equation
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
def Normalized {s t : RingStage.{u} l}
    (a : Change (s.coefficients l) (t.coefficients l))
    (A : Support l Ω c s) (B : Support l Ω c t)
    (AX : Scalar l Ω a X) (AY : Scalar l Ω a Y)
    (q : A.functor ⋙ AY.functor ≅ AX.functor ⋙ B.functor) : Prop :=
  ∀ K : C l Ω X (s.stage l),
    (RingStage.inclusion l Ω Y t).map (q.hom.app K) ≫
        B.realization.hom.app (AX.functor.obj K) ≫
        (image (t.coefficients l) c).map (AX.realization.hom.app K) =
      AY.realization.hom.app (A.functor.obj K) ≫
        (pbcDerivedExtend (a.map Y)).map (A.realization.hom.app K) ≫
        (comparison a c).app ((RingStage.inclusion l Ω X s).obj K)

/-- A supplied restricted associator whose realization is balanced tensor associativity.
Source: blueprint exceptional coefficient normalization, alpha paragraph
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
structure Associator {s t r : RingStage.{u} l}
    {a : Change (s.coefficients l) (t.coefficients l)}
    {b : Change (t.coefficients l) (r.coefficients l)}
    {d : Change (s.coefficients l) (r.coefficients l)}
    (h : ∀ W : Scheme.{u}, a.map W ≫ b.map W = d.map W)
    (T : Scheme.{u}) (A : Scalar l Ω a T) (B : Scalar l Ω b T)
    (D : Scalar l Ω d T) where
  iso : A.functor ⋙ B.functor ≅ D.functor
  normalized (K : C l Ω T (s.stage l)) :
    (RingStage.inclusion l Ω T r).map (iso.hom.app K) ≫ D.realization.hom.app K =
      B.realization.hom.app (A.functor.obj K) ≫
        (pbcDerivedExtend (b.map T)).map (A.realization.hom.app K) ≫
        (tensorComposition (a.map T) (b.map T) (d.map T) (h T)).hom.app
          ((RingStage.inclusion l Ω T s).obj K)

/-- A supplied restricted unit whose realization is scalar multiplication.
The equality h retains arbitrary presentations of the identity ring map.
Source: blueprint exceptional coefficient normalization, unit paragraph
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
structure Unit {s : RingStage.{u} l}
    {a : Change (s.coefficients l) (s.coefficients l)}
    (h : ∀ W : Scheme.{u}, a.map W = 𝟙 _) (T : Scheme.{u})
    (A : Scalar l Ω a T) where
  iso : A.functor ≅ 𝟭 _
  normalized (K : C l Ω T (s.stage l)) :
    (RingStage.inclusion l Ω T s).map (iso.hom.app K) =
      A.realization.hom.app K ≫
        (eqToIso (congrArg pbcDerivedExtend (h T))).hom.app
          ((RingStage.inclusion l Ω T s).obj K) ≫
        (tensorIdentity ((s.coefficients l).ring T)).hom.app
          ((RingStage.inclusion l Ω T s).obj K)

/-- All five clauses of the normalized ring compact-support scalar assertion.
The last clause expresses independence of an allowedness proof through uniqueness for
fixed actual maps and realizations; any alternate presentation is compared via those
realizations. All coefficient changes are compatible maps of the actual ring sheaves.
Source: blueprint exceptional coefficient normalization, ambient and restricted cocycles
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
structure Laws : Prop where
  ambient_composition {s t r : RingStage.{u} l}
      (a : Change (s.coefficients l) (t.coefficients l))
      (b : Change (t.coefficients l) (r.coefficients l))
      (d : Change (s.coefficients l) (r.coefficients l))
      (h : ∀ W : Scheme.{u}, a.map W ≫ b.map W = d.map W)
      (M : DerivedCategory (pbcModules X ((s.coefficients l).ring X))) :
    (pbcDerivedExtend (b.map Y)).map ((comparison a c).app M) ≫
        (comparison b c).app ((pbcDerivedExtend (a.map X)).obj M) ≫
        (image (r.coefficients l) c).map
          ((tensorComposition (a.map X) (b.map X) (d.map X) (h X)).hom.app M) =
      (tensorComposition (a.map Y) (b.map Y) (d.map Y) (h Y)).hom.app
          ((image (s.coefficients l) c).obj M) ≫ (comparison d c).app M
  ambient_identity {s : RingStage.{u} l}
      (a : Change (s.coefficients l) (s.coefficients l))
      (h : ∀ W : Scheme.{u}, a.map W = 𝟙 _)
      (M : DerivedCategory (pbcModules X ((s.coefficients l).ring X))) :
    (comparison a c).app M ≫ (image (s.coefficients l) c).map
        ((eqToIso (congrArg pbcDerivedExtend (h X)) ≪≫
          tensorIdentity ((s.coefficients l).ring X)).hom.app M) =
      (eqToIso (congrArg pbcDerivedExtend (h Y)) ≪≫
        tensorIdentity ((s.coefficients l).ring Y)).hom.app
          ((image (s.coefficients l) c).obj M)
  composition {s t r : RingStage.{u} l}
      (a : Change (s.coefficients l) (t.coefficients l))
      (b : Change (t.coefficients l) (r.coefficients l))
      (d : Change (s.coefficients l) (r.coefficients l))
      (h : ∀ W : Scheme.{u}, a.map W ≫ b.map W = d.map W)
      (A : Support l Ω c s) (B : Support l Ω c t) (D : Support l Ω c r)
      (AX : Scalar l Ω a X) (AY : Scalar l Ω a Y)
      (BX : Scalar l Ω b X) (BY : Scalar l Ω b Y)
      (DX : Scalar l Ω d X) (DY : Scalar l Ω d Y)
      (qa : A.functor ⋙ AY.functor ≅ AX.functor ⋙ B.functor)
      (qb : B.functor ⋙ BY.functor ≅ BX.functor ⋙ D.functor)
      (qd : A.functor ⋙ DY.functor ≅ DX.functor ⋙ D.functor)
      (ha : Normalized l Ω c a A B AX AY qa)
      (hb : Normalized l Ω c b B D BX BY qb)
      (hd : Normalized l Ω c d A D DX DY qd)
      (αX : Associator l Ω h X AX BX DX) (αY : Associator l Ω h Y AY BY DY)
      (K : C l Ω X (s.stage l)) :
    BY.functor.map (qa.hom.app K) ≫ qb.hom.app (AX.functor.obj K) ≫
        D.functor.map (αX.iso.hom.app K) =
      αY.iso.hom.app (A.functor.obj K) ≫ qd.hom.app K
  identity {s : RingStage.{u} l} (a : Change (s.coefficients l) (s.coefficients l))
      (h : ∀ W : Scheme.{u}, a.map W = 𝟙 _) (A : Support l Ω c s)
      (AX : Scalar l Ω a X) (AY : Scalar l Ω a Y)
      (q : A.functor ⋙ AY.functor ≅ AX.functor ⋙ A.functor)
      (hq : Normalized l Ω c a A A AX AY q)
      (uX : Unit l Ω h X AX) (uY : Unit l Ω h Y AY)
      (K : C l Ω X (s.stage l)) :
    q.hom.app K ≫ A.functor.map (uX.iso.hom.app K) = uY.iso.hom.app (A.functor.obj K)
  unique {s t : RingStage.{u} l} (a : Change (s.coefficients l) (t.coefficients l))
      (A : Support l Ω c s) (B : Support l Ω c t)
      (AX : Scalar l Ω a X) (AY : Scalar l Ω a Y)
      (q q' : A.functor ⋙ AY.functor ≅ AX.functor ⋙ B.functor)
      (hq : Normalized l Ω c a A B AX AY q)
      (hq' : Normalized l Ω c a A B AX AY q') : q = q'

/-- Normalized compact-support scalar comparisons obey the ambient and restricted cocycles.
Source: current blueprint, exceptional inverse image coefficient normalization;
Stacks Project, Tags 0GL1, 0D6D, 0E47
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle).

Proof:
1. Write J_s for open extension and P_s for proper direct image. Open tensor
normalization identifies the restriction of each beta with identity. Restrict the
successive and direct beta composites to the open. Coefficient pullback coherence
identifies both with balanced associativity. Full faithfulness of J_r detects equality.
Multiplication units give the same open identity law. No flatness or stalk detection
is involved, including for completed ring sheaves.
2. Apply the ringed coefficient projection cocycle to the proper factor and the three
ring sheaves, using the compatible pull identifications. Its chi is the specified
proper mate. It supplies associativity and multiplication identities without assuming
invertibility, so quotient and mixed integral/finite maps are included.
3. Substitute Q_a = P_t(beta_a) chi_a(J_s). Naturality of chi_b at beta_a moves
P_t(beta_a) across chi_b. Functoriality followed by the open identity of step 1 and
the proper identity of step 2 yields the ambient composition identity. Apply their
unit identities in the same order for ambient_identity.
4. For the restricted comparisons put A_a = H_t(sigma_a^X) r_t(T_a^X) and
B_a = S_a^Y(r_s) sigma_a^Y(F_s). The hypothesis is A_a I_t(q_a) = Q_a(I_s) B_a.
Substitute this first for q_b and then q_a. Naturality of sigma_b^Y at q_a and of Q_b
at sigma_a^X identifies the successive realized comparison with Q_b S_b(Q_a),
conjugated by the successive A and B isomorphisms.
5. The two Associator.normalized equations and naturality of r_r identify the realized
restricted associators with tau_X and tau_Y. Apply the ambient composition identity,
cancel the A_d isomorphism and use faithfulness of the full inclusion I_r to obtain
composition at every K.
6. Unit.normalized, naturality of r_s and of scalar multiplication turn the identity
normalization into the ambient unit equation. Cancel r_s and use faithfulness for
identity. Finally Normalized determines I_t(q_a) uniquely by cancelling A_a. Faithfulness
and extensionality give unique. There is no inverse of the ambient Q_a anywhere.
-/
theorem normalizedRingCompactScalarCocycle
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Laws l Ω c := by
  sorry

end WeilConjectures.NormalizedRingCompactScalar
```

## New

```lean
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.Paper.RingedCoefficientPullbackCoherence
import Sheaf.Paper.RingedCoefficientProjectionCocycle
import Sheaf.SixFunctors.OpenTensorNormalization

/-! # Normalized compact-support scalar cocycles at ring stages

Source: current Weil blueprint, exceptional inverse image coefficient normalization;
Stacks Project, Tags 0GL1, 0D6D and 0E47
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle).

The input records below package only the realizations stipulated in the statement.
The categories, full inclusions, scalar associators, multiplication units and proper/open
comparison are the existing constructions. In particular no preservation or invertibility
of an ambient proper mate is built into these records.
-/

@[expose] public noncomputable section

set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures WeilConjectures.ConstructibleExceptionalCoefficients
open WeilConjectures.PurCompactSupport

namespace WeilConjectures.NormalizedRingCompactScalar

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X Y : Scheme.{max u v}} {f : X ⟶ Y} (c : Compactification f)

/-- A supplied compact-support functor and its specified ambient realization.
Source: blueprint exceptional coefficient normalization, realization paragraph
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
structure Support (s : RingStage.{max u v} l) where
  functor : C.{u, v} l Ω X (s.stage l) ⥤ C.{u, v} l Ω Y (s.stage l)
  realization : functor ⋙ RingStage.inclusion.{u, v} l Ω Y s ≅
    RingStage.inclusion.{u, v} l Ω X s ⋙ image (s.coefficients l) c

/-- A supplied scalar functor with its actual ordinary derived scalar realization.
No exactness or shift structure is an additional input.
Source: blueprint exceptional coefficient normalization, sigma paragraph
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
structure Scalar {s t : RingStage.{max u v} l}
    (a : Change (s.coefficients l) (t.coefficients l)) (T : Scheme.{max u v}) where
  functor : C.{u, v} l Ω T (s.stage l) ⥤ C.{u, v} l Ω T (t.stage l)
  realization : functor ⋙ RingStage.inclusion.{u, v} l Ω T t ≅
    RingStage.inclusion.{u, v} l Ω T s ⋙ pbcDerivedExtend (a.map T)

/-- The written normalization of the supplied restricted comparison, component by component.
Source: blueprint exceptional coefficient normalization, displayed realization equation
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
def Normalized {s t : RingStage.{max u v} l}
    (a : Change (s.coefficients l) (t.coefficients l))
    (A : Support.{u, v} l Ω c s) (B : Support.{u, v} l Ω c t)
    (AX : Scalar.{u, v} l Ω a X) (AY : Scalar.{u, v} l Ω a Y)
    (q : A.functor ⋙ AY.functor ≅ AX.functor ⋙ B.functor) : Prop :=
  ∀ K : C.{u, v} l Ω X (s.stage l),
    (RingStage.inclusion.{u, v} l Ω Y t).map (q.hom.app K) ≫
        B.realization.hom.app (AX.functor.obj K) ≫
        (image (t.coefficients l) c).map (AX.realization.hom.app K) =
      AY.realization.hom.app (A.functor.obj K) ≫
        (pbcDerivedExtend (a.map Y)).map (A.realization.hom.app K) ≫
        (comparison a c).app ((RingStage.inclusion.{u, v} l Ω X s).obj K)

/-- A supplied restricted associator whose realization is balanced tensor associativity.
Source: blueprint exceptional coefficient normalization, alpha paragraph
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
structure Associator {s t r : RingStage.{max u v} l}
    {a : Change (s.coefficients l) (t.coefficients l)}
    {b : Change (t.coefficients l) (r.coefficients l)}
    {d : Change (s.coefficients l) (r.coefficients l)}
    (h : ∀ W : Scheme.{max u v}, a.map W ≫ b.map W = d.map W)
    (T : Scheme.{max u v}) (A : Scalar.{u, v} l Ω a T) (B : Scalar.{u, v} l Ω b T)
    (D : Scalar.{u, v} l Ω d T) where
  iso : A.functor ⋙ B.functor ≅ D.functor
  normalized (K : C.{u, v} l Ω T (s.stage l)) :
    (RingStage.inclusion.{u, v} l Ω T r).map (iso.hom.app K) ≫ D.realization.hom.app K =
      B.realization.hom.app (A.functor.obj K) ≫
        (pbcDerivedExtend (b.map T)).map (A.realization.hom.app K) ≫
        (tensorComposition (a.map T) (b.map T) (d.map T) (h T)).hom.app
          ((RingStage.inclusion.{u, v} l Ω T s).obj K)

/-- A supplied restricted unit whose realization is scalar multiplication.
The equality h retains arbitrary presentations of the identity ring map.
Source: blueprint exceptional coefficient normalization, unit paragraph
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
structure Unit {s : RingStage.{max u v} l}
    {a : Change (s.coefficients l) (s.coefficients l)}
    (h : ∀ W : Scheme.{max u v}, a.map W = 𝟙 _) (T : Scheme.{max u v})
    (A : Scalar.{u, v} l Ω a T) where
  iso : A.functor ≅ 𝟭 _
  normalized (K : C.{u, v} l Ω T (s.stage l)) :
    (RingStage.inclusion.{u, v} l Ω T s).map (iso.hom.app K) =
      A.realization.hom.app K ≫
        (eqToIso (congrArg pbcDerivedExtend (h T))).hom.app
          ((RingStage.inclusion.{u, v} l Ω T s).obj K) ≫
        (tensorIdentity ((s.coefficients l).ring T)).hom.app
          ((RingStage.inclusion.{u, v} l Ω T s).obj K)

/-- All five clauses of the normalized ring compact-support scalar assertion.
The last clause expresses independence of an allowedness proof through uniqueness for
fixed actual maps and realizations; any alternate presentation is compared via those
realizations. All coefficient changes are compatible maps of the actual ring sheaves.
Source: blueprint exceptional coefficient normalization, ambient and restricted cocycles
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle). -/
structure Laws : Prop where
  ambient_composition {s t r : RingStage.{max u v} l}
      (a : Change (s.coefficients l) (t.coefficients l))
      (b : Change (t.coefficients l) (r.coefficients l))
      (d : Change (s.coefficients l) (r.coefficients l))
      (h : ∀ W : Scheme.{max u v}, a.map W ≫ b.map W = d.map W)
      (M : DerivedCategory (pbcModules X ((s.coefficients l).ring X))) :
    (pbcDerivedExtend (b.map Y)).map ((comparison a c).app M) ≫
        (comparison b c).app ((pbcDerivedExtend (a.map X)).obj M) ≫
        (image (r.coefficients l) c).map
          ((tensorComposition (a.map X) (b.map X) (d.map X) (h X)).hom.app M) =
      (tensorComposition (a.map Y) (b.map Y) (d.map Y) (h Y)).hom.app
          ((image (s.coefficients l) c).obj M) ≫ (comparison d c).app M
  ambient_identity {s : RingStage.{max u v} l}
      (a : Change (s.coefficients l) (s.coefficients l))
      (h : ∀ W : Scheme.{max u v}, a.map W = 𝟙 _)
      (M : DerivedCategory (pbcModules X ((s.coefficients l).ring X))) :
    (comparison a c).app M ≫ (image (s.coefficients l) c).map
        ((eqToIso (congrArg pbcDerivedExtend (h X)) ≪≫
          tensorIdentity ((s.coefficients l).ring X)).hom.app M) =
      (eqToIso (congrArg pbcDerivedExtend (h Y)) ≪≫
        tensorIdentity ((s.coefficients l).ring Y)).hom.app
          ((image (s.coefficients l) c).obj M)
  composition {s t r : RingStage.{max u v} l}
      (a : Change (s.coefficients l) (t.coefficients l))
      (b : Change (t.coefficients l) (r.coefficients l))
      (d : Change (s.coefficients l) (r.coefficients l))
      (h : ∀ W : Scheme.{max u v}, a.map W ≫ b.map W = d.map W)
      (A : Support.{u, v} l Ω c s) (B : Support.{u, v} l Ω c t) (D : Support.{u, v} l Ω c r)
      (AX : Scalar.{u, v} l Ω a X) (AY : Scalar.{u, v} l Ω a Y)
      (BX : Scalar.{u, v} l Ω b X) (BY : Scalar.{u, v} l Ω b Y)
      (DX : Scalar.{u, v} l Ω d X) (DY : Scalar.{u, v} l Ω d Y)
      (qa : A.functor ⋙ AY.functor ≅ AX.functor ⋙ B.functor)
      (qb : B.functor ⋙ BY.functor ≅ BX.functor ⋙ D.functor)
      (qd : A.functor ⋙ DY.functor ≅ DX.functor ⋙ D.functor)
      (ha : Normalized.{u, v} l Ω c a A B AX AY qa)
      (hb : Normalized.{u, v} l Ω c b B D BX BY qb)
      (hd : Normalized.{u, v} l Ω c d A D DX DY qd)
      (αX : Associator.{u, v} l Ω h X AX BX DX) (αY : Associator.{u, v} l Ω h Y AY BY DY)
      (K : C.{u, v} l Ω X (s.stage l)) :
    BY.functor.map (qa.hom.app K) ≫ qb.hom.app (AX.functor.obj K) ≫
        D.functor.map (αX.iso.hom.app K) =
      αY.iso.hom.app (A.functor.obj K) ≫ qd.hom.app K
  identity {s : RingStage.{max u v} l} (a : Change (s.coefficients l) (s.coefficients l))
      (h : ∀ W : Scheme.{max u v}, a.map W = 𝟙 _) (A : Support.{u, v} l Ω c s)
      (AX : Scalar.{u, v} l Ω a X) (AY : Scalar.{u, v} l Ω a Y)
      (q : A.functor ⋙ AY.functor ≅ AX.functor ⋙ A.functor)
      (hq : Normalized.{u, v} l Ω c a A A AX AY q)
      (uX : Unit.{u, v} l Ω h X AX) (uY : Unit.{u, v} l Ω h Y AY)
      (K : C.{u, v} l Ω X (s.stage l)) :
    q.hom.app K ≫ A.functor.map (uX.iso.hom.app K) = uY.iso.hom.app (A.functor.obj K)
  unique {s t : RingStage.{max u v} l} (a : Change (s.coefficients l) (t.coefficients l))
      (A : Support.{u, v} l Ω c s) (B : Support.{u, v} l Ω c t)
      (AX : Scalar.{u, v} l Ω a X) (AY : Scalar.{u, v} l Ω a Y)
      (q q' : A.functor ⋙ AY.functor ≅ AX.functor ⋙ B.functor)
      (hq : Normalized.{u, v} l Ω c a A B AX AY q)
      (hq' : Normalized.{u, v} l Ω c a A B AX AY q') : q = q'

/-- Normalized compact-support scalar comparisons obey the ambient and restricted cocycles.
Source: current blueprint, exceptional inverse image coefficient normalization;
Stacks Project, Tags 0GL1, 0D6D, 0E47
(blueprint: lem-sf-normalized-ring-compact-scalar-cocycle).

Proof:
1. Write J_s for open extension and P_s for proper direct image. Open tensor
normalization identifies the restriction of each beta with identity. Restrict the
successive and direct beta composites to the open. Coefficient pullback coherence
identifies both with balanced associativity. Full faithfulness of J_r detects equality.
Multiplication units give the same open identity law. No flatness or stalk detection
is involved, including for completed ring sheaves.
2. Apply the ringed coefficient projection cocycle to the proper factor and the three
ring sheaves, using the compatible pull identifications. Its chi is the specified
proper mate. It supplies associativity and multiplication identities without assuming
invertibility, so quotient and mixed integral/finite maps are included.
3. Substitute Q_a = P_t(beta_a) chi_a(J_s). Naturality of chi_b at beta_a moves
P_t(beta_a) across chi_b. Functoriality followed by the open identity of step 1 and
the proper identity of step 2 yields the ambient composition identity. Apply their
unit identities in the same order for ambient_identity.
4. For the restricted comparisons put A_a = H_t(sigma_a^X) r_t(T_a^X) and
B_a = S_a^Y(r_s) sigma_a^Y(F_s). The hypothesis is A_a I_t(q_a) = Q_a(I_s) B_a.
Substitute this first for q_b and then q_a. Naturality of sigma_b^Y at q_a and of Q_b
at sigma_a^X identifies the successive realized comparison with Q_b S_b(Q_a),
conjugated by the successive A and B isomorphisms.
5. The two Associator.normalized equations and naturality of r_r identify the realized
restricted associators with tau_X and tau_Y. Apply the ambient composition identity,
cancel the A_d isomorphism and use faithfulness of the full inclusion I_r to obtain
composition at every K.
6. Unit.normalized, naturality of r_s and of scalar multiplication turn the identity
normalization into the ambient unit equation. Cancel r_s and use faithfulness for
identity. Finally Normalized determines I_t(q_a) uniquely by cancelling A_a. Faithfulness
and extensionality give unique. There is no inverse of the ambient Q_a anywhere.
-/
theorem normalizedRingCompactScalarCocycle
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Laws.{u, v} l Ω c := by
  sorry

end WeilConjectures.NormalizedRingCompactScalar
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.NormalizedRingCompactScalarCocycle | unclaimed | Uniform universe generalization only. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | D6 | Instantiates the theorem at the independent universes of the unchanged target signature. |

## Status

landed 20261025T162157-L-343722 2026-10-25 (merge of deliver/D6/Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence)
