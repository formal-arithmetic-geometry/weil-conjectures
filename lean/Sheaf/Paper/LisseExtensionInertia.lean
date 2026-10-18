/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.Paper.QbarCurveOrdinaryImage
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Paper.CanonicalWeilFundamentalRepresentation
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Sheaf.Paper.DenseOpenPiOneSurjective
import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.Paper.CommonStageCurveWeilMiddleExtension
import Sheaf.Paper.EtaleWeilFundamentalRepresentation
import Sheaf.Paper.EtaleWeilSheafEquivalence
import Sheaf.Paper.RealSheavesSetup

/-! # Lisse extension and trivial boundary inertia

Source: Stacks Project, Tag 0BTD; Weil II (1.1.12); blueprint main-20261015,
rem-dl-a1-conventions, second paragraph (blueprint: lem-dl-a1-lisse-extension-inertia).

The ordinary sheaf realization of Weil pairs is used, rather than a derived category
of Weil sheaves. The direct image is the already recorded curveWeilMiddleExtension.
The adjoint of a restriction isomorphism is specified by its actual underlying
adic sheaf adjunction, so its normalization is part of the statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- The characteristic implicit in the finite-field datum.
Source: the finite-field hypothesis of Tag 0BTD and rem-dl-a1-conventions
(blueprint: lem-dl-a1-lisse-extension-inertia).
Proof: a finite field has prime characteristic r and cardinality r^b with b positive.
The datum gives cardinality p^a with a positive and p prime. Unique factorization
therefore gives r = p. -/
theorem FiniteFieldDatum.lisseExtensionCharacteristic (D : FiniteFieldDatum.{u}) :
    ringChar D.k₀ = D.p := by
  sorry

/-- Supply the upstream coefficient-prime class from the stated inequality l != p.
Source: rem-dl-a1-conventions (blueprint: lem-dl-a1-lisse-extension-inertia). -/
instance FiniteFieldDatum.lisseExtensionCoefficientFact (D : FiniteFieldDatum.{u})
    (l : ℕ) [hl : Fact (l ≠ D.p)] : Fact (ringChar D.k₀ ≠ l) :=
  ⟨fun h ↦ hl.out (h.symm.trans D.lisseExtensionCharacteristic)⟩

end WeilConjectures

namespace AlgebraicGeometry

open WeilConjectures

/-- The dense open and its ambient pure one-dimensional curve satisfy the existing
upstream curve class (separated, finite type, dimension at most one).
Source: Tag 0BTD; rem-dl-a1-conventions (blueprint: lem-dl-a1-lisse-extension-inertia).
Proof: pure dimension one bounds the dimension of the noetherian ambient curve by one.
Dimension does not increase on an open subscheme. The finite-type and separatedness
hypotheses of both schemes are precisely the fields of MiddleExtensionCurve. -/
theorem Scheme.MiddleExtensionCurve.lisseExtensionCurves {D : FiniteFieldDatum.{u}}
    (c : Scheme.MiddleExtensionCurve D) : IsCurve c.U.hom ∧ IsCurve c.C.hom := by
  sorry

/-- The existing curve structure on the dense open, derived rather than assumed.
Source: rem-dl-a1-conventions (blueprint: lem-dl-a1-lisse-extension-inertia). -/
instance Scheme.MiddleExtensionCurve.lisseExtensionCurveU {D : FiniteFieldDatum.{u}}
    (c : Scheme.MiddleExtensionCurve D) :
    IsCurve (c.U.left ↘ Spec (.of D.k₀)) := c.lisseExtensionCurves.1

/-- The existing curve structure on the ambient scheme, derived rather than assumed.
Source: rem-dl-a1-conventions (blueprint: lem-dl-a1-lisse-extension-inertia). -/
instance Scheme.MiddleExtensionCurve.lisseExtensionCurveC {D : FiniteFieldDatum.{u}}
    (c : Scheme.MiddleExtensionCurve D) :
    IsCurve (c.C.left ↘ Spec (.of D.k₀)) := c.lisseExtensionCurves.2

/-- The dense open of the geometrically connected ambient curve is nonempty.
Source: rem-dl-a1-conventions (blueprint: lem-dl-a1-lisse-extension-inertia).
Proof: geometric connectedness implies nonemptiness of C; density then forbids U
from being empty. -/
theorem Scheme.MiddleExtensionCurve.lisseExtensionNonempty {D : FiniteFieldDatum.{u}}
    (c : Scheme.MiddleExtensionCurve D) [GeometricallyConnected c.C.hom] :
    Nonempty c.U.left := by
  sorry

/-- The derived nonemptiness instance, with no new geometric assumption.
Source: rem-dl-a1-conventions (blueprint: lem-dl-a1-lisse-extension-inertia). -/
instance Scheme.MiddleExtensionCurve.lisseExtensionNonemptyInstance
    {D : FiniteFieldDatum.{u}} (c : Scheme.MiddleExtensionCurve D)
    [GeometricallyConnected c.C.hom] : Nonempty c.U.left := c.lisseExtensionNonempty

end AlgebraicGeometry

namespace AlgebraicGeometry.WeilSheaf

open WeilConjectures ProEtale

/-- A lisse Weil sheaf extends across a smooth curve's boundary exactly when each
boundary inertia group acts trivially. Under those conditions the ordinary direct
image is lisse; the morphism adjoint to every specified restriction isomorphism is
an isomorphism of Weil sheaves; two extensions have a unique compatible isomorphism.
Source: Tag 0BTD, Weil II (1.1.12), rem-dl-a1-conventions, second paragraph
(blueprint: lem-dl-a1-lisse-extension-inertia).
Proof:
1. Apply prop-wf-weil-sheaf-representation-equivalence to the generic stalk of F,
with its fundamentalRep of def-wf-fundamental-representation. Here M is the stalk
monodromy of cor-galois-lisse-representations: hM says it is the equivalence at B.t.
The boundary action is its restriction to the inertia subgroups of d-real-boundary.
2. By lem-dl-a1-weil-kernel-inertia, these subgroups generate the kernel of Weil
restriction as a closed normal subgroup. Continuity makes the representation kernel
closed. Thus trivial inertia is equivalent to killing the restriction kernel.
Clause (2) of lem-wf-dense-open-pi1-surjective makes restriction surjective and open:
on the open geometric subgroups it is a surjection of profinite groups, hence open.
Consequently the representation descends uniquely and continuously.
3. Use the representation equivalence on C to obtain G. The generic-stalk action of
j^*G is restriction of its Weil action, including the Frobenius operator; full
faithfulness on U gives the specified Weil isomorphism to F. Conversely any extension
kills the restriction kernel and hence every boundary inertia group.
4. The geometric curve is connected, noetherian and normal (lem-sc-smooth-normal).
Clause (3) of lem-wf-dense-open-pi1-surjective makes G -> j_*j^*G an isomorphism.
Compose with j_*alpha. Frobenius commutes with j and the unit is natural, so this
canonical adjoint is Weil-equivariant. Its target j_*F is therefore lisse.
5. By clause (4) of lem-wf-dense-open-pi1-surjective, restriction on lisse Weil
sheaves is fully faithful. The unique lift of alpha followed by alpha' inverse is
an isomorphism and is the unique isomorphism preserving the specified restrictions. -/
theorem lisse_extension_iff_trivial_inertia
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
    (c : Scheme.MiddleExtensionCurve D) [GeometricallyConnected c.C.hom]
    {WU : WeilGroup (c.U.left ↘ Spec (.of D.k₀))}
    {WC : WeilGroup (c.C.left ↘ Spec (.of D.k₀))}
    (b : BoundaryDatum c.j.left WU WC)
    (M : LisseMonodromy l (c.U.left ↘ Spec (.of D.k₀)).geometricFiber D.k₀)
    (B : WeilGroup.BasePointData WU) (hM : M.IsEquivalenceAt B.t)
    (F : WeilSheaf D.k₀ l c.U.left) (hF : F.IsLisse) :
    ((∃ G : WeilSheaf D.k₀ l c.C.left,
        G.IsLisse ∧ Nonempty ((WeilSheaf.upperStar c.j.left).obj G ≅ F)) ↔
      ∀ (x : ↥((Set.range c.j.left.base)ᶜ)) (g : b.inertia x)
        (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)),
        WeilGroup.canonicalFundamentalRep M B F hF g.1 v = v) ∧
    ((∀ (x : ↥((Set.range c.j.left.base)ᶜ)) (g : b.inertia x)
        (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)),
        WeilGroup.canonicalFundamentalRep M B F hF g.1 v = v) →
      ((curveWeilMiddleExtension c.j.left).obj F).IsLisse ∧
      (∀ (G : WeilSheaf D.k₀ l c.C.left), G.IsLisse →
        ∀ α : (WeilSheaf.upperStar c.j.left).obj G ≅ F,
        ∃ e : G ≅ (curveWeilMiddleExtension c.j.left).obj F,
          e.hom.hom.hom.f =
            (adicUpperStarLowerStarAdjunction l
              (Scheme.Hom.geometricFiberMap c.j.left
                (comp_over c.j.left (Spec (.of D.k₀))))).homEquiv G.carrier F.carrier
              α.hom.hom.hom.f) ∧
      (∀ (G G' : WeilSheaf D.k₀ l c.C.left), G.IsLisse → G'.IsLisse →
        ∀ (α : (WeilSheaf.upperStar c.j.left).obj G ≅ F)
          (α' : (WeilSheaf.upperStar c.j.left).obj G' ≅ F),
        ∃! e : G ≅ G', (WeilSheaf.upperStar c.j.left).map e.hom ≫ α'.hom = α.hom)) := by
  sorry

end AlgebraicGeometry.WeilSheaf
