/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! Support restriction for a commutative proper/open square.
Source: latest blueprint composition proof, normalized proper/open comparisons.
(blueprint: lem-zl-geometric-proper-support-restriction). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper

/-- In a commutative proper/open square, support restriction is invertible on the
stipulated geometric bounded constructible inputs.
Source: latest blueprint sk-thm-sf-comp-composition.proof.md, composition paragraph;
Stacks 0F7B, proper commutative-square case.
(blueprint: lem-zl-geometric-proper-support-restriction).

Proof: Form V = W ×_Z Y and write the induced map s : U → V. Its composite with
V → W is j, so s is open. Since V → Y is separated and its composite with s is
proper, s is proper. It is therefore closed as well as open. The clopen module
product decomposition, transported to internal modules and then degreewise to the
derived category, identifies J_s with zero insertion and hence with R_s. Fix the
comparison alpha_s : J_s → R_s to be the P_s ⊣ R_s adjunct of the inverse unit
P_s J_s → id; on clopen coordinates this is identity on U and zero on C, so it is
invertible. The candidate support isomorphism is explicitly the composite
P_i R_r J_j → P_i R_r J_t J_s → R_q P_t J_t J_s → R_q J_s → R_q R_s → R_p,
using inverse jComp, Cartesian restriction, the inverse open unit for t, alpha_s,
and rComp. To check normalization, transpose these
identifications through the specified adjunctions. The Cartesian restriction is the
recorded pullback-square mate, while the clopen coordinate unit and counit are the
inclusion and projection on U. The open triangle identity cancels the unit of j.
Thus this is precisely supportRestrictionComponent, which is invertible. No proper
base-change theorem, invertibility of Gamma, or compatibility with k is used. -/
theorem geometricProperSupportRestriction_isIso
    (F : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ F.p)
    {U W Y Z : SepFinType F.k}
    {j : U.obj.left ⟶ W.obj.left} {p : U.obj.left ⟶ Y.obj.left}
    {r : W.obj.left ⟶ Z.obj.left} {i : Y.obj.left ⟶ Z.obj.left}
    [IsOpenImmersion j] [IsOpenImmersion i] [QuasiCompact j] [QuasiCompact i]
    [IsProper p] [IsProper r] (sq : CommSq j p r i)
    (K : D (Profinite.padicAlgClRingObj ℓ) U.obj.left)
    (_hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.obj.left) K) :
    IsIso (supportRestrictionComponent (Profinite.padicAlgClRingObj ℓ) sq K) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
