module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.PQFCohomology

/-! # Vanishing of the first Hodge differential in characteristic zero

Source: Popa, Kodaira dimension of algebraic varieties, proof of Theorem 1.6.6,
pp. 26–27; Stacks Project, Tags 01UM and 01F1.
(blueprint: lem-sfb-hodge-first-differential-zero)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000 in
-- Scalar restriction and the unit module need extra definitional-equality elaboration.
/-- The universal differential as a morphism of sheaves of vector spaces over the base field.
Its components are the existing universal derivations, with scalars restricted to the field.
Source: Popa, proof of Theorem 1.6.6, pp. 26–27; Stacks, Tag 01UM.
(blueprint: lem-sfb-hodge-first-differential-zero). -/
noncomputable def fieldLinearUniversalDifferential {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) :
    scalarSheaf f (SheafOfModules.unit X.ringCatSheaf) ⟶
      scalarSheaf f f.relativeDifferentials :=
  ⟨{ app := fun U ↦
       letI : Module k ((SheafOfModules.unit X.ringCatSheaf).val.obj U) :=
         Module.compHom _ (scalarMap f U.unop)
       letI : Module k (f.relativeDifferentials.val.obj U) :=
         Module.compHom _ (scalarMap f U.unop)
       ModuleCat.ofHom
        (X := scalarObj f (SheafOfModules.unit X.ringCatSheaf) U)
        (Y := scalarObj f f.relativeDifferentials U)
        { toFun := fun a : scalarObj f (SheafOfModules.unit X.ringCatSheaf) U ↦
            (f.relativeDifferentialsDerivation.d a : scalarObj f f.relativeDifferentials U)
          map_add' := fun a b ↦ f.relativeDifferentialsDerivation.d.map_add a b
          map_smul' := fun r a ↦ by
            change X.presheaf.obj U at a
            change f.relativeDifferentialsDerivation.d (scalarMap f U.unop r * a) =
              scalarMap f U.unop r • f.relativeDifferentialsDerivation.d a
            rw [f.relativeDifferentialsDerivation.d_mul]
            have h : f.relativeDifferentialsDerivation.d (scalarMap f U.unop r) = 0 := by
              have hz := f.relativeDifferentialsDerivation.d_app_app ⊤
                ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)
              change f.relativeDifferentialsDerivation.d
                (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)) = 0 at hz
              have hn := f.relativeDifferentialsDerivation.d_map
                (homOfLE (le_top (a := U.unop))).op
                (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r))
              change f.relativeDifferentialsDerivation.d (scalarMap f U.unop r) =
                f.relativeDifferentials.val.map (homOfLE (le_top (a := U.unop))).op
                  (f.relativeDifferentialsDerivation.d
                    (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r))) at hn
              exact hn.trans ((congrArg
                (fun z ↦ f.relativeDifferentials.val.map
                  (homOfLE (le_top (a := U.unop))).op z) hz).trans (map_zero _))
            rw [h, smul_zero, add_zero] }
     naturality := fun U V i ↦ by
       ext a
       change f.relativeDifferentialsDerivation.d (X.presheaf.map i a) =
         f.relativeDifferentials.val.map i (f.relativeDifferentialsDerivation.d a)
       exact f.relativeDifferentialsDerivation.d_map i a }⟩

/-- The induced map on ordinary module-sheaf cohomology, formed in vector sheaves.
The existing scalar cohomology/Ext equivalences identify the two cohomology theories;
postcomposition with the actual field-linear universal differential is transported through
these canonical equivalences. No O-linear map is used.
Source: Popa, proof of Theorem 1.6.6, pp. 26–27; Stacks, Tag 01F1.
(blueprint: lem-sfb-hodge-first-differential-zero). -/
noncomputable def fieldLinearUniversalDifferentialCohomology
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (q : ℕ) :
    scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) q →+
      scalarCohomology f f.relativeDifferentials q := by
  letI : HasExt.{u + 1} (KSheaf X k) := HasExt.standard (KSheaf X k)
  letI : MonoidalCategory (KSheaf X k) := Sheaf.monoidalCategory _ _
  exact (scalarCohomologyExtEquiv f f.relativeDifferentials q).symm.toAddMonoidHom.comp
    (((Abelian.Ext.mk₀ (fieldLinearUniversalDifferential f)).postcomp
      (𝟙_ (KSheaf X k)) (add_zero q)).comp
        (scalarCohomologyExtEquiv f (SheafOfModules.unit X.ringCatSheaf) q).toAddMonoidHom)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The universal F-linear derivation induces zero on cohomology in every degree.
The map is formed in vector sheaves and transported to ordinary module cohomology
by the canonical scalar cohomology comparison. No connectedness, geometric integrality,
or embedding of F into the complex numbers is assumed.

Source: Popa, proof of Theorem 1.6.6, pp. 26–27, and section 1.6, p. 22.
(blueprint: lem-sfb-hodge-first-differential-zero).

Proof:
1. By lem-sfb-smooth-projective-complex-field-model descend the smooth projective
scheme to a finitely generated subfield k of F admitting an embedding into C.
Let Y be the complex base change of this model X₀. Neither connectedness nor
geometric integrality is needed, and the empty scheme is allowed.
2. For each class in H^q(Y,O), use lem-sfb-algebraic-dolbeault-derivative-comparison
and lem-sfb-projective-harmonic-representatives to choose a harmonic (0,q)-form α.
It is d-closed. Its partial and bar-partial derivatives have distinct types,
so partial α = 0. The comparison sends H^q(d)([α]) to [(-1)^q partial α] = 0.
Injectivity of the comparison gives H^q(Y,d) = 0, component by component.
3. Apply lem-sfb-derivation-cohomology-scalar-square for k → C. It identifies
H^q(X₀,d) tensored with C with the zero map just obtained. Scalar extension
along a field embedding detects zero: a nonzero image vector has a coordinate
functional with value 1, contradicting its tensor with 1 being zero.
4. Apply the same scalar square for k → F. The source comparison is surjective,
so H^q(X₀ ×_k F,d) = 0. Transport along its model isomorphism with W; the
universal property identifies the derivations on affine charts. Functoriality
of derived global sections identifies the cohomology maps. This holds for
every q, without choosing any embedding of F into C. -/
theorem hodge_first_differential_zero (F : Type u) [Field F] [CharZero F]
    (W : Scheme.{u}) (f : W ⟶ Spec (CommRingCat.of F)) [Smooth f] [IsProjective f]
    (q : ℕ) :
    AlgebraicGeometry.Scheme.Modules.fieldLinearUniversalDifferentialCohomology f q = 0 := by
  sorry

end AlgebraicGeometry

