/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.TensorProduct.Tower

import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.LinearAlgebra.InvariantBasisNumber

/-!
# Standard smooth affine charts for prescribed differential coordinates

Source: Stacks Project, morphisms.tex, Tags 01V7 and 02GU(8); algebra.tex, Tag 00T7(2);
schemes.tex, Tags 01HV and 01I2
(blueprint: lem-pur-coordinate-differentials-affine-chart).

The auxiliary predicate expands the conclusion, installing only canonical scalar structures.
A `Presentation` contains the polynomial quotient isomorphism `quotientEquiv`;
`SubmersivePresentation` additionally contains the invertible Jacobian minor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

/-- The full affine-chart conclusion, packaged to install its canonical scalar structures.
Here `n = r + d` by the variable indexing. `P.map` selects the first `r` variables, and
`Fin.natAdd r` selects the last `d`. The two presentations encode precisely the quotient
isomorphisms, including their action on variables. The linear map `g` is characterized on
all differentials, which generate the Kähler module, and `Φ` on every pure tensor. Thus these
are the germ map and its canonical base change, rather than unspecified isomorphisms.
Source: Stacks Project, Tags 01V7, 00T7(2), 01HV and 02GU(8)
(blueprint: lem-pur-coordinate-differentials-affine-chart). -/
def HasCoordinateDifferentialAffineChart
    (k : Type u) [Field k] (U : Scheme.{u}) [U.Over (Spec (.of k))]
    (x : U) (d : ℕ) (h : Fin d → Γ(U, ⊤))
    (W : U.Opens) (hW : IsAffineOpen W) (hx : x ∈ W) : Prop :=
  let res : Γ(U, ⊤) →+* Γ(U, W) := (U.presheaf.map (homOfLE le_top).op).hom
  letI : Algebra k Γ(U, W) :=
    ((ΓSpecIso (.of k)).inv ≫ (U ↘ Spec (.of k)).appTop ≫
      U.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  letI : Algebra Γ(U, W) (IsLocalRing.ResidueField (U.presheaf.stalk x)) :=
    (U.presheaf.germ W x hx ≫ U.residue x).hom.toAlgebra
  letI : Module Γ(U, W)
      ((RingedSpace.moduleStalkFunctor U.toRingedSpace x).obj
        (U ↘ Spec (.of k)).relativeDifferentials) :=
    Module.compHom _ (U.presheaf.germ W x hx).hom
  letI : Algebra (MvPolynomial (ULift.{u} (Fin d)) k) Γ(U, W) :=
    (MvPolynomial.aeval (fun j : ULift.{u} (Fin d) ↦ res (h j.down))).toRingHom.toAlgebra
  ∃ (r : ℕ) (P : Algebra.SubmersivePresentation k Γ(U, W) (Fin (r + d)) (Fin r)),
    P.map = Fin.castAdd d ∧
    (∃ ε : (hW.primeIdealOf ⟨x, hx⟩).asIdeal.ResidueField ≃+*
        IsLocalRing.ResidueField (U.presheaf.stalk x),
      ∀ a : Γ(U, W), ε (algebraMap _ _ a) =
        (U.residue x) (U.presheaf.germ W x hx a)) ∧
    (∃ (g : KaehlerDifferential k Γ(U, W) →ₗ[Γ(U, W)]
          ((RingedSpace.moduleStalkFunctor U.toRingedSpace x).obj
            (U ↘ Spec (.of k)).relativeDifferentials))
        (Φ : (IsLocalRing.ResidueField (U.presheaf.stalk x) ⊗[Γ(U, W)]
            KaehlerDifferential k Γ(U, W)) ≃ₗ[IsLocalRing.ResidueField (U.presheaf.stalk x)]
          (IsLocalRing.ResidueField (U.presheaf.stalk x) ⊗[U.presheaf.stalk x]
            ((RingedSpace.moduleStalkFunctor U.toRingedSpace x).obj
              (U ↘ Spec (.of k)).relativeDifferentials))),
      (∀ a : Γ(U, W), g (KaehlerDifferential.D k Γ(U, W) a) =
        (U ↘ Spec (.of k)).relativeDifferentials.presheaf.germ W x hx
          ((U ↘ Spec (.of k)).relativeDifferentialsDerivation.d a)) ∧
      (∀ (ω : KaehlerDifferential k Γ(U, W))
          (c : IsLocalRing.ResidueField (U.presheaf.stalk x)),
        Φ (c ⊗ₜ[Γ(U, W)] ω) = c ⊗ₜ[U.presheaf.stalk x] g ω) ∧
      (∀ j : Fin d, Φ (1 ⊗ₜ[Γ(U, W)] KaehlerDifferential.D k Γ(U, W) (res (h j))) =
        TensorProduct.tmul (U.presheaf.stalk x)
          (N := (RingedSpace.moduleStalkFunctor U.toRingedSpace x).obj
            (U ↘ Spec (.of k)).relativeDifferentials)
          (1 : IsLocalRing.ResidueField (U.presheaf.stalk x))
          ((U ↘ Spec (.of k)).relativeDifferentials.presheaf.germ ⊤ x trivial
            ((U ↘ Spec (.of k)).relativeDifferentialsDerivation.d (h j))))) ∧
    (∃ b : Module.Basis (Fin d) (IsLocalRing.ResidueField (U.presheaf.stalk x))
        (IsLocalRing.ResidueField (U.presheaf.stalk x) ⊗[Γ(U, W)]
          KaehlerDifferential k Γ(U, W)),
      ∀ j : Fin d, b j = 1 ⊗ₜ[Γ(U, W)]
        KaehlerDifferential.D k Γ(U, W) (P.val (Fin.natAdd r j))) ∧
    (∃ (H : Fin d → MvPolynomial (Fin (r + d)) k)
        (G : Algebra.Presentation (MvPolynomial (ULift.{u} (Fin d)) k) Γ(U, W)
          (Fin (r + d)) (Fin r ⊕ Fin d)),
      (∀ j : Fin d, MvPolynomial.aeval P.val (H j) = res (h j)) ∧
      G.val = P.val ∧
      (∀ i : Fin r, G.relation (Sum.inl i) =
        MvPolynomial.map (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin d)) k)
          (P.relation i)) ∧
      (∀ j : Fin d, G.relation (Sum.inr j) =
        MvPolynomial.map (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin d)) k)
          (H j) - MvPolynomial.C (MvPolynomial.X (ULift.up j)))) ∧
    Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (fun j : ULift.{u} (Fin d) ↦ res (h j.down))).toRingHom) ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin d)) (.of k)).inv =
      hW.fromSpec ≫ AffineSpace.homOfVector (U ↘ Spec (.of k))
        (fun j : ULift.{u} (Fin d) ↦ h j.down)

/-- Prescribed differential coordinates admit a standard smooth affine chart, its canonical
cotangent-fibre comparison, and the graph presentation over their coordinate polynomial ring.
Source: Stacks Project, morphisms.tex, Tags 01V7 and 02GU(8); algebra.tex, Tag 00T7(2)
(blueprint: lem-pur-coordinate-differentials-affine-chart).

Proof:
1. Apply `lem-weil-pbc-smooth-locally-standard-smooth` at `x`. The target affine open is all
   of `Spec k`. Unpack the standard smooth presentation on the resulting affine open `W`.
2. `lem-weil-pbc-affine-open-stalk-localization` identifies the local ring with `A_q` and
   its residue field with `κ(q)`. The affine description of the relative differential sheaf
   and `lem-weil-pbc-spec-tilde-stalk-localization` identify its stalk with `(Ω[A/k])_q`,
   sending the germ of a differential to its fraction with denominator one.
3. The germ map induces `Φ`. Its inverse sends `(ω/s) ⊗ λ` to `ω ⊗ λ/s̄`. Denominators
   outside `q` have nonzero residue. The fraction equivalence relation is respected after
   dividing by the residues of the denominators and a clearing factor. This formula is
   additive, balanced over `A_q`, and inverse on pure tensors. Derivations are compatible.
4. `lem-weil-pbc-standard-smooth-kahler-basis` gives the basis of the last `n-r`
   differentials. Base change preserves the coordinate maps and their reconstruction
   identity. Compare this residue-field basis through `Φ` with the given length-`d` basis;
   `lem-sfb-commutative-ring-invariant-basis-number` gives `n-r=d`. Reindex with `n=r+d`.
5. Choose polynomial lifts `H_j` by surjectivity of the presentation. Evaluation kills the
   graph relations `F_i,H_j-T_j`, giving the map from the graph quotient to `A`. Conversely,
   the classes of `y_b` kill the original relations, giving the inverse through the original
   quotient isomorphism. It is linear over `R` since `H_j(y)=T_j`. Both composites fix
   every generator, hence are identities by the polynomial universal property.
6. `lem-weil-pbc-spec-map-global-sections` identifies the coordinate pullbacks with `h_j|W`.
   The polynomial universal property and affine spectrum correspondence identify this
   spectrum morphism with the restriction of the prescribed coordinate morphism. -/
theorem exists_coordinate_differentials_affine_chart
    (k : Type u) [Field k] (U : Scheme.{u}) [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [Smooth (U ↘ Spec (.of k))] (x : U) (d : ℕ) (h : Fin d → Γ(U, ⊤))
    (hbasis : ∃ b : Module.Basis (Fin d) (IsLocalRing.ResidueField (U.presheaf.stalk x))
        (IsLocalRing.ResidueField (U.presheaf.stalk x) ⊗[U.presheaf.stalk x]
          ((RingedSpace.moduleStalkFunctor U.toRingedSpace x).obj
            (U ↘ Spec (.of k)).relativeDifferentials)),
      ∀ j : Fin d, b j = TensorProduct.tmul (U.presheaf.stalk x)
        (N := (RingedSpace.moduleStalkFunctor U.toRingedSpace x).obj
          (U ↘ Spec (.of k)).relativeDifferentials)
        (1 : IsLocalRing.ResidueField (U.presheaf.stalk x))
        ((U ↘ Spec (.of k)).relativeDifferentials.presheaf.germ ⊤ x trivial
          ((U ↘ Spec (.of k)).relativeDifferentialsDerivation.d (h j)))) :
    ∃ (W : U.Opens) (hW : IsAffineOpen W) (hx : x ∈ W),
      HasCoordinateDifferentialAffineChart k U x d h W hW hx := by
  sorry

end AlgebraicGeometry.Scheme
