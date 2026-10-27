/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.GeometricFiberFrobenius
public import WeilConjectures.AlgebraicGeometry.Morphisms.AbsoluteFrobenius
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Sheaf.AlgebraicGeometry.RelativeFrobeniusFinite
import Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyNoetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Flat.Localization
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Finite faithfully flat Frobenius of a smooth connected affine group

Source: Milne, Algebraic Groups (2017), 2.24--2.29, printed pp.46--49;
Stacks Project, Tags 0CCD, 0CCG and 01TX
(blueprint: lem-sfb-smooth-connected-group-frobenius-flat).

The target is the existing pullback along the absolute field Frobenius, with the
existing base-changed group operations. For an affine group with coordinate algebra
`C`, this is `Spec (C ⊗[k, a ↦ a^(p^r)] k)`, with its second-factor structure map.
The coordinate formula below uses the two pullback projections: their images are
`c ⊗ 1` and `1 ⊗ a`, whose product is `c ⊗ a`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- The canonical iterated relative Frobenius, viewed as a morphism over the field.
Its target is the base change along the `p ^ r`-power field Frobenius. This is the
existing `Scheme.relativeIterateFrobenius`, with its existing second-projection identity.
In affine coordinates it sends `c ⊗ a` to `a * c ^ (p ^ r)`.

Source: Milne 2.24--2.28, printed pp.46--48; Stacks Tag 0CCG
(blueprint: lem-sfb-smooth-connected-group-frobenius-flat). -/
noncomputable def groupRelativeIterateFrobenius
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : p.Prime)
    (G : Over (Spec (.of k))) (r : ℕ) :
    G ⟶ (Over.pullback ((Spec (.of k)).iterateFrobenius hp
      (Scheme.isOfCharacteristic_Spec (CharP.cast_eq_zero k p)) r)).obj G :=
  Over.homMk (Scheme.relativeIterateFrobenius hp
    (Scheme.isOfCharacteristic_Spec (CharP.cast_eq_zero k p)) r G.hom)
    (Scheme.relativeIterateFrobenius_snd hp
      (Scheme.isOfCharacteristic_Spec (CharP.cast_eq_zero k p)) r G.hom)

/-- For every positive iterate, the relative Frobenius of a smooth connected affine
finite-type group is a finite faithfully flat homomorphism, locally of finite presentation,
and is quasi-compact. The final clause gives its map on pure tensors in affine coordinates.
No commutativity, reductivity, or positive-dimensionality is assumed.

Source: Milne 2.26--2.29, printed pp.47--49, and Summary 1.71, printed p.28;
Stacks Tags 0CCD, 0CCG and 01TX
(blueprint: lem-sfb-smooth-connected-group-frobenius-flat).

Proof:
1. By `lem-pc-affine-finite-type-algebra`, the coordinate algebra `C` is finitely generated.
   The affine fibre-product calculation identifies the target with the Frobenius-twisted
   tensor algebra `D`. Its generators are `x_i ⊗ 1` for generators `x_i` of `C`.
   Smoothness makes `G` reduced (`sbc-lem-smooth-geometrically-reduced`), hence `C` reduced
   (`lem-weil-pbc-affine-scheme-reduced-iff`).
2. Algebraic closedness makes the field power map sigma bijective, with inverse beta.
   The tensor relations give a ring isomorphism `D ≃ C`, `c ⊗ a ↦ c * beta(a)`.
   The relative Frobenius map phi is this isomorphism followed by the power map on `C`.
   Reducedness makes phi injective. The calculations use
   `lem-weil-pbc-algebra-tensor-pushout-universal-property`.
3. The coordinate Hopf maps (`lem-sfb-affine-group-coordinate-hopf`) commute with phi:
   comultiplication commutes because powers commute with multiplication and finite sums;
   the counit and antipode commute for the same reason. Thus `lem-sfb-hopf-spectrum-functor`
   makes the canonical morphism a group homomorphism for the base-changed operations.
4. Apply `lem-sfb-reduced-target-dominant-group-flatness` to the injective Hopf map phi
   between finitely generated algebras, with reduced source `D`. It makes `C` faithfully
   flat over `D`; this uses neither commutativity of the group nor reductivity.
5. The two projections of the canonical map are absolute Frobenius and the structure map.
   Apply `lem-trf-relative-frobenius-finite` to the finite-type structure morphism.
6. Faithful flatness gives surjectivity by
   `lem-weil-pbc-faithfully-flat-surjective-spectrum`. Flatness is stalkwise: localize the
   flat module `C` at a prime, using `lem-weil-pbc-localization-module-exact`, then use
   `lem-weil-pbc-flat-over-localization` to pass from `D` to its prime localization.
   The local-ring identifications are `lem-weil-pbc-spec-domain-stalks-function-field` (1).
7. The target algebra `D` is Noetherian (`lem-wf-affine-noetherian-components`), so its
   spectrum is locally Noetherian (`pqf-def-locnoeth`). Finiteness implies finite
   presentation by `pqf-lem-finite-fp-locnoeth` and quasi-compactness by
   `lem-weil-pbc-affine-morphism-permanence` (3). Together with flatness and surjectivity
   these are precisely a quasi-compact fppf covering. The pure-tensor formula follows
   from the two projection identities and multiplicativity. Every step includes the
   trivial group and characteristic two. -/
theorem smoothConnectedGroup_relativeIterateFrobenius_finite_faithfullyFlat
    (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [CharP k p] (hp : p.Prime)
    (G : Over (Spec (.of k))) [GrpObj G] [IsAffine G.left] [ConnectedSpace G.left]
    [Smooth G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (r : ℕ) (hr : 1 ≤ r) :
    IsMonHom (groupRelativeIterateFrobenius k p hp G r) ∧
      IsFinite (groupRelativeIterateFrobenius k p hp G r).left ∧
      Flat (groupRelativeIterateFrobenius k p hp G r).left ∧
      Surjective (groupRelativeIterateFrobenius k p hp G r).left ∧
      LocallyOfFinitePresentation (groupRelativeIterateFrobenius k p hp G r).left ∧
      QuasiCompact (groupRelativeIterateFrobenius k p hp G r).left ∧
      ∀ (c : Γ(G.left, ⊤)) (a : k),
        (groupRelativeIterateFrobenius k p hp G r).left.appTop.hom
          ((pullback.fst G.hom ((Spec (.of k)).iterateFrobenius hp
            (Scheme.isOfCharacteristic_Spec (CharP.cast_eq_zero k p)) r)).appTop.hom c *
            (pullback.snd G.hom ((Spec (.of k)).iterateFrobenius hp
              (Scheme.isOfCharacteristic_Spec (CharP.cast_eq_zero k p)) r)).appTop.hom
              ((Scheme.ΓSpecIso (.of k)).inv.hom a)) =
          G.hom.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a) * c ^ (p ^ r) := by
  sorry

end AlgebraicGeometry
