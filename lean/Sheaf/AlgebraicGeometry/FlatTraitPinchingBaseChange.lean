module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.FerrandSchemePushout
import Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Flat trait pinching and arbitrary scalar extension

Source: Stacks Project, More on Morphisms, Tags 0E25 and 0ET0; Algebra, Tag 00HL;
More on Algebra, Tag 0AUW (blueprint: lem-sfb-flat-trait-pinching-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The algebraic clauses of a pinching chart, on its actual four coordinate rings.
The equalizer subalgebra is the matching-pairs ring with coordinatewise operations.
The equivalence after tensoring is specified on every pure tensor, so it is the canonical
comparison, not an arbitrary isomorphism. The scalar algebra may be the zero ring.
Source: Stacks Project, Tags 0E25, 00HL and 0AUW
(blueprint: lem-sfb-flat-trait-pinching-base-change). -/
def FlatTraitPinchingAlgebra
    (R Q A E D : Type u) [CommRing R] [CommRing Q] [CommRing A] [CommRing E] [CommRing D]
    (r : R →+* Q) (f : Q →+* A) (g : Q →+* E) (α : A →+* D) (β : E →+* D) : Prop :=
  letI : Algebra R Q := r.toAlgebra
  letI : Algebra R A := (f.comp r).toAlgebra
  letI : Algebra R E := (g.comp r).toAlgebra
  letI : Algebra R D := (α.comp (f.comp r)).toAlgebra
  Function.Injective (fun q : Q ↦ (f q, g q)) ∧
  Function.Exact (fun q : Q ↦ (f q, g q)) (fun p : A × E ↦ α p.1 - β p.2) ∧
  Function.Surjective (fun p : A × E ↦ α p.1 - β p.2) ∧
  Module.Flat R Q ∧
  ∃ (fa : Q →ₐ[R] A) (ga : Q →ₐ[R] E) (αa : A →ₐ[R] D) (βa : E →ₐ[R] D),
    fa.toRingHom = f ∧ ga.toRingHom = g ∧ αa.toRingHom = α ∧ βa.toRingHom = β ∧
    (∃ e : Q ≃ₐ[R] AlgHom.equalizer
        (αa.comp (AlgHom.fst R A E)) (βa.comp (AlgHom.snd R A E)),
      ∀ q : Q, (e q).val = (f q, g q)) ∧
    ∀ (R' : Type u) [CommRing R'] [Algebra R R'],
      ∃ e : Q ⊗[R] R' ≃ₐ[R] AlgHom.equalizer
          ((Algebra.TensorProduct.map αa (AlgHom.id R R')).comp
            (AlgHom.fst R (A ⊗[R] R') (E ⊗[R] R')))
          ((Algebra.TensorProduct.map βa (AlgHom.id R R')).comp
            (AlgHom.snd R (A ⊗[R] R') (E ⊗[R] R'))),
        ∀ (q : Q) (s : R'), (e (q ⊗ₜ[R] s)).val = (f q ⊗ₜ[R] s, g q ⊗ₜ[R] s)

/-- The pushout property on every open restriction, using the canonical pullback maps.
This packages precisely the open-compatibility clause of the pinching statement.
Source: Stacks Project, Tag 0E25, restriction-compatible construction
(blueprint: lem-sfb-flat-trait-pinching-base-change). -/
def PinchingPushoutOnOpens {Z X T P : Scheme.{u}}
    (i : Z ⟶ X) (j : Z ⟶ T) (a : X ⟶ P) (b : T ⟶ P)
    (h : i ≫ a = j ≫ b) : Prop :=
  ∀ V : P.Opens, IsPushout
    ((Over.pullback V.ι).map
      (Over.homMk i rfl : Over.mk (i ≫ a) ⟶ Over.mk a)).left
    ((Over.pullback V.ι).map
      (Over.homMk j h.symm : Over.mk (i ≫ a) ⟶ Over.mk b)).left
    (pullback.snd a V.ι) (pullback.snd b V.ι)

/-- Flat pinching over a discrete valuation ring is preserved by every scalar extension.
The cover uses the actual section rings Q, A, E and D, with their canonical maps.
The predicate on these rings includes the short exact sequence, flatness, matching-pairs
identification, and the canonical algebra comparison for every scalar algebra.
The final clause imposes the pushout universal property on every open after base change;
thus the chartwise identifications agree on arbitrary open restrictions.

Source: Stacks Project, More on Morphisms, Tags 0E25 and 0ET0; Algebra, Tag 00HL;
More on Algebra, Tag 0AUW (blueprint: lem-sfb-flat-trait-pinching-base-change).

Proof plan:
1. Finite j is integral (lem-weil-pbc-finite-iff-integral-lft). The affine open U
   contains each pinched fibre, so lem-sfb-ferrand-scheme-pushout applies. Uniqueness
   of colimits (def-weil-pbc-category-colimit) identifies its pushout with P over S.
   Transfer its simultaneous affine cover and its matching-pairs coordinate rings.
2. On a chart, Q maps injectively to A × E. Its image is the kernel of the difference
   map (x,y) ↦ α(x)-β(y). This map is onto by lifting d along the surjection α
   and using (x,0). This proves the displayed short exact sequence of R-modules.
3. By lem-weil-pbc-flat-morphism-affine-criterion, A, E and D are R-flat. Since R
   is a domain, A × E and its submodule Q are torsion-free. The DVR is a PID, so
   lem-weil-pbc-pid-torsion-free-module-flat makes Q flat. By
   lem-weil-pbc-flat-ring-map-iff-flat-affine each chart, and hence P, is flat.
4. Apply lem-weil-pbc-flat-quotient-tensor-injective to the exact sequence, with
   quotient D flat. Tensoring by arbitrary R' stays short exact; R' need not be flat.
5. Distribute tensor over A × E. The kernel of α⊗1-β⊗1 is exactly the matching-pairs
   ring. Exactness makes the canonical comparison bijective. Its pure-tensor formula
   preserves 1 and products, so it gives the asserted algebra equivalence.
6. By lem-weil-pbc-fibre-product-affine-spectra the base-changed chart has the tensor
   coordinate rings. The tensor of α stays surjective by lifting pure-tensor factors.
   Apply lem-sfb-affine-closed-pinching-pushout. The charts stay open by
   lem-weil-pbc-open-immersion-base-change, and cover the base-changed P.
7. On a principal open D(h), lem-sfb-ring-fibre-product-spectrum identifies the
   localized rings with the same matching-pairs construction. The tensor comparison
   commutes with restrictions since its two projections are the canonical tensor maps.
   By lem-weil-pbc-spec-localization-away-basic-open these opens refine chart overlaps.
   The local pushout maps therefore agree, and lem-weil-pbc-scheme-morphism-gluing
   glues them uniquely, proving the global and open-restricted pushout properties.
   For R'=0 all rings vanish and all schemes are empty, and the same argument applies.
-/
theorem flat_trait_pinching_base_change
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (Z X T P : Over (Spec (CommRingCat.of R)))
    (i : Z ⟶ X) (j : Z ⟶ T) (a : X ⟶ P) (b : T ⟶ P)
    [Flat Z.hom] [Flat X.hom] [Flat T.hom]
    [IsClosedImmersion i.left] [IsFinite j.left]
    (U : X.left.Opens) (hU : IsAffineOpen U) (hiU : Set.range i.left ⊆ U)
    (hs : IsPushout i.left j.left a.left b.left) :
    Flat P.hom ∧
    (∃ (ι : Type u) (W : ι → P.left.Opens), iSup W = ⊤ ∧ ∀ k : ι,
      IsAffineOpen (W k) ∧ IsAffineOpen (a.left ⁻¹ᵁ W k) ∧
      IsAffineOpen (b.left ⁻¹ᵁ W k) ∧ IsAffineOpen ((i.left ≫ a.left) ⁻¹ᵁ W k) ∧
      Function.Surjective (i.left.app (a.left ⁻¹ᵁ W k)).hom ∧
      FlatTraitPinchingAlgebra R Γ(P.left, W k) Γ(X.left, a.left ⁻¹ᵁ W k)
        Γ(T.left, b.left ⁻¹ᵁ W k) Γ(Z.left, (i.left ≫ a.left) ⁻¹ᵁ W k)
        (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ P.hom.appLE ⊤ (W k)
          (by simp)).hom)
        (a.left.app (W k)).hom (b.left.app (W k)).hom
        (i.left.app (a.left ⁻¹ᵁ W k)).hom
        (j.left.appLE (b.left ⁻¹ᵁ W k) ((i.left ≫ a.left) ⁻¹ᵁ W k)
          (le_of_eq (congrArg (fun f : Z.left ⟶ P.left ↦ f ⁻¹ᵁ W k) hs.w))).hom) ∧
    ∀ (R' : Type u) [CommRing R'] [Algebra R R'],
      ∃ h' : IsPushout
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).map i).left
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).map j).left
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).map a).left
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).map b).left,
      PinchingPushoutOnOpens
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).map i).left
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).map j).left
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).map a).left
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).map b).left h'.w := by
  sorry

end AlgebraicGeometry
