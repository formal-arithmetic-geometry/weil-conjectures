/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover

/-!
# Exactness from relative-flat tensor charts

Source: Stacks Project, Tags 00HL, 00CS, 01HV, 01I3, 01LN and 00E0.
(blueprint: lem-sfb-relative-flat-tensor-charts-sheaf-exact).
-/

@[expose] public section
set_option autoImplicit false

universe u w r a s l m n

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- Relative-flat quotient tensor charts give short exactness of module sheaves.
The chart identifications are additive equivalences with the scalar equation on pure
ring tensors; by additivity this says exactly that they are linear over A tensor_R S.
The principal-open equivalences extend restriction on denominator-one fractions. Their
arrow equations, written using the supplied chart equivalences, identify the arrows
with the localized displayed tensor arrows on every fraction.

Source: Stacks Project, Tags 00HL, 00CS, 01HV, 01I3, 01LN and 00E0.
(blueprint: lem-sfb-relative-flat-tensor-charts-sheaf-exact).

Proof:
1. Restrict the short exact A-module sequences to R. Apply
   lem-weil-pbc-flat-quotient-tensor-injective (00HL) to the flat last term N and
   arbitrary tensor factor S. Swap factors and use the two commuting squares to
   get short exactness on each Q. Neither A nor S must be flat.
2. By lem-weil-pbc-affine-open-section-vanishing-prime, D(c) is affine with ring B_c.
   Use lem-weil-pbc-quasi-coherent-affine-section-base-change (01LN) and
   lem-weil-pbc-localization-module-tensor (00DK) to identify sections with fractions.
   Naturality and linearity identify both arrows with localization of the tensor
   arrows. Apply lem-weil-pbc-localization-module-exact (00CS), including the pairs
   with zero endpoints, to get short exactness on D(c).
3. The principal-open basis from lem-weil-pbc-spec-localization-away-basic-open,
   transported by lem-weil-pbc-affine-open-section-vanishing-prime, gives u v = 0
   by sheaf uniqueness. Form the canonical lift F to ker v. Its target is
   quasi-coherent by lem-weil-pbc-quasi-coherent-module-kernel. Its section maps
   on Q are bijective by step 1, so lem-weil-pbc-quasi-coherent-iso-on-affine-cover
   makes it an isomorphism. Its composite with the kernel inclusion is u.
4. Lem-weil-pbc-quasicoherent-epi-affine-cover makes v epi. The kernel isomorphism
   makes u mono and identifies its image with ker v. These give short exactness
   by def-weil-pbc-exact-sequence. Kernel monicity gives canonicity. No finiteness
   is used, and zero rings, empty opens and the empty cover are included. -/
theorem relativeFlat_tensorCharts_sheaf_shortExact
    {Y : Scheme.{u}} (F G H : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] [H.IsQuasicoherent]
    (f : F ⟶ G) (g : G ⟶ H)
    (ι : Type w) (Q : ι → Y.Opens)
    (hcover : ⨆ i, Q i = ⊤) (haffine : ∀ i, IsAffineOpen (Q i))
    (R : ι → Type r) (A : ι → Type a) (S : ι → Type s)
    [∀ i, CommRing (R i)] [∀ i, CommRing (A i)] [∀ i, CommRing (S i)]
    [∀ i, Algebra (R i) (A i)] [∀ i, Algebra (R i) (S i)]
    (e : ∀ i, Γ(Y, Q i) ≃+* (A i ⊗[R i] S i))
    (L : ι → Type l) (M : ι → Type m) (N : ι → Type n)
    [∀ i, AddCommGroup (L i)] [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)]
    [∀ i, Module (A i) (L i)] [∀ i, Module (A i) (M i)] [∀ i, Module (A i) (N i)]
    [∀ i, Module (R i) (L i)] [∀ i, Module (R i) (M i)] [∀ i, Module (R i) (N i)]
    [∀ i, IsScalarTower (R i) (A i) (L i)]
    [∀ i, IsScalarTower (R i) (A i) (M i)]
    [∀ i, IsScalarTower (R i) (A i) (N i)]
    (p : ∀ i, L i →ₗ[A i] M i) (q : ∀ i, M i →ₗ[A i] N i)
    (hp : ∀ i, Function.Injective (p i))
    (hpq : ∀ i, Function.Exact (p i) (q i))
    (hq : ∀ i, Function.Surjective (q i)) [∀ i, Module.Flat (R i) (N i)]
    (eF : ∀ i, Γ(F, Q i) ≃+ (L i ⊗[R i] S i))
    (eG : ∀ i, Γ(G, Q i) ≃+ (M i ⊗[R i] S i))
    (eH : ∀ i, Γ(H, Q i) ≃+ (N i ⊗[R i] S i))
    (heF : ∀ (i : ι) (b : A i) (c : S i) (x : Γ(F, Q i)),
      eF i ((e i).symm (b ⊗ₜ[R i] c) • x) =
        b • (TensorProduct.comm (R i) (S i) (L i))
          (c • TensorProduct.comm (R i) (L i) (S i) (eF i x)))
    (heG : ∀ (i : ι) (b : A i) (c : S i) (x : Γ(G, Q i)),
      eG i ((e i).symm (b ⊗ₜ[R i] c) • x) =
        b • (TensorProduct.comm (R i) (S i) (M i))
          (c • TensorProduct.comm (R i) (M i) (S i) (eG i x)))
    (heH : ∀ (i : ι) (b : A i) (c : S i) (x : Γ(H, Q i)),
      eH i ((e i).symm (b ⊗ₜ[R i] c) • x) =
        b • (TensorProduct.comm (R i) (S i) (N i))
          (c • TensorProduct.comm (R i) (N i) (S i) (eH i x)))
    (hf : ∀ (i : ι) (x : Γ(F, Q i)),
      eG i (f.app (Q i) x) = ((p i).restrictScalars (R i)).rTensor (S i) (eF i x))
    (hg : ∀ (i : ι) (x : Γ(G, Q i)),
      eH i (g.app (Q i) x) = ((q i).restrictScalars (R i)).rTensor (S i) (eG i x)) :
    (∀ i, Function.Injective (f.app (Q i)) ∧
      Function.Exact (f.app (Q i)) (g.app (Q i)) ∧ Function.Surjective (g.app (Q i))) ∧
    (∀ (i : ι) (c : Γ(Y, Q i)),
      (Function.Injective (f.app (Y.basicOpen c)) ∧
        Function.Exact (f.app (Y.basicOpen c)) (g.app (Y.basicOpen c)) ∧
        Function.Surjective (g.app (Y.basicOpen c))) ∧
      ∃ dF : LocalizedModule (Submonoid.powers c) Γ(F, Q i) ≃+
          Γ(F, Y.basicOpen c),
      ∃ dG : LocalizedModule (Submonoid.powers c) Γ(G, Q i) ≃+
          Γ(G, Y.basicOpen c),
      ∃ dH : LocalizedModule (Submonoid.powers c) Γ(H, Q i) ≃+
          Γ(H, Y.basicOpen c),
        (∀ x : Γ(F, Q i),
          dF (LocalizedModule.mkLinearMap (Submonoid.powers c) Γ(F, Q i) x) =
            F.presheaf.map (homOfLE (Y.basicOpen_le c)).op x) ∧
        (∀ (b : Γ(Y, Q i)) (z : LocalizedModule (Submonoid.powers c) Γ(F, Q i)),
          dF (b • z) = Y.presheaf.map (homOfLE (Y.basicOpen_le c)).op b • dF z) ∧
        (∀ x : Γ(G, Q i),
          dG (LocalizedModule.mkLinearMap (Submonoid.powers c) Γ(G, Q i) x) =
            G.presheaf.map (homOfLE (Y.basicOpen_le c)).op x) ∧
        (∀ (b : Γ(Y, Q i)) (z : LocalizedModule (Submonoid.powers c) Γ(G, Q i)),
          dG (b • z) = Y.presheaf.map (homOfLE (Y.basicOpen_le c)).op b • dG z) ∧
        (∀ x : Γ(H, Q i),
          dH (LocalizedModule.mkLinearMap (Submonoid.powers c) Γ(H, Q i) x) =
            H.presheaf.map (homOfLE (Y.basicOpen_le c)).op x) ∧
        (∀ (b : Γ(Y, Q i)) (z : LocalizedModule (Submonoid.powers c) Γ(H, Q i)),
          dH (b • z) = Y.presheaf.map (homOfLE (Y.basicOpen_le c)).op b • dH z) ∧
        (∀ (x : L i ⊗[R i] S i) (t : Submonoid.powers c),
          f.app (Y.basicOpen c) (dF (LocalizedModule.mk ((eF i).symm x) t)) =
            dG (LocalizedModule.mk
              ((eG i).symm (((p i).restrictScalars (R i)).rTensor (S i) x)) t)) ∧
        (∀ (x : M i ⊗[R i] S i) (t : Submonoid.powers c),
          g.app (Y.basicOpen c) (dG (LocalizedModule.mk ((eG i).symm x) t)) =
            dH (LocalizedModule.mk
              ((eH i).symm (((q i).restrictScalars (R i)).rTensor (S i) x)) t))) ∧
    ∃ hfg : f ≫ g = 0,
      (ShortComplex.mk f g hfg).ShortExact ∧
      IsIso (kernel.lift g f hfg) ∧ kernel.lift g f hfg ≫ kernel.ι g = f := by
  sorry

end AlgebraicGeometry.Scheme.Modules
