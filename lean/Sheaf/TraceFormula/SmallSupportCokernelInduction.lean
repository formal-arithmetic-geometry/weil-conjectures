module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Pi
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.CoherentFiniteType

import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Localization
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.AssociatedSectionsLocalize

/-!
# Smaller-support induction for the cokernel of a finite free submodule

Source: Stacks Project, `flat.tex`, Tag 05I5, first proof, the passage from the
smaller-support cokernel to the middle module
(blueprint: lem-trf-small-support-cokernel-induction).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The closed-fibre module, written as the quotient by the extended maximal ideal.
Source: Stacks Project, Tag 05I5, first proof, `Q/mQ`.
(blueprint: lem-trf-small-support-cokernel-induction). -/
abbrev smallSupportClosedFibre (A B M : Type u) [CommRing A] [CommRing B]
    [IsLocalRing A] [Algebra A B] [AddCommGroup M] [Module B M] :=
  M ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B M))

/-- The actual tensor-product ring after localizing a pointed affine base.
Source: Stacks Project, Tag 05I5, first proof, `B ⊗[A] O_{T,t}`.
(blueprint: lem-trf-small-support-cokernel-induction). -/
abbrev smallSupportBaseRing (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (C : CommAlgCat.{u} A) (t : PrimeSpectrum C) :=
  B ⊗[A] Localization.AtPrime t.asIdeal

/-- Finite presentation and relative flatness of the associated sheaf on an actual open.
Source: Stacks Project, Tag 05I5, first proof, the open neighbourhood supplied by induction.
(blueprint: lem-trf-small-support-cokernel-induction). -/
def smallSupportSheafGoodOpen {A B M : Type u} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module B M] (φ : A →+* B) (U : (Spec (.of B)).Opens) : Prop :=
  SheafOfModules.IsFinitePresentation
      ((Scheme.Modules.restrictFunctor U.ι).obj (tilde (ModuleCat.of B M))) ∧
    Scheme.Modules.IsFlatOver
      ((Scheme.Modules.restrictFunctor U.ι).obj (tilde (ModuleCat.of B M)))
      (U.ι ≫ Spec.map (CommRingCat.ofHom φ))

/-- Finite presentation and base-flatness of the actual localized module.
Source: Stacks Project, Tag 05I5, first proof, the properties of `Q'_g` and `N'_g`.
(blueprint: lem-trf-small-support-cokernel-induction). -/
def smallSupportModuleGoodPrincipal {A B M : Type u} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module B M] (φ : A →+* B) (g : B) : Prop :=
  Module.FinitePresentation (Localization.Away g) (LocalizedModule.Away g M) ∧
    @Module.Flat A (LocalizedModule.Away g M) _ _ (Module.compHom _ φ)

/-- The two module properties on a principal open, together with their associated-sheaf form.
Source: Stacks Project, Tag 05I5, first proof, the principal-open shrinking.
(blueprint: lem-trf-small-support-cokernel-induction). -/
def smallSupportGoodPrincipal {A B M : Type u} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module B M] (φ : A →+* B) (g : B) : Prop :=
  smallSupportModuleGoodPrincipal (M := M) φ g ∧
    smallSupportSheafGoodOpen (M := M) φ (PrimeSpectrum.basicOpen g)

/-- The canonical arrow between localizations of modules, sending `m/s` to `f(m)/s`.
Source: Stacks Project, Tag 05I5, first proof, exact localization.
(blueprint: lem-trf-small-support-cokernel-induction). -/
noncomputable def smallSupportAwayMap {B M N : Type u} [CommRing B]
    [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]
    (f : M →ₗ[B] N) (g : B) :
    LocalizedModule.Away g M →ₗ[B] LocalizedModule.Away g N :=
  IsLocalizedModule.map (Submonoid.powers g)
    (LocalizedModule.mkLinearMap _ _) (LocalizedModule.mkLinearMap _ _) f

/-- The localization of a map from a finite free module, on its standard basis.
Source: Stacks Project, Tag 05I5, first proof, the localized finite free submodule.
(blueprint: lem-trf-small-support-cokernel-induction). -/
noncomputable def smallSupportAwayFreeMap {B N : Type u} [CommRing B]
    [AddCommGroup N] [Module B N] {r : ℕ} (α : (Fin r → B) →ₗ[B] N) (g : B) :
    (Fin r → Localization.Away g) →ₗ[Localization.Away g] LocalizedModule.Away g N :=
  (Pi.basisFun (Localization.Away g) (Fin r)).constr (Localization.Away g)
    (fun i ↦ LocalizedModule.mk (α (Pi.single i 1)) 1)

/-- The canonical localized arrow: apply tensor base change and then localization.
Source: Stacks Project, Tag 05I5, first proof, localization of the short exact sequence.
(blueprint: lem-trf-small-support-cokernel-induction). -/
noncomputable def smallSupportLocalizedMap {B R M N : Type u} [CommRing B] [CommRing R]
    [Algebra B R] [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]
    (f : M →ₗ[B] N) (g : R) :
    LocalizedModule.Away g (R ⊗[B] M) →ₗ[R] LocalizedModule.Away g (R ⊗[B] N) :=
  smallSupportAwayMap (f.baseChange R) g

/-- The canonical arrow out of the localized free module, specified on its standard basis.
Source: Stacks Project, Tag 05I5, first proof, the arrow `(B'_g)^r → N'_g`.
(blueprint: lem-trf-small-support-cokernel-induction). -/
noncomputable def smallSupportLocalizedFreeMap {B R N : Type u} [CommRing B] [CommRing R]
    [Algebra B R] [AddCommGroup N] [Module B N] {r : ℕ}
    (α : (Fin r → B) →ₗ[B] N) (g : R) :
    (Fin r → Localization.Away g) →ₗ[Localization.Away g]
      LocalizedModule.Away g (R ⊗[B] N) :=
  (Pi.basisFun (Localization.Away g) (Fin r)).constr (Localization.Away g)
    (fun i ↦ LocalizedModule.mk (1 ⊗ₜ[B] α (Pi.single i 1)) 1)

/-- The open-neighbourhood conclusion used in the smaller-support induction hypothesis.
The local ring of `Spec C` at `t` is represented by its canonical localization `C_t`.
Source: Stacks Project, Tag 05I5, first proof, the induction hypothesis applied to a module.
(blueprint: lem-trf-small-support-cokernel-induction). -/
def smallSupportEtaleNeighborhood {A B M : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [Algebra A B] [AddCommGroup M] [Module B M]
    (q : PrimeSpectrum B) : Prop :=
  ∃ (C : CommAlgCat.{u} A) (t : PrimeSpectrum C),
    Etale (Spec.map (CommRingCat.ofHom (algebraMap A C))) ∧
    (Spec.map (CommRingCat.ofHom (algebraMap A C))) t = IsLocalRing.closedPoint A ∧
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A C))).residueFieldMap t) ∧
    ∃ (U : (Spec (.of (smallSupportBaseRing A B C t))).Opens)
      (q' : PrimeSpectrum (smallSupportBaseRing A B C t)),
      PrimeSpectrum.comap (algebraMap B (smallSupportBaseRing A B C t)) q' = q ∧
      q' ∈ U ∧ smallSupportSheafGoodOpen
        (M := smallSupportBaseRing A B C t ⊗[B] M)
        (Algebra.TensorProduct.includeRight (R := A) (A := B)
          (B := Localization.AtPrime t.asIdeal)).toRingHom U

/-- The full principal-open conclusion, with the canonical localized short exact sequence.
The tensor `B' ⊗[B] M` represents `M ⊗[A] A'` through tensor associativity and symmetry.
Source: Stacks Project, Tag 05I5, first proof, the cokernel induction and extension argument.
(blueprint: lem-trf-small-support-cokernel-induction). -/
def smallSupportCokernelConclusion {A B N Q : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [Algebra A B] [AddCommGroup N] [AddCommGroup Q]
    [Module B N] [Module B Q] {r : ℕ} (α : (Fin r → B) →ₗ[B] N)
    (β : N →ₗ[B] Q) (q : PrimeSpectrum B) : Prop :=
  ∃ (C : CommAlgCat.{u} A) (t : PrimeSpectrum C),
    Etale (Spec.map (CommRingCat.ofHom (algebraMap A C))) ∧
    (Spec.map (CommRingCat.ofHom (algebraMap A C))) t = IsLocalRing.closedPoint A ∧
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A C))).residueFieldMap t) ∧
    ∃ (q' : PrimeSpectrum (smallSupportBaseRing A B C t))
      (g : smallSupportBaseRing A B C t),
      PrimeSpectrum.comap (algebraMap B (smallSupportBaseRing A B C t)) q' = q ∧
      (∀ p : PrimeSpectrum (smallSupportBaseRing A B C t),
        PrimeSpectrum.comap (algebraMap B (smallSupportBaseRing A B C t)) p = q → p = q') ∧
      g ∉ q'.asIdeal ∧
      smallSupportModuleGoodPrincipal (M := smallSupportBaseRing A B C t ⊗[B] Q)
        (Algebra.TensorProduct.includeRight (R := A) (A := B)
          (B := Localization.AtPrime t.asIdeal)).toRingHom g ∧
      smallSupportGoodPrincipal (M := smallSupportBaseRing A B C t ⊗[B] N)
        (Algebra.TensorProduct.includeRight (R := A) (A := B)
          (B := Localization.AtPrime t.asIdeal)).toRingHom g ∧
      Function.Injective (smallSupportLocalizedFreeMap α g) ∧
      Function.Exact (smallSupportLocalizedFreeMap α g) (smallSupportLocalizedMap β g) ∧
      Function.Surjective (smallSupportLocalizedMap β g)

/-- Smaller-support induction for the cokernel of a universally injective finite free map.

Source: Stacks Project, `flat.tex`, Tag 05I5, first proof, last paragraph.
(blueprint: lem-trf-small-support-cokernel-induction).

Proof:
1. If the localized closed-fibre cokernel vanishes, Nakayama over `B_q` gives `Q_q = 0`.
   Choose finite generators of `Q` and multiply denominators killing them. The resulting
   `g` avoids `q`, and `Q_g = 0`; the identity elementary etale neighbourhood suffices.
   Uses lem-weil-pbc-localization-module-exact, lem-weil-pbc-nakayama-jacobson.
2. Otherwise apply the smaller-support hypothesis to `Q`. The one-step pointed etale
   local-tower result identifies the fibre over `q` with `Spec kappa(q)`, giving uniqueness
   of `q'`. Choose a principal open containing `q'` inside the supplied open. Associated
   sections are localizations, so affine finite presentation and relative flatness give
   the two desired properties of `Q'_g`.
   Uses lem-trf-pointed-etale-local-tower-realization,
   lem-weil-pbc-spec-localization-away-basic-open, pqf-lem-associated-sections-localize,
   lem-weil-pbc-quasi-coherent-finite-type-affine, def-pc-scheme-module-flat-over.
3. Smoothness makes `B` flat over `A`. Base change and localization make `B'_g` flat over
   `A'`, hence also its finite free power (including rank zero).
   Uses lem-pc-smooth-flat, lem-pc-affine-sections-flat-over-base,
   lem-weil-pbc-flat-module-base-change, lem-pc-affine-flat-module-localization-preserves-flatness.
4. Tensor right exactness and universal injectivity give the base-changed exact sequence.
   Exact localization gives the displayed sequence, with the canonical maps on fractions.
   It remains universally injective over `A'`: tensor associativity reduces this to the
   hypothesis over `A`, and localization is exact.
   Uses lem-weil-pbc-tensor-right-exact, lem-weil-pbc-localization-module-exact.
5. The kernel of the surjection to `Q'_g` is the injected finite free module, hence is
   finitely presented. The kernel criterion then proves finite presentation of `N'_g`.
   Uses lem-trf-module-finite-presentation-of-kernel, def-sc-finitely-presented-module.
6. For an injection of `A'`-modules, tensor the short exact sequence. An element killed
   in the middle maps to zero on the right by flatness of `Q'_g`, hence lifts from the
   free term. Universal injectivity in the lower row and flatness of the free term kill
   this lift. This proves flatness of `N'_g` by the injection criterion.
   Uses lem-weil-pbc-tensor-right-exact, def-weil-pbc-flat-ring-map.
7. Affine finite presentation gives finite presentation of the associated sheaf on `D(g)`.
   Its stalks are localizations of `N'_g`, flat over `A'` and then over the corresponding
   localized base. The stalk criterion gives relative flatness.
   Uses pqf-lem-associated-sections-localize, lem-weil-pbc-quasi-coherent-finite-type-affine,
   lem-pc-affine-flat-module-localization-preserves-flatness, lem-weil-pbc-flat-over-localization,
   lem-weil-pbc-spec-tilde-stalk-localization, lem-weil-pbc-spec-domain-stalks-function-field.
-/
theorem exists_smallSupport_cokernel_induction
    {A B N Q : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
    [AddCommGroup N] [AddCommGroup Q] [Module B N] [Module B Q]
    [Module A N] [IsScalarTower A B N] [Module.Finite B N] [Module.Finite B Q]
    (n r : ℕ)
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    (hgeom : ∀ (p : PrimeSpectrum A) (K : Type (max u v)) [Field K] [Algebra A K]
      (ι : p.asIdeal.ResidueField →+* K),
      algebraMap A K = ι.comp (algebraMap A p.asIdeal.ResidueField) → IsDomain (K ⊗[A] B))
    (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap (algebraMap A B) q = IsLocalRing.closedPoint A)
    (α : (Fin r → B) →ₗ[B] N) (β : N →ₗ[B] Q)
    (hinj : Function.Injective α) (hexact : Function.Exact α β)
    (hsurj : Function.Surjective β)
    (hui : ∀ (L : Type (max u v)) [AddCommGroup L] [Module A L],
      Function.Injective ((α.restrictScalars A).lTensor L))
    (hflat : @Module.Flat A (LocalizedModule q.asIdeal.primeCompl Q) _ _
      (Module.compHom _ (algebraMap A B)))
    (hdim : q ∉ Module.support B (smallSupportClosedFibre A B Q) ∨
      ∃ h : q ∈ Module.support B (smallSupportClosedFibre A B Q),
        topologicalKrullDimAt (⟨q, h⟩ : Module.support B (smallSupportClosedFibre A B Q)) <
          (n : WithBot ℕ∞))
    (hind : ∀ (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M],
      @Module.Flat A (LocalizedModule q.asIdeal.primeCompl M) _ _
        (Module.compHom _ (algebraMap A B)) →
      ∀ h : q ∈ Module.support B (smallSupportClosedFibre A B M),
        topologicalKrullDimAt (⟨q, h⟩ : Module.support B (smallSupportClosedFibre A B M)) <
          (n : WithBot ℕ∞) → smallSupportEtaleNeighborhood (A := A) (M := M) q) :
    smallSupportCokernelConclusion (A := A) α β q := by
  sorry

/-- In the zero-fibre case the identity base suffices, without any induction hypothesis.

Source: Stacks Project, Tag 05I5, first proof, zero-cokernel boundary; Algebra Tag 00DV.
(blueprint: lem-trf-small-support-cokernel-induction).

Proof: By exact localization, the vanishing closed-fibre localization is
`Q_q / m Q_q = 0`. Since `Q_q` is finite over the local ring `B_q` and `m B_q` is
contained in its maximal ideal, Nakayama gives `Q_q = 0`. Multiply annihilating
denominators for a finite generating list of `Q`; for an empty list take `g = 1`.
Then `Q_g = 0`. Localizing the original short exact sequence gives an isomorphism
from `B_g^r` to `N_g`. Smoothness makes `B_g` flat over `A`, so this finite free
module is `A`-flat and finitely presented over `B_g`. The affine associated-sheaf
criterion and the relative-flatness criterion give the sheaf conclusion. No
smaller-support hypothesis is used. Uses lem-weil-pbc-nakayama-jacobson,
lem-weil-pbc-localization-module-exact, lem-pc-smooth-flat,
lem-pc-affine-flat-module-localization-preserves-flatness,
lem-weil-pbc-quasi-coherent-finite-type-affine, def-pc-scheme-module-flat-over.
-/
theorem exists_smallSupport_cokernel_zero
    {A B N Q : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
    [AddCommGroup N] [AddCommGroup Q] [Module B N] [Module B Q]
    [Module A N] [IsScalarTower A B N] [Module.Finite B N] [Module.Finite B Q]
    (n r : ℕ)
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    (hgeom : ∀ (p : PrimeSpectrum A) (K : Type (max u v)) [Field K] [Algebra A K]
      (ι : p.asIdeal.ResidueField →+* K),
      algebraMap A K = ι.comp (algebraMap A p.asIdeal.ResidueField) → IsDomain (K ⊗[A] B))
    (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap (algebraMap A B) q = IsLocalRing.closedPoint A)
    (α : (Fin r → B) →ₗ[B] N) (β : N →ₗ[B] Q)
    (hinj : Function.Injective α) (hexact : Function.Exact α β)
    (hsurj : Function.Surjective β)
    (hui : ∀ (L : Type (max u v)) [AddCommGroup L] [Module A L],
      Function.Injective ((α.restrictScalars A).lTensor L))
    (hflat : @Module.Flat A (LocalizedModule q.asIdeal.primeCompl Q) _ _
      (Module.compHom _ (algebraMap A B)))
    (hzero : q ∉ Module.support B (smallSupportClosedFibre A B Q)) :
    ∃ g : B, g ∉ q.asIdeal ∧ Subsingleton (LocalizedModule.Away g Q) ∧
      smallSupportModuleGoodPrincipal (M := Q) (algebraMap A B) g ∧
      smallSupportGoodPrincipal (M := N) (algebraMap A B) g ∧
      Function.Injective (smallSupportAwayFreeMap α g) ∧
      Function.Exact (smallSupportAwayFreeMap α g) (smallSupportAwayMap β g) ∧
      Function.Surjective (smallSupportAwayMap β g) := by
  sorry

end AlgebraicGeometry
