/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.QuasiIso
import Sheaf.RingTheory.WeaklyEtaleTorBoundedResolution
import Sheaf.Algebra.Homology.FlatResolutionTorComparison
import WeilConjectures.Algebra.Homology.DoubleComplexCokernelHomologyIso
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import Sheaf.RingTheory.IndEtaleUniverseTransport

/-! # Tor and flat resolution bounds for weakly etale algebras

Source: blueprint, proper base change, Flat diagonal and Tor groups
(blueprint: lem-weil-pbc-weak-etale-tor).

Mathlib's monoidal module category requires the ring and carrier universes to coincide.
Both coefficient rings are therefore canonically lifted to `max u v`; this admits
arbitrary module sizes without equating the original ring and module universes.
Restriction along `ULift.ringEquiv` identifies these with the original coefficient modules.

The two-factor action is specified by its values on pure tensors, using the actual
functorial maps on Tor. It is part of the conclusion, not an assumed coefficient action.
The isomorphisms are natural in both modules; naturality is stated on pure tensors,
which generate the diagonal tensor product.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ModuleCat

noncomputable section

/-- The functorial map on Tor in both arguments. Source: Stacks, Tag 00LY;
blueprint proof step 3 (blueprint: lem-weil-pbc-weak-etale-tor). -/
def torBothMap {R : Type u} [CommRing R] (i : ℕ)
    {M M' N N' : ModuleCat.{u} R} (f : M ⟶ M') (g : N ⟶ N') :
    (((Tor' (ModuleCat.{u} R) i).obj M).obj N) ⟶
      (((Tor' (ModuleCat.{u} R) i).obj M').obj N') :=
  ((Tor' (ModuleCat.{u} R) i).map f).app N ≫
    ((Tor' (ModuleCat.{u} R) i).obj M').map g

/-- Tor over the base ring of two algebra modules, with restriction along the given
algebra map. Source: blueprint proof step 3 (blueprint: lem-weil-pbc-weak-etale-tor). -/
def torOverBase (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (i : ℕ)
    (M N : ModuleCat.{u} B) : ModuleCat.{u} A :=
  ((Tor' (ModuleCat.{u} A) i).obj
    ((restrictScalars (algebraMap A B)).obj M)).obj
      ((restrictScalars (algebraMap A B)).obj N)

/-- Package the two-factor Tor action as a module over the diagonal ring. The action
will be characterized in the theorem, rather than supplied as a hypothesis.
Source: blueprint proof step 3 (blueprint: lem-weil-pbc-weak-etale-tor). -/
def torDiagonalModule (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (i : ℕ)
    (M N : ModuleCat.{u} B)
    (action : Module (B ⊗[A] B) (torOverBase A B i M N)) :
    ModuleCat.{u} (B ⊗[A] B) :=
  @ModuleCat.of (B ⊗[A] B) _ (torOverBase A B i M N) _ action

/-- Tensor along multiplication, not along either inclusion of the tensor factors.
Source: blueprint proof steps 4--5 (blueprint: lem-weil-pbc-weak-etale-tor). -/
def torDiagonalTensor (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (i : ℕ)
    (M N : ModuleCat.{u} B)
    (action : Module (B ⊗[A] B) (torOverBase A B i M N)) : ModuleCat.{u} B :=
  (extendScalars (Algebra.TensorProduct.lmul' A (S := B)).toRingHom).obj
    (torDiagonalModule A B i M N action)

/-- A pure tensor in the diagonal extension, using multiplication for the action on `B`.
Source: blueprint proof step 5 (blueprint: lem-weil-pbc-weak-etale-tor). -/
def torDiagonalTmul (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (i : ℕ)
    (M N : ModuleCat.{u} B)
    (action : Module (B ⊗[A] B) (torOverBase A B i M N))
    (b : B) (t : torOverBase A B i M N) : torDiagonalTensor A B i M N action :=
  @TensorProduct.tmul (B ⊗[A] B) _ B (torOverBase A B i M N) _ _
    (Module.compHom B (Algebra.TensorProduct.lmul' A (S := B)).toRingHom) action b t

/-- The natural diagonal Tor comparison, with its two-factor coefficient action fixed
by the maps of the existing Tor bifunctor. Source: blueprint proof steps 3--5
(blueprint: lem-weil-pbc-weak-etale-tor). -/
def DiagonalTorComparison (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (i : ℕ) : Prop :=
    ∃ action : ∀ M N : ModuleCat.{u} B,
        Module (B ⊗[A] B) (torOverBase A B i M N),
      (∀ (M N : ModuleCat.{u} B) (b₁ b₂ : B) (t : torOverBase A B i M N),
        @SMul.smul _ _ (action M N).toSMul (b₁ ⊗ₜ[A] b₂) t =
          torBothMap i
            ((restrictScalars (algebraMap A B)).map
              (ofHom ((LinearMap.lsmul B M) b₁)))
            ((restrictScalars (algebraMap A B)).map
              (ofHom ((LinearMap.lsmul B N) b₂))) t) ∧
      ∃ e : ∀ M N : ModuleCat.{u} B,
          torDiagonalTensor A B i M N (action M N) ≅
            (((Tor' (ModuleCat.{u} B) i).obj M).obj N),
        ∀ (M M' N N' : ModuleCat.{u} B) (f : M ⟶ M') (g : N ⟶ N')
          (b : B) (t : torOverBase A B i M N),
          torBothMap i f g ((e M N).hom (torDiagonalTmul A B i M N (action M N) b t)) =
            (e M' N').hom (torDiagonalTmul A B i M' N' (action M' N') b
              (torBothMap i ((restrictScalars (algebraMap A B)).map f)
                ((restrictScalars (algebraMap A B)).map g) t))

/-- For a weakly etale algebra, Tor over `B` is naturally the diagonal extension of Tor
over `A`. The coefficient action is the canonical one: `b₁ ⊗ b₂` acts by the functorial
maps induced by multiplication by `b₁` and `b₂` on the respective modules.
Source: blueprint, Flat diagonal and Tor groups (blueprint: lem-weil-pbc-weak-etale-tor).

Proof: Transport the coefficient rings along their canonical ULift ring equivalences.
(1) Construct a free `B`-resolution of the first module by successively taking
free modules on the underlying sets of the module and its kernels. (2) Its terms are
`A`-flat, since `B` is `A`-flat and direct sums preserve flatness. Tensor over `A` with
`N`; the two `B`-actions give the diagonal-ring action. (3) Compare this flat resolution
with a free `A`-resolution using the double-complex cokernel homology comparison,
Tor symmetry and resolution lifts. This identifies its homology with Tor over `A`,
intertwining both scalar actions and maps in both arguments. (4) Flatness of `B` over
the diagonal ring makes tensoring commute with cycles, boundaries and homology.
(5) The balanced maps `b ⊗ (p ⊗ n) ↦ bp ⊗ n` and `p ⊗ n ↦ 1 ⊗ (p ⊗ n)` are inverse
chain maps to the tensor complex over `B`. Its homology computes Tor over `B`.
All comparisons commute with resolution lifts, proving the displayed naturality. -/
theorem exists_weaklyEtale_tor_iso
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.WeaklyEtale A B]
    (i : ℕ) :
    @DiagonalTorComparison (ULift.{v} A) (ULift.{v} B) _ _ (ULift.algebra' A (ULift.{v} B)) i := by
  sorry

/-- A common bound for flat resolutions over `A` remains a common bound over a weakly
etale `A`-algebra `B`. Length at most `d` means flat terms and zero terms above `d`.
Source: blueprint, Flat diagonal and Tor groups; Stacks, Tag 066F
(blueprint: lem-weil-pbc-weak-etale-tor).

Proof: Transport along the canonical ULift ring equivalences.
(6) A flat resolution of length at most `d` computes Tor by
`lem-pc-flat-resolution-tor-comparison`, so Tor over `A` vanishes above `d`.
The diagonal comparison gives the same vanishing over `B`. (7) In a free `B`-resolution
of a module, its `d`-th syzygy has first Tor with `B/I` equal to degree `d+1` Tor of the
original module, for every ideal `I`. The flat Tor ideal criterion makes that syzygy
flat. Truncate there to obtain the required resolution. When `d = 0`, the syzygy is
the original module, which is flat and has its length-zero resolution. -/
theorem weaklyEtale_flatResolutionBound
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.WeaklyEtale A B]
    (d : ℕ)
    (hA : ∀ M : ModuleCat.{max u v} (ULift.{v} A),
      ∃ (F : ChainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℕ)
        (ε : F ⟶
          (ChainComplex.single₀ (ModuleCat.{max u v} (ULift.{v} A))).obj M),
        QuasiIso ε ∧ (∀ j : ℕ, Module.Flat (ULift.{v} A) (F.X j)) ∧
          (∀ j : ℕ, d < j → IsZero (F.X j))) :
    ∀ M : ModuleCat.{max u v} (ULift.{v} B),
      ∃ (F : ChainComplex (ModuleCat.{max u v} (ULift.{v} B)) ℕ)
        (ε : F ⟶
          (ChainComplex.single₀ (ModuleCat.{max u v} (ULift.{v} B))).obj M),
        QuasiIso ε ∧ (∀ j : ℕ, Module.Flat (ULift.{v} B) (F.X j)) ∧
          (∀ j : ℕ, d < j → IsZero (F.X j)) := by
  let : Algebra (ULift.{v} A) (ULift.{v} B) := ULift.algebra' A (ULift.{v} B)
  apply WeaklyEtaleTorAux.flatResolution_of_tor_vanishing (ULift.{v} B) d
  intro M N j hj
  obtain ⟨action, _, e, _⟩ := exists_weaklyEtale_tor_iso A B j
  obtain ⟨F, ε, hε, hflat, hzero⟩ := hA ((restrictScalars (algebraMap _ _)).obj M)
  let : QuasiIso ε := hε
  obtain ⟨c⟩ := flatResolution_torComparison
    ((restrictScalars (algebraMap _ _)).obj M) F ε hflat
    ((restrictScalars (algebraMap _ _)).obj N) j
  have hz : IsZero (torOverBase (ULift.{v} A) (ULift.{v} B) j M N) := by
    apply IsZero.of_iso _ c
    apply HomologicalComplex.ExactAt.isZero_homology
    apply HomologicalComplex.ExactAt.of_isZero
    change IsZero ((MonoidalCategory.tensorRight
      ((restrictScalars (algebraMap (ULift.{v} A) (ULift.{v} B))).obj N)).obj (F.X j))
    exact (MonoidalCategory.tensorRight
      ((restrictScalars (algebraMap (ULift.{v} A) (ULift.{v} B))).obj N)).map_isZero
        (hzero j hj)
  have hd : IsZero (torDiagonalModule (ULift.{v} A) (ULift.{v} B) j M N (action M N)) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton (torOverBase (ULift.{v} A) (ULift.{v} B) j M N)
    exact ModuleCat.subsingleton_of_isZero hz
  have ht : IsZero (torDiagonalTensor (ULift.{v} A) (ULift.{v} B) j M N (action M N)) :=
    (extendScalars (Algebra.TensorProduct.lmul' (ULift.{v} A)
      (S := ULift.{v} B)).toRingHom).map_isZero hd
  exact ht.of_iso (e M N).symm

end

end ModuleCat
