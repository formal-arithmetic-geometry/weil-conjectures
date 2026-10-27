module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Sites.Spaces

/-! # Norm transition frames and tensor-power section gluing

Source: Stacks Project, Divisors, Tags 0BCY and 0BCZ, Section 0BCX;
Modules, Section 01CA (blueprint: lem-sfb-norm-frame-tensor-section-gluing).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The pure tensor power of a section on an arbitrary open, using the existing
`tensorPow` and `tmulSection`. At zero it is the section 1 of the structure sheaf;
at a successor it is the tensor of the original section with the preceding power.
This is the local-section version of `tensorPowSection` (whose input is a global
morphism from the unit), with the same parenthesization and degree-zero convention.
Source: Stacks Project, Modules, Section 01CA, iterated pure tensors
(blueprint: lem-sfb-norm-frame-tensor-section-gluing). -/
noncomputable def tensorPowLocalSection {X : Scheme.{u}} {M : X.Modules}
    {U : X.Opens} (e : Γ(M, U)) : (n : ℕ) → Γ(M.tensorPow n, U)
  | 0 => unitSectionsEquiv U 1
  | n + 1 => tmulSection e (tensorPowLocalSection e n)

/-- A restriction-compatible family of multiplicative, unital maps sends the transition
units of given local frames to a cocycle. This cocycle defines an invertible module
with frames, and the same module and frames glue norm coefficients in every positive
tensor power.

Source: Stacks Project, Divisors, Tags 0BCY and 0BCZ, local-frame constructions;
Section 0BCX. Only multiplicativity, preservation of 1 and restriction compatibility
are used: no degree, vanishing or finiteness hypothesis is needed here.
(blueprint: lem-sfb-norm-frame-tensor-section-gluing).

Proof plan:
1. The inverse frame isomorphism gives the unique overlap coefficient. Reversing
indices makes its inverse, so it is a unit. Uniqueness gives identity and cocycle laws.
2. Apply the multiplicative maps. They preserve units and their inverses; naturality
with restriction transports the triple-overlap identities to the target scheme.
3. Glue copies of the structure sheaf using these transition units by
`lem-weil-pbc-glue-sheaves-of-modules` (2). The inverse local trivializations send 1
to frames with exactly the asserted transition orientation. On affine subopens these
are rank-one tilde modules (`lem-weil-pbc-spec-tilde-free-module`), hence quasi-coherent
(`pqf-def-coherent`) and invertible (`def-sc-invertible-module`).
4. Induct on the positive tensor exponent. Tensor products preserve invertibility
(`lem-weil-pbc-invertible-pullback-tensor`). The restriction comparison
(`lem-weil-pbc-module-restriction-tensor-comparison`) and the monoidal unitors
(`lem-weil-pbc-module-tensor-symmetric-monoidal`) show that pure tensor powers of
frames remain frames. Bilinearity (`def-pur-sheaf-tensor-product`) raises transition
coefficients to the same powers, on both schemes.
5. Express the restricted global section uniquely in these frames. On overlaps its
coefficients satisfy b_j = b_i u_ij^n. Multiplicativity implies preservation of positive
powers; restriction compatibility gives nu(b_j) = nu(b_i) v_ij^n. Thus the specified
local sections in the target tensor power agree on intersections.
6. The underlying sheaf of `def-weil-sheaf-of-modules-category` glues these local
sections uniquely by the Zariski sheaf axiom (`def-sc-zariski-site`), including the
empty-cover case. All exponents and sections use the same previously fixed module. -/
theorem norm_frame_tensor_section_gluing
    {Y Z : Scheme.{u}} (p : Y ⟶ Z)
    (ν : ∀ V : Z.Opens, Γ(Y, p ⁻¹ᵁ V) →* Γ(Z, V))
    (hν : ∀ (V W : Z.Opens) (h : W ≤ V) (a : Γ(Y, p ⁻¹ᵁ V)),
      ν W (Y.presheaf.map (homOfLE (p.preimage_mono h)).op a) =
        Z.presheaf.map (homOfLE h).op (ν V a))
    (M : Y.Modules) [M.IsInvertible]
    (I : Type w) (V : I → Z.Opens) (hcover : ⨆ i, V i = ⊤)
    (e : ∀ i : I, Γ(M, p ⁻¹ᵁ V i)) (he : ∀ i : I, IsFreeGenerator (e i)) :
    ∃ uij : ∀ i j : I, Γ(Y, p ⁻¹ᵁ (V i ⊓ V j))ˣ,
      (∀ i j : I,
        M.presheaf.map (homOfLE (p.preimage_mono inf_le_left)).op (e i) =
          (uij i j : Γ(Y, p ⁻¹ᵁ (V i ⊓ V j))) •
            M.presheaf.map (homOfLE (p.preimage_mono inf_le_right)).op (e j) ∧
        ∀ a : Γ(Y, p ⁻¹ᵁ (V i ⊓ V j))ˣ,
          M.presheaf.map (homOfLE (p.preimage_mono inf_le_left)).op (e i) =
            (a : Γ(Y, p ⁻¹ᵁ (V i ⊓ V j))) •
              M.presheaf.map (homOfLE (p.preimage_mono inf_le_right)).op (e j) →
          a = uij i j) ∧
      ∃ vij : ∀ i j : I, Γ(Z, V i ⊓ V j)ˣ,
        (∀ i j : I, vij i j = Units.map (ν (V i ⊓ V j)) (uij i j)) ∧
        (∀ i : I, vij i i = 1) ∧
        (∀ (i j : I) (W : Z.Opens) (hi : W ≤ V i) (hj : W ≤ V j),
          Units.map (Z.presheaf.map (homOfLE (le_inf hj hi)).op).hom.toMonoidHom
              (vij j i) =
            (Units.map (Z.presheaf.map (homOfLE (le_inf hi hj)).op).hom.toMonoidHom
              (vij i j))⁻¹) ∧
        (∀ (i j k : I) (W : Z.Opens)
            (hi : W ≤ V i) (hj : W ≤ V j) (hk : W ≤ V k),
          Units.map (Z.presheaf.map (homOfLE (le_inf hi hk)).op).hom.toMonoidHom
              (vij i k) =
            Units.map (Z.presheaf.map (homOfLE (le_inf hi hj)).op).hom.toMonoidHom
                (vij i j) *
              Units.map (Z.presheaf.map (homOfLE (le_inf hj hk)).op).hom.toMonoidHom
                (vij j k)) ∧
        ∃ N : Z.Modules, N.IsInvertible ∧
          ∃ f : ∀ i : I, Γ(N, V i),
            (∀ i : I, IsFreeGenerator (f i)) ∧
            (∀ i j : I,
              N.presheaf.map (homOfLE inf_le_left).op (f i) =
                (vij i j : Γ(Z, V i ⊓ V j)) •
                  N.presheaf.map (homOfLE inf_le_right).op (f j)) ∧
            ∀ (n : ℕ), 1 ≤ n →
              (M.tensorPow n).IsInvertible ∧ (N.tensorPow n).IsInvertible ∧
              (∀ i : I, IsFreeGenerator (tensorPowLocalSection (e i) n)) ∧
              (∀ i : I, IsFreeGenerator (tensorPowLocalSection (f i) n)) ∧
              (∀ i j : I,
                (M.tensorPow n).presheaf.map
                    (homOfLE (p.preimage_mono inf_le_left)).op
                    (tensorPowLocalSection (e i) n) =
                  (uij i j : Γ(Y, p ⁻¹ᵁ (V i ⊓ V j))) ^ n •
                    (M.tensorPow n).presheaf.map
                      (homOfLE (p.preimage_mono inf_le_right)).op
                      (tensorPowLocalSection (e j) n)) ∧
              (∀ i j : I,
                (N.tensorPow n).presheaf.map (homOfLE inf_le_left).op
                    (tensorPowLocalSection (f i) n) =
                  (vij i j : Γ(Z, V i ⊓ V j)) ^ n •
                    (N.tensorPow n).presheaf.map (homOfLE inf_le_right).op
                      (tensorPowLocalSection (f j) n)) ∧
              ∀ s : Γ(M.tensorPow n, ⊤),
                ∃ b : ∀ i : I, Γ(Y, p ⁻¹ᵁ V i),
                  (∀ i : I,
                    (M.tensorPow n).presheaf.map (homOfLE le_top).op s =
                      b i • tensorPowLocalSection (e i) n ∧
                    ∀ a : Γ(Y, p ⁻¹ᵁ V i),
                      (M.tensorPow n).presheaf.map (homOfLE le_top).op s =
                        a • tensorPowLocalSection (e i) n → a = b i) ∧
                  ∃! t : Γ(N.tensorPow n, ⊤), ∀ i : I,
                    (N.tensorPow n).presheaf.map (homOfLE le_top).op t =
                      ν (V i) (b i) • tensorPowLocalSection (f i) n := by
  sorry

end AlgebraicGeometry.Scheme.Modules
