/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.AssociatedCharacterLineBundle
public import WeilConjectures.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.FpqcTensorSections
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace

/-! # Sections of homogeneous character line bundles

Source: Milne, Algebraic Groups (2017), Section 18c, pp.389--390,
Definition 22.21, p.468, and proof of Theorem 22.48, p.479.
(blueprint: lem-sfb-homogeneous-line-bundle-sections)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The associated quotient is a homogeneous line bundle with invertible coherent
section sheaf, and pullback in the specified trivialization identifies its global
sections F-linearly with the actual regular semi-invariants for the inverse character.
The final identity is the section-action formula (sf)(g) = f(s⁻¹g), on every test
scheme, using the geometric left action on the total space. Thus it includes
algebraic equivariance, rather than equivariance only on rational points.

Source: Milne, Section 18c, pp.389--390, Definition 22.21, p.468, and proof of
Theorem 22.48, p.479.
(blueprint: lem-sfb-homogeneous-line-bundle-sections)

Proof:
1. The Borel-pair theorem gives the faithfully flat torsor π. Since G is affine
   of finite type over F it is Noetherian (lem-wf-affine-noetherian-components).
   Every open in G is quasi-compact (lem-sfb-noetherian-space-compact-subsets),
   so π is fpqc; this remains true after base change
   (lem-galois-fpqc-covering-base-change).
2. The pointwise inverse of χ is a character, since G_m is commutative.
   On G ×_Q G, identified with G × B by the specified torsor, descend O_G with
   transition z ↦ χ(b)⁻¹z. Multiplicativity of χ gives the cocycle and identity
   conditions. Apply lem-pc-fpqc-descent, including its rank-one clause, to get
   the Zariski-invertible section sheaf with the specified trivialization.
3. Glue the trivial affine-line bundles in Zariski frames using their unit
   transition functions (lem-weil-pbc-glue-schemes). The section functor of the
   resulting total space is represented by L, naturally under base change.
   Its pullback to G is G × A¹, with exactly the displayed B-orbit relation.
   Lemma lem-weil-pbc-fpqc-representable-descent identifies this with the fpqc
   quotient. The sheaf is coherent by lem-trf-proper-field-invertible-coherent.
4. Descend left multiplication (s,g,z) ↦ (sg,z), which commutes with the right
   B-action, by representable descent. The same argument supplies the base
   action. Their group laws and fibrewise linearity follow after the fpqc cover,
   where the coordinate z is unchanged.
5. Pull a section back and take its coordinate f. Compatibility on G ×_Q G is
   exactly f(gb) = χ(b)⁻¹ f(g), tested on all commutative F-algebras. Conversely
   those equations descend a unique section by
   lem-sc-etale-qcoherent-descent-fpqc-sections. The two constructions preserve
   addition and F-scalars, and descent uniqueness proves they are inverse.
6. A transformed section at g is s times the original section at s⁻¹g.
   The total-space action sends [s⁻¹g,f(s⁻¹g)] to [g,f(s⁻¹g)]. This gives the
   final identity on every test scheme. Equivalently, write E as the kernel
   of the regular-function difference map; tensoring with an F-algebra is exact,
   so the same comparison holds after base change, including the universal s.
   This proves the claimed algebraic equivariance. -/
theorem exists_homogeneousLineBundle_sections
    {F : Type u} [Field F] [IsAlgClosed F]
    (G : Grp (Over (Spec (.of F)))) (hG : ReductiveTorusCentralizer.IsReductive G)
    (T B : Grp (Over (Spec (.of F)))) (iT : T ⟶ G) (iB : B ⟶ G)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hTs : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (hB : IsBorelGroupScheme iB.hom.hom) (j : T ⟶ B) (hj : j ≫ iB = iT)
    (Q : Over (Spec (.of F))) (π : G.X ⟶ Q)
    (hQ : IsProper Q.hom) (hQft : LocallyOfFiniteType Q.hom) (hQqc : QuasiCompact Q.hom)
    (hπf : Flat π.left) (hπs : Surjective π.left)
    (hπi : (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) ≫ π = fst G.X B.X ≫ π)
    (hπt : IsPullback (fst G.X B.X)
      (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) π π)
    (χ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) :
    ∃ ψ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
      ψ.hom.hom = χ.hom.hom⁻¹ ∧
      ∃ P : AssociatedCharacterLineBundle.Presentation G B iB Q π χ,
      P.L.IsInvertible ∧ Scheme.Modules.isCoherent Q.left P.L ∧
      ∃ e : AssociatedCharacterLineBundle.sections Q P.L ≃ₗ[F]
        RhoSection.sectionModule G B iB ψ 1,
        (∀ σ : AssociatedCharacterLineBundle.sections Q P.L,
          (e σ).val = AssociatedCharacterLineBundle.pullbackCoordinate π P.L P.trivialization σ) ∧
        ∀ (S : Over (Spec (.of F))) (s g : S ⟶ G.X)
          (σ : AssociatedCharacterLineBundle.sections Q P.L),
          lift s ((P.sectionRepresentation S ((s⁻¹ * g) ≫ π)
            (AssociatedCharacterLineBundle.pullTopSection ((s⁻¹ * g) ≫ π).left P.L σ)).val) ≫
              P.totalAction.smul =
            lift g (AssociatedCharacterLineBundle.linePoint S
              (((algΓ (.of F)).map (s⁻¹ * g)).unop.hom (e σ).val)) ≫ P.quotientMap := by
  sorry

end AlgebraicGeometry
