module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Properties
import Sheaf.FieldTheory.CommonExtensionFields
import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-!
# Base change of the reduced geometric-fibre locus

Source: Stacks Project, More on Morphisms, Tag 0576
(`lemma-base-change-fibres-geometrically-reduced`),
with the geometric-fibre formulation from Varieties, Tags 035X and 020I.
(blueprint: lem-trf-geometric-reduced-fibre-locus-base-change)

The proof compares the two fibres at a point after identifying them with scalar
extensions of the same scheme-theoretic fibre.  A common overfield of the two
chosen algebraic closures, perfectness of algebraic closures, affine tensor
product charts, and faithful-flat descent of nilpotents give both implications.
Empty fibres are included because reducedness is the local-ring condition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/--
The reduced geometric-fibre locus is preserved and reflected by arbitrary base change.
(blueprint: lem-trf-geometric-reduced-fibre-locus-base-change)

Source: Stacks Project, More on Morphisms, Tag 0576,
`lemma-base-change-fibres-geometrically-reduced`;
see Varieties, Tags 035X and 020I for the geometric-reducedness interpretation.

Proof plan: (1) identify the geometric fibre of the pullback at `t'` with the
scalar extension of the original scheme-theoretic fibre over `g t'`; (2) place the
chosen algebraic closures in a common overfield and use that fields are reduced and
algebraic closures are perfect; (3) test reducedness on affine charts, where the
charts are tensor products; (4) use reduced tensor products over a perfect field
and tensor cancellation in the forward direction; (5) use faithful flatness of a
field extension to reflect nilpotents; (6) repeat the argument backwards; and
(7) conclude the equality of subsets pointwise. No flatness, finite presentation,
or surjectivity hypothesis on either morphism is used, and empty fibres are allowed.
-/
theorem geometricReduced_fibre_locus_baseChange
    {X T T' : Scheme.{u}} (f : X ⟶ T) (g : T' ⟶ T) :
    {t' : T' |
      ∀ (Ω : Type u) [Field Ω] [Algebra (T'.residueField t') Ω]
        [IsAlgClosure (T'.residueField t') Ω],
        IsReduced (pullback (pullback.snd f g)
          (Spec.map (CommRingCat.ofHom (algebraMap (T'.residueField t') Ω)) ≫
            T'.fromSpecResidueField t'))} =
      g ⁻¹' {t : T |
        ∀ (Ω : Type u) [Field Ω] [Algebra (T.residueField t) Ω]
          [IsAlgClosure (T.residueField t) Ω],
          IsReduced (pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
              T.fromSpecResidueField t))} := by
  sorry

end AlgebraicGeometry
