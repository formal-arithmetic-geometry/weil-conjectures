module

public import Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction

/-! # Graded algebra isomorphisms on a base open

Source: Stacks Project, Constructions, Tags 01MY and 02NC, the local algebra
isomorphisms used to glue relative Proj (blueprint: def-trf-local-graded-algebra-iso).
The affine-basis presentation records the actual section maps in both directions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.RelativeProjAlgebra

/-- An isomorphism of the restricted graded algebra sheaves on U, specified on every
contained affine open. Both maps preserve the grading, base scalars and restriction;
their composites are identities. Affine opens form a basis, so these are precisely
isomorphisms of the restricted sheaves, including their algebra and grading structures.
Source: Stacks, Constructions, Tags 01MY and 02NC
(blueprint: def-trf-local-graded-algebra-iso). -/
structure LocalGradedIso {S : Scheme.{u}} (A B : RelativeProjAlgebra S)
    (U : S.affineOpens) where
  hom : ∀ (V : S.affineOpens), V ≤ U → A.sectionGrade V →+*ᵍ B.sectionGrade V
  inv : ∀ (V : S.affineOpens), V ≤ U → B.sectionGrade V →+*ᵍ A.sectionGrade V
  hom_inv : ∀ (V : S.affineOpens) (h : V ≤ U) (a : A.sections V),
    inv V h (hom V h a) = a
  inv_hom : ∀ (V : S.affineOpens) (h : V ≤ U) (b : B.sections V),
    hom V h (inv V h b) = b
  hom_base : ∀ (V : S.affineOpens) (h : V ≤ U) (r : Γ(S, V.1)),
    hom V h (algebraMap Γ(S, V.1) (A.sections V) r) =
      algebraMap Γ(S, V.1) (B.sections V) r
  inv_base : ∀ (V : S.affineOpens) (h : V ≤ U) (r : Γ(S, V.1)),
    inv V h (algebraMap Γ(S, V.1) (B.sections V) r) =
      algebraMap Γ(S, V.1) (A.sections V) r
  hom_naturality : ∀ (V W : S.affineOpens) (h : W ≤ V) (hV : V ≤ U)
    (a : A.sections V),
    B.restriction h (hom V hV a) = hom W (h.trans hV) (A.restriction h a)
  inv_naturality : ∀ (V W : S.affineOpens) (h : W ≤ V) (hV : V ≤ U)
    (b : B.sections V),
    A.restriction h (inv V hV b) = inv W (h.trans hV) (B.restriction h b)

namespace LocalGradedIso

variable {S : Scheme.{u}} {A B : RelativeProjAlgebra S} {U : S.affineOpens}

/-- The inverse local graded sheaf-algebra isomorphism, by exchanging its two maps.
Source: Stacks, Constructions, Tag 01MY
(blueprint: def-trf-local-graded-algebra-iso). -/
def symm (β : LocalGradedIso A B U) : LocalGradedIso B A U where
  hom := β.inv
  inv := β.hom
  hom_inv := β.inv_hom
  inv_hom := β.hom_inv
  hom_base := β.inv_base
  inv_base := β.hom_base
  hom_naturality := β.inv_naturality
  inv_naturality := β.hom_naturality

/-- Restriction of a local isomorphism to a contained affine base open.
Source: Stacks, Constructions, Tags 01MY and 02NC
(blueprint: def-trf-local-graded-algebra-iso). -/
def restrict (β : LocalGradedIso A B U) (V : S.affineOpens) (h : V ≤ U) :
    LocalGradedIso A B V where
  hom W hW := β.hom W (hW.trans h)
  inv W hW := β.inv W (hW.trans h)
  hom_inv W hW := β.hom_inv W (hW.trans h)
  inv_hom W hW := β.inv_hom W (hW.trans h)
  hom_base W hW := β.hom_base W (hW.trans h)
  inv_base W hW := β.inv_base W (hW.trans h)
  hom_naturality W T hTW hW := β.hom_naturality W T hTW (hW.trans h)
  inv_naturality W T hTW hW := β.inv_naturality W T hTW (hW.trans h)

end LocalGradedIso
end AlgebraicGeometry.RelativeProjAlgebra
