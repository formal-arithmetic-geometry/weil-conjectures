module

public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.KrullDimension

/-!
# Topological dimension of an algebraic space from an étale atlas

Source: Stacks Project, decent-spaces.tex, Tag 0A4J; spaces-properties.tex,
Tags 0A4H, 0BAN (blueprint: lem-sfb-space-etale-atlas-topological-dimension).

The topological Krull dimension of a quasi-separated algebraic space is computed by
any representable surjective étale scheme atlas, after arbitrary scheme base change.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Topological dimension is unchanged on a representable surjective étale atlas after
arbitrary base change of a quasi-separated algebraic space. The atlas scheme `U`
is independent of the base-change scheme `T`.
Source: Stacks Project, decent-spaces.tex, Tag 0A4J, lemma-dimension-decent-space (2),
and spaces-properties.tex, Tags 0A4H and 0BAN (blueprint:
lem-sfb-space-etale-atlas-topological-dimension).
Proof: form the sheaf fibre product with the representable scheme `T` and regard it as
an algebraic space.  The diagonal remains quasi-compact by base change.  The local-ring
formula for a quasi-separated algebraic space and the scheme local-ring dimension
formula identify both dimensions with suprema of local dimensions.  Étaleness identifies
local dimensions in the atlas and surjectivity identifies the indexing point sets, so the
suprema agree, including the empty and infinite-dimensional cases. -/
theorem space_etale_atlas_topological_dimension {B : Scheme.{u}}
    (X : AlgebraicSpace B)
    (f : X ⟶ schemeSpace (Over.mk (𝟙 B)))
    (hqs : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
      (Limits.pullback.diagonal f.hom.hom))
    (T : Over B)
    (U : Over B)
    (a : yoneda.obj U ⟶
      (enlargedFibreProduct f
        (ObjectProperty.homMk ⟨yoneda.map (Over.homMk T.hom rfl)⟩ :
          schemeSpace T ⟶ schemeSpace (Over.mk (𝟙 B)))).obj.obj)
    (hae : IsEtale a)
    (has : IsSurjective a) :
    topologicalKrullDim
        (Point (enlargedFibreProduct f
          (ObjectProperty.homMk ⟨yoneda.map (Over.homMk T.hom rfl)⟩ :
          schemeSpace T ⟶ schemeSpace (Over.mk (𝟙 B)))).obj.obj) =
      topologicalKrullDim U.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
