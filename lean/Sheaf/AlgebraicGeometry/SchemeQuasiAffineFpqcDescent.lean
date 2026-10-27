module

public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.QuasiAffineBaseChange
import WeilConjectures.AlgebraicGeometry.FpqcDescendQuasiCompact
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Quasi-affine scheme morphisms descend along fpqc coverings

Source: Stacks Project, Descent, Tag 02L7, lemma-descending-property-quasi-affine,
descent implication (blueprint: lem-sfb-scheme-quasi-affine-fpqc-descent).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Quasi-affineness descends along an arbitrary fpqc covering family of the target.
Source: Stacks Project, Descent, Tag 02L7, lemma-descending-property-quasi-affine.
(blueprint: lem-sfb-scheme-quasi-affine-fpqc-descent)

Proof:
1. Fix an affine open `V` of `U` and set `X = Y ×_U V`. Base change the covering
   to `V`. The fpqc covering axioms and the definition of a quasi-compact covering
   give finitely many affine opens `B_j` in its members whose images cover `V`.
   Their disjoint union `B` is affine, and `g : B ⟶ V` is flat and surjective.
   A morphism between affine schemes is affine, hence quasi-compact. If there are
   no components, `V` and `X` are empty and `X` is already quasi-affine.
2. Put `W = X ×_V B`. Quasi-affine base change makes each `X ×_V B_j` quasi-affine.
   Its canonical affine embedding is an open immersion and its source is
   quasi-compact. The coproduct universal property identifies `W` with the finite
   disjoint union of these schemes. Their canonical embeddings embed `W` openly
   into a finite disjoint union of affine schemes, which is affine. Thus `W` is
   quasi-affine, hence separated and quasi-compact. Separated cancellation and
   qcqs morphism permanence make `W ⟶ B` separated and quasi-compact.
3. Fpqc descent of quasi-compactness and separatedness along `g` makes `X ⟶ V`
   quasi-compact and separated. A separated morphism is quasi-separated. Since
   `V` is affine, qcqs morphism permanence makes `X` a qcqs scheme.
4. Set `R = Γ(V, O)`, `R' = Γ(B, O)`, `C = Γ(X, O)` and `D = Spec C`.
   The identity on `C` gives the canonical `V`-morphism `j : X ⟶ D` by the
   morphism-into-affine bijection. Flat base change identifies
   `C ⊗_R R'` with `Γ(W, O)` by `c ⊗ b ↦ c|_W * b|_W`. The affine fibre-product
   identification then identifies the pullback `j_B` with the canonical map
   `W ⟶ Spec Γ(W, O)`: the section maps agree on both tensor factors.
   The canonical affine-embedding lemma makes `j_B` an open immersion.
5. The map `D ×_V B ⟶ D` is flat and surjective by base change and has affine
   source and target. Affine open-immersion descent makes `j` an open immersion.
   By step 3, `X` is quasi-compact, so `j` exhibits it as a quasi-compact open
   subscheme of the affine scheme `D`. This holds for every affine open `V` of
   `U`, which is the definition of `IsQuasiAffineHom f`.

No separation, Noetherian, finite-type or finite-presentation hypothesis is imposed.
-/
theorem isQuasiAffineHom_of_fpqc_cover {Y U : Scheme.{u}} (f : Y ⟶ U)
    {I : Type v} (Uᵢ : I → Scheme.{u}) (p : ∀ i : I, Uᵢ i ⟶ U)
    (hp : Presieve.ofArrows Uᵢ p ∈ Scheme.fpqcPrecoverage U)
    (h : ∀ i : I, IsQuasiAffineHom (pullback.snd f (p i))) : IsQuasiAffineHom f := by
  sorry

end AlgebraicGeometry
