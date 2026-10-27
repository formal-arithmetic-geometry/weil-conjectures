module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Grp
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Extension of relative rational group homomorphisms

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 5.1 Lemma 4 and the proof of
Proposition 3, printed pp.113--114; 2.5 Proposition 5.
(blueprint: lem-sfb-rational-group-hom-extension)

An open is represented by an open immersion in `Over S`. Its density in every fibre is
written using the inverse image of its range along `Scheme.Hom.fiberι`. The pullback of
`(j ⊗ₘ j) ≫ μ[G]` along `j` is precisely the open domain of `a(xy)` inside `U ×_S U`.
The compatibility below is equality of morphisms on a fibrewise dense open of that domain.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A rational homomorphism on a fibrewise dense open extends uniquely over any base scheme.

Source: BLR, Néron Models, 5.1 Lemma 4 and proof of Proposition 3, pp.113--114;
2.5 Proposition 5 (blueprint: lem-sfb-rational-group-hom-extension).

Proof: (1) Smooth maps are flat, locally finitely presented and universally open
(lem-pc-smooth-flat, lem-weil-pbc-flat-lfp-open); consequently inverse images of fibrewise
dense opens are fibrewise dense. Such opens in smooth schemes are schematically dense,
also after base change (lem-sfb-smooth-fibrewise-dense-open-base-change). Morphisms into a
separated target agreeing there are equal
(lemma-nagata-ext-scheme-theoretically-dominant-separated).
(2) Multiplication is smooth, using the automorphism (x,y) ↦ (xy,y), smooth base change
and composition (lem-pc-proper-base-change, lem-trf-smooth-composition). Its restriction
q : U ×_S U → G is smooth (lem-pc-open-immersion-smooth-composition,
lem-weil-pbc-smooth-restrict-open-subschemes) and surjective: on each geometric fibre,
the dense opens U and U⁻¹g intersect, giving g = xy with x,y in U.
(3) Put b(x,y) = a(x)a(y). The hypothesis and schematic density give b = a q on q⁻¹(U).
(4) On the actual kernel pair of q, the two pullbacks of b agree over the dense open
lying over U, and hence everywhere by (1).
(5) The smooth surjection q is an fpqc covering: over any affine open, finitely many
affine opens of the source have images covering it, by universal openness and
quasi-compactness (lem-weil-pbc-affine-scheme-qcqs, def-weil-pbc-fpqc-covering).
Representable fpqc descent gives a unique map A with A q = b
(lem-weil-pbc-fpqc-representable-descent). Descent uniqueness with target S makes A an S-map.
(6) The base change q⁻¹(U) → U is also a smooth surjection, so descent gives A|U = a
on all of U. (7) Multiplicativity holds on the dense multiplication domain and hence
on G ×_S G by (1). On test schemes, multiplicativity implies preservation of identity
and inverses. Density of U gives uniqueness. -/
theorem existsUnique_groupHom_extension_of_fibrewiseDense_open
    {S : Scheme.{u}} (G H : Over S) [GrpObj G] [GrpObj H]
    [Smooth G.hom] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth H.hom] [IsSeparated H.hom] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    (U : Over S) (j : U ⟶ G) [IsOpenImmersion j.left]
    (hU : ∀ s : S, Dense ((G.hom.fiberι s) ⁻¹' Set.range j.left)) (a : U ⟶ H)
    (hcompat : ∃ (W : Over S) (k : W ⟶ pullback ((j ⊗ₘ j) ≫ μ[G]) j),
      IsOpenImmersion k.left ∧
      (∀ s : S, Dense (((pullback ((j ⊗ₘ j) ≫ μ[G]) j).hom.fiberι s) ⁻¹'
        Set.range k.left)) ∧
      k ≫ pullback.fst ((j ⊗ₘ j) ≫ μ[G]) j ≫ (a ⊗ₘ a) ≫ μ[H] =
        k ≫ pullback.snd ((j ⊗ₘ j) ≫ μ[G]) j ≫ a) :
    ∃! f : G ⟶ H, IsMonHom f ∧ j ≫ f = a := by
  sorry

/-- A birational map compatible with multiplication extends uniquely to a group isomorphism.

Source: BLR, Néron Models, proof of 5.1 Proposition 3, pp.113--114
(blueprint: lem-sfb-rational-group-hom-extension).

Proof: Apply the extension construction of steps (1)--(7) above to `α.hom ≫ jV`,
obtaining A : G → H. (8) The dense multiplication domain in U ×_S U has fibrewise dense
image in V ×_S V under α × α. On that image the inverse α⁻¹ preserves multiplication:
if v = α(x), w = α(y), then vw = α(xy), so α⁻¹(vw) = xy. The image is contained in,
and is fibrewise dense in, the multiplication domain of α⁻¹. Apply the same extension
theorem to obtain B : H → G. The composites BA and AB are the identities on U and V,
respectively, so schematic density and separatedness make them the identities everywhere
(lem-sfb-smooth-fibrewise-dense-open-base-change,
lemma-nagata-ext-scheme-theoretically-dominant-separated). Thus A is an isomorphism.
The same density argument gives uniqueness, including equality of inverse morphisms. -/
theorem existsUnique_groupIso_extension_of_fibrewiseDense_open
    {S : Scheme.{u}} (G H : Over S) [GrpObj G] [GrpObj H]
    [Smooth G.hom] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth H.hom] [IsSeparated H.hom] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    (U V : Over S) (j : U ⟶ G) (jV : V ⟶ H)
    [IsOpenImmersion j.left] [IsOpenImmersion jV.left]
    (hU : ∀ s : S, Dense ((G.hom.fiberι s) ⁻¹' Set.range j.left))
    (hV : ∀ s : S, Dense ((H.hom.fiberι s) ⁻¹' Set.range jV.left)) (α : U ≅ V)
    (hcompat : ∃ (W : Over S) (k : W ⟶ pullback ((j ⊗ₘ j) ≫ μ[G]) j),
      IsOpenImmersion k.left ∧
      (∀ s : S, Dense (((pullback ((j ⊗ₘ j) ≫ μ[G]) j).hom.fiberι s) ⁻¹'
        Set.range k.left)) ∧
      k ≫ pullback.fst ((j ⊗ₘ j) ≫ μ[G]) j ≫
          ((α.hom ≫ jV) ⊗ₘ (α.hom ≫ jV)) ≫ μ[H] =
        k ≫ pullback.snd ((j ⊗ₘ j) ≫ μ[G]) j ≫ α.hom ≫ jV) :
    ∃! f : G ≅ H, IsMonHom f.hom ∧ j ≫ f.hom = α.hom ≫ jV := by
  sorry

end AlgebraicGeometry
